import OCaml.Bytecode.Semantics
import OCaml.Vm.Layout
import OCaml.Vm.PrimitiveEntries
import Vsa.Machine
import Vsa.Sim.RamReadBytes
import Vsa.Sim.BlockPilot

/-!
# The VM-state representation predicate (skeleton)

How a `BcSem` state `s : St` sits in a machine configuration `c : Config`
of the bare-metal `ocamlrun` when `caml_interprete` is at its dispatch loop
head (`Layout.loopHead`). Everything here is a definition; the Layer A
simulation obligations (`OCaml/Refinement.lean`) are stated with it.

The central design choice (README §GC strategy) is the **placement**
`Place`: abstract block locations are mapped to addresses by `φ`, and `φ`
is an existential of `VmRepr`, not a fixed function. A minor collection or
a compaction moves blocks: across it, the simulation proof exhibits a NEW
placement `φ'` for the same abstract state (the collector preserves the
abstract heap up to the renaming `φ' ∘ φ⁻¹` on reachable blocks). Blocks
unreachable from the roots (registers, stack, globals, named values,
channels) need not be placed at all: `HeapRepr` constrains only the
blocks reachable from the roots (`Live`).

Word conventions follow `runtime/caml/mlvalues.h`: a value pointer points
at field 0, the header is the word before it (`wosize << 10 | color << 8 |
tag`); `Atom(t)` is `&caml_atom_table[t] + 1 word`; code pointers are
`caml_start_code + 4 pc` (no threaded code: `-DSHRINKED_GNUC`, so code
words are opcodes, not label addresses).
-/

namespace OCaml.Vm

open OCaml.Bytecode Vsa.Machine

/-- The 64-bit little-endian word at `a` (absent bytes read as 0, as the
Sail model reads them). -/
def word (c : Config) (a : Nat) : BitVec 64 := Vsa.Sim.bytesT c.σ.mem a 8

/-- The byte at `a`. -/
def byte (c : Config) (a : Nat) : BitVec 8 := Vsa.Sim.bytesT c.σ.mem a 1

/-- The 32-bit word at `a`. -/
def word32 (c : Config) (a : Nat) : BitVec 32 := Vsa.Sim.bytesT c.σ.mem a 4

/-- A general-purpose register. -/
def gpr (c : Config) (n : Nat) : Option (BitVec 64) := Vsa.Sim.gprGet c.σ n

/-- The program counter. -/
def pcOf (c : Config) : Option (BitVec 64) :=
  c.σ.regs.get? LeanRV64DExecutable.Register.PC

/-- The function pointer selected by a bytecode primitive index. Both data
addresses come from the ELF-derived layout; entries are ordinary code pointers. -/
def primitiveTarget (c : Config) (index : Nat) : BitVec 64 :=
  word c ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * index)

/-- The bytecode's primitive names must agree with the runtime's function
pointer table. This metadata contains no abstract heap locations. -/
structure PrimitiveBindings (P : Prog) (c : Config) : Prop where
  targets : ∀ i name, P.prims[i]? = some name →
    ∃ entry, PrimitiveEntries.lookup name = some entry ∧ primitiveTarget c i = BitVec.ofNat 64 entry

/-- Select a represented call target using its checked ELF entry. -/
theorem PrimitiveBindings.get {P : Prog} {c : Config} (h : PrimitiveBindings P c)
    {i : Nat} {name : String} {entry : Nat} (hp : P.prims[i]? = some name)
    (he : PrimitiveEntries.lookup name = some entry) :
    primitiveTarget c i = BitVec.ofNat 64 entry := by
  obtain ⟨entry', he', target⟩ := h.targets i name hp
  rw [he] at he'
  cases he'
  exact target

/-- Binding metadata depends only on total word reads, including the dynamic
pointer-table address. This also supports zero-equivalent boot memories. -/
theorem PrimitiveBindings.of_words {P : Prog} {c c' : Config} (h : PrimitiveBindings P c)
    (hw : ∀ a, word c' a = word c a) : PrimitiveBindings P c' := by
  refine ⟨?_⟩
  intro i name hp
  obtain ⟨entry, he, target⟩ := h.targets i name hp
  exact ⟨entry, he, by simpa only [primitiveTarget, hw] using target⟩

/-- Read-only machine summaries preserve every primitive binding together. -/
theorem PrimitiveBindings.frame {P : Prog} {c c' : Config} (h : PrimitiveBindings P c)
    (hm : c'.σ.mem = c.σ.mem) : PrimitiveBindings P c' :=
  h.of_words fun _ => by simp only [word, hm]

/-- Where the abstract heap lives at a given moment. -/
structure Place where
  /-- address of field 0 of block `l` (the value pointer) -/
  φ : Nat → Option Nat
  /-- `caml_start_code` -/
  codeBase : Nat
  /-- Address stored in caml_atom_table; the allocated static table does not move. -/
  atomBase : Nat

/-- The machine word of a value under a placement. -/
def valWord (pl : Place) : Val → Option (BitVec 64)
  | .int n => some (tag64 n)
  | .ptr l k => (pl.φ l).map fun a => BitVec.ofNat 64 (a + 8 * k)
  | .code pc => some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  | .atom t => some (BitVec.ofNat 64 (pl.atomBase + 8 * t + 8))
  | .raw w => some w

/-- A header word describes `wosize` and `tag` (the two color bits are the
major GC's business and unconstrained). -/
def HeaderOk (w : BitVec 64) (wosize tag : Nat) : Prop :=
  w.toNat % 256 = tag ∧ w.toNat / 1024 = wosize

/-- `struct channel` field offsets (`runtime/caml/io.h`, LP64). -/
def chanOffFd : Nat := 0
def chanOffCurr : Nat := 24
def chanOffBuff : Nat := 72

def chanOffOffset : Nat := 8
def chanOffMax : Nat := 32
def chanOffEnd : Nat := 16
def chanOffFlags : Nat := 68

/-- `CHANNEL_FLAG_UNBUFFERED` (`runtime/caml/io.h`). -/
def chanFlagUnbuffered : BitVec 32 := 16#32

/-- The active bytes and cursor of either kind of C channel. -/
def _root_.OCaml.Bytecode.Chan.buffer (ch : Chan) : List UInt8 :=
  if ch.fd = -1 then [] else if ch.isOut then ch.buf else ch.inBuf
def _root_.OCaml.Bytecode.Chan.cursor (ch : Chan) : Nat :=
  if ch.fd = -1 then ioBufferSize else if ch.isOut then ch.buf.length else ch.inPos

/-- Channel layout from runtime/caml/io.h, including read-ahead and offset. -/
def ChanAt (c : Config) (a : Nat) (ch : Chan) : Prop :=
  (word32 c (a + chanOffFd)).toInt = ch.fd ∧
  (word c (a + chanOffOffset)).toInt = ch.offset ∧
  (word c (a + chanOffCurr)).toNat = a + chanOffBuff + ch.cursor ∧
  (word c (a + chanOffMax)).toNat = (if ch.fd = -1 then a + chanOffBuff + ioBufferSize else if ch.isOut then 0 else a + chanOffBuff + ch.inBuf.length) ∧
  (word c (a + chanOffEnd)).toNat = a + chanOffBuff + ioBufferSize ∧
  word32 c (a + chanOffFlags) &&& chanFlagUnbuffered = 0#32 ∧
  ∀ i (b : UInt8), ch.buffer[i]? = some b → byte c (a + chanOffBuff + i) = BitVec.ofNat 8 b.toNat

/-- Where the `struct channel`s live (`caml_open_descriptor_in` mallocs
them). -/
abbrev ChanPlace := Nat → Option Nat

/-- Object `o` is laid out at value address `a`. -/
def ObjAt (c : Config) (pl : Place) (cp : ChanPlace) (a : Nat) (o : Obj) : Prop :=
  HeaderOk (word c (a - 8)) o.wosize o.tag ∧
  match o with
  | .block _ fs => ∀ i v, fs[i]? = some v → valWord pl v = some (word c (a + 8 * i))
  | .bytes b =>
      (∀ i (x : UInt8), b[i]? = some x → byte c (a + i) = BitVec.ofNat 8 x.toNat) ∧
      -- `caml_alloc_string` padding: the last byte is `wosize*8 - 1 - len`
      (byte c (a + 8 * o.wosize - 1)).toNat = 8 * o.wosize - 1 - b.length
  | .partialBytes b =>
      (∀ i x, b[i]? = some x → ∀ v, x = some v → byte c (a + i) = BitVec.ofNat 8 v.toNat) ∧
      (byte c (a + 8 * o.wosize - 1)).toNat = 8 * o.wosize - 1 - b.length
  | .double d => word c a = d
  | .doubleArray ds => ∀ i d, ds[i]? = some d → word c (a + 8 * i) = d
  | .int64 n => (word c a).toNat = Layout.sym_caml_int64_ops ∧ word c (a + 8) = n
  | .int32 n => (word c a).toNat = Layout.sym_caml_int32_ops ∧ word32 c (a + 8) = n
  | .nativeint n => (word c a).toNat = Layout.sym_caml_nativeint_ops ∧ word c (a + 8) = n
  | .channel id =>
      (word c a).toNat = Layout.sym_channel_operations ∧
      cp id = some (word c (a + 8)).toNat

/-- Values pointing into the heap from a value. -/
def _root_.OCaml.Bytecode.Val.loc? : Val → Option Nat
  | .ptr l _ => some l
  | _ => none

/-- Blocks reachable from a set of root values. -/
inductive Live (h : Heap) (roots : List Val) : Nat → Prop where
  | root {v : Val} {l : Nat} : v ∈ roots → v.loc? = some l → Live h roots l
  | field {l l' : Nat} {t : Nat} {fs : List Val} {v : Val} :
      Live h roots l → h.get? l = some (.block t fs) → v ∈ fs → v.loc? = some l' →
      Live h roots l'

/-- The roots of a state: registers, stack, globals, argv, named values,
and the channel blocks (the runtime's own roots; `roots_byt.c`). -/
def roots (P : Prog) (s : St) : List Val :=
  s.accu :: s.env :: P.globals :: s.world.argv :: s.stack ++ s.world.named.map (·.2) ++
    s.world.callbacks.flatMap (fun f => f.accu :: f.env :: f.stack) ++
    s.world.pendingException.toList

/-- The heap is laid out: every LIVE block is placed, laid out, and distinct
live blocks do not overlap. -/
def HeapRepr (c : Config) (pl : Place) (cp : ChanPlace) (P : Prog) (s : St) : Prop :=
  (∀ l, Live s.heap (roots P s) l → ∃ a o, pl.φ l = some a ∧ s.heap.get? l = some o ∧
      ObjAt c pl cp a o) ∧
  (∀ l l' a a' o o', Live s.heap (roots P s) l → Live s.heap (roots P s) l' → l ≠ l' →
      pl.φ l = some a → pl.φ l' = some a' → s.heap.get? l = some o → s.heap.get? l' = some o' →
      a + 8 * o.wosize ≤ a' - 8 ∨ a' + 8 * o'.wosize ≤ a - 8)

/-- The stack: `sp[i] = stack[i]` and the stack ends at `stack_high`. -/
def StackRepr (c : Config) (pl : Place) (sp high : Nat) (stk : List Val) : Prop :=
  sp + 8 * stk.length = high ∧
  ∀ i v, stk[i]? = some v → valWord pl v = some (word c (sp + 8 * i))

/-- The world: the console is the machine's HTIF output, and every channel
is laid out at its place. -/
def WorldRepr (c : Config) (cp : ChanPlace) (w : World) : Prop :=
  output c.σ = bytesToString w.console ∧
  (∀ id ch, w.chans[id]? = some ch → ∃ a, cp id = some a ∧ ChanAt c a ch) ∧
  word c Layout.sym_oo_last_id = tag64 (BitVec.ofNat 63 w.ooId)

theorem WorldRepr.output {c : Config} {cp : ChanPlace} {w : World} (h : WorldRepr c cp w) :
    Vsa.Machine.output c.σ = bytesToString w.console := h.1

theorem WorldRepr.chans {c : Config} {cp : ChanPlace} {w : World} (h : WorldRepr c cp w) :
    ∀ id ch, w.chans[id]? = some ch → ∃ a, cp id = some a ∧ ChanAt c a ch := h.2.1

theorem WorldRepr.ooId {c : Config} {cp : ChanPlace} {w : World} (h : WorldRepr c cp w) :
    word c Layout.sym_oo_last_id = tag64 (BitVec.ofNat 63 w.ooId) := h.2.2

/-- Recognize only GETPUBMET cache operands on a linear instruction decode.
An opcode-looking operand is never treated as an instruction boundary. -/
def methodCacheSlot (code : Code) (index : Nat) : Bool :=
  let rec scan : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, pc =>
      if pc > index then false else
      match decodeAt code pc with
      | none => false
      | some ins =>
        if ins.op == .GETPUBMET && index == pc + 2 then true
        else scan fuel (pc + 1 + ins.args.length)
  scan code.size 0

/-- Cache payloads may change; every opcode and ordinary operand stays pinned.
Correctness of the cache hit/miss lookup remains an F3 arm obligation, with
well-formed method tables and control flow through instruction boundaries. -/
def CodeWordOk (code : Code) (index : Nat) (expected actual : BitVec 32) : Prop :=
  methodCacheSlot code index = true ∨ actual = expected

/-- Shared code observation for dispatch states and C-call payloads. F1
never writes code, so every word is exact (as `LoadedAt.code`); F3's
`GETPUBMET` relaxes this to `CodeWordOk` (PLAN.md §Risks). -/
def CodeRepr (code : Code) (base : Nat) (c : Config) : Prop :=
  ∀ i w, code[i]? = some w → word32 c (base + 4 * i) = w

/-- The machine is at `caml_interprete`'s loop head in state `s`, under the
placement `pl`, channel placement `cp`, stack pointer `sp` and stack top
`high` (named fields: the discipline's rule for posts/entries). -/
structure VmReprAt (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) : Prop where
  atHead : pcOf c = some (BitVec.ofNat 64 Layout.loopHead)
  pc : gpr c Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
  spReg : gpr c Layout.reg_sp = some (BitVec.ofNat 64 sp)
  accu : ∃ w, gpr c Layout.reg_accu = some w ∧ valWord pl s.accu = some w
  env : ∃ w, gpr c Layout.reg_env = some w ∧ valWord pl s.env = some w
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)
  /-- `Caml_state->stack_high` (`Caml_state` is a pointer in `.bss`) -/
  stackHigh : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high
  /-- `Caml_state->trapsp`: the innermost trap frame, `s.trap` words below the top -/
  trapsp : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat =
    high - 8 * s.trap
  codeBase : (word c Layout.sym_caml_start_code).toNat = pl.codeBase
  /-- Code is immutable (F1; F3 relaxes this for GETPUBMET caches). -/
  code : CodeRepr P.code pl.codeBase c
  globals : valWord pl P.globals = some (word c Layout.sym_caml_global_data)
  stack : StackRepr c pl sp high s.stack
  heap : HeapRepr c pl cp P s
  world : WorldRepr c cp s.world
  primitives : PrimitiveBindings P c
  /-- Bind atom values to the runtime table pointer, not its global variable address. -/
  atomBase : (word c Layout.sym_caml_atom_table).toNat = pl.atomBase

/-- **`VmRepr P s c`**: the machine is at `caml_interprete`'s loop head in the
state `s` of program `P`, under SOME placement (a collection may change it). -/
def VmRepr (P : Prog) (s : St) (c : Config) : Prop :=
  ∃ (pl : Place) (cp : ChanPlace) (sp high : Nat), VmReprAt P s c pl cp sp high

end OCaml.Vm
