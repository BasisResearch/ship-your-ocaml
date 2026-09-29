import OCaml.Bytecode.Semantics
import OCaml.Vm.Layout
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

/-- Where the abstract heap lives at a given moment. -/
structure Place where
  /-- address of field 0 of block `l` (the value pointer) -/
  φ : Nat → Option Nat
  /-- `caml_start_code` -/
  codeBase : Nat

/-- The machine word of a value under a placement. -/
def valWord (pl : Place) : Val → Option (BitVec 64)
  | .int n => some (tag64 n)
  | .ptr l k => (pl.φ l).map fun a => BitVec.ofNat 64 (a + 8 * k)
  | .code pc => some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  | .atom t => some (BitVec.ofNat 64 (Layout.sym_caml_atom_table + 8 * t + 8))
  | .raw w => some w

/-- A header word describes `wosize` and `tag` (the two color bits are the
major GC's business and unconstrained). -/
def HeaderOk (w : BitVec 64) (wosize tag : Nat) : Prop :=
  w.toNat % 256 = tag ∧ w.toNat / 1024 = wosize

/-- `struct channel` field offsets (`runtime/caml/io.h`, LP64). -/
def chanOffFd : Nat := 0
def chanOffCurr : Nat := 24
def chanOffBuff : Nat := 72

/-- A channel structure at `a` holds `ch`: its fd, and its pending bytes
between `buff` and `curr`. -/
def ChanAt (c : Config) (a : Nat) (ch : Chan) : Prop :=
  (word32 c (a + chanOffFd)).toInt = ch.fd ∧
  (word c (a + chanOffCurr)).toNat = a + chanOffBuff + ch.buf.length ∧
  ∀ i (b : UInt8), ch.buf[i]? = some b → byte c (a + chanOffBuff + i) = BitVec.ofNat 8 b.toNat

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
  s.accu :: s.env :: P.globals :: s.world.argv :: s.stack ++ s.world.named.map (·.2)

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
  ∀ id ch, w.chans[id]? = some ch → ∃ a, cp id = some a ∧ ChanAt c a ch

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
  /-- the code, unmodified (F3's `GETPUBMET` relaxes this to "up to caches") -/
  code : ∀ i w, P.code[i]? = some w → word32 c (pl.codeBase + 4 * i) = w
  globals : valWord pl P.globals = some (word c Layout.sym_caml_global_data)
  stack : StackRepr c pl sp high s.stack
  heap : HeapRepr c pl cp P s
  world : WorldRepr c cp s.world

/-- **`VmRepr P s c`**: the machine is at `caml_interprete`'s loop head in the
state `s` of program `P`, under SOME placement (a collection may change it). -/
def VmRepr (P : Prog) (s : St) (c : Config) : Prop :=
  ∃ (pl : Place) (cp : ChanPlace) (sp high : Nat), VmReprAt P s c pl cp sp high

end OCaml.Vm
