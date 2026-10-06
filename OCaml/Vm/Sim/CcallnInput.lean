import OCaml.Vm.Sim.CcallnStore
import OCaml.Vm.Sim.CcallnReturn
import OCaml.Vm.Sim.CcallSetup
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- C_CALLN uses the stack-array C ABI. The represented VM payload remains at
the original sp; a0 points to the pushed accumulator and a1 is the count.
a1-prims supplies summaries against this call-site boundary. -/
structure CcallnInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high count : Nat) (c : Config) : Prop
    extends LeafInput (0x80002e64#64) c where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  runtime : runtimeOk c
  loop : LoopRegisters c
  positive : 0 < count
  bound : count - 1 ≤ s.stack.length
  array : StackRepr c pl (sp - 8)
    (sp - 8 + 8 * (s.accu :: s.stack.take (count - 1)).length)
    (s.accu :: s.stack.take (count - 1))
  pointer : gpr c 10 = some (BitVec.ofNat 64 (sp - 8))
  countReg : gpr c 11 = some (BitVec.ofNat 64 count)

/-- Represented stack-array primitive boundary and caller-owned saved frame. -/
structure CcallnSetupPost (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high count domain nativeSp entry : Nat) (env : BitVec 64) (c : Config) : Prop where
  input : CcallnInput L.runtimeOk P s pl cp sp high count c
  saved : CcallnSaved {s with pc := s.pc + 3} pl sp count (BitVec.ofNat 64 nativeSp)
    (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 24)) env c
  target : pcOf c = some (BitVec.ofNat 64 entry)
  /-- the VM stack geometry at the callee entry (`Invariant.lean`) -/
  geometry : OCaml.LoopGeometry L P s c pl cp high
  /-- the native invocation at the callee entry (`Invocation.lean`) -/
  native : NativePlaced c

/-- C_CALLN's setup keeps the native invocation: its VM-stack and
`Caml_state` stores lie in the arena, and its native store (`sp + 88`) is a
spill slot outside `invocationRanges`. -/
theorem CcallnWriteOk.native {P : Prog} {s : St} {c after : Config} {pl : Place} {cp : ChanPlace}
    {sp high domain nativeSp : Nat} {next env accu : BitVec 64}
    (space : CcallnWriteOk P s c pl cp sp domain nativeSp next env accu) (n : NativePlaced c)
    (g : ArmGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (domainWord : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain)
    (nativeReg : gpr c 2 = some (BitVec.ofNat 64 nativeSp))
    (memory : after.σ.mem = writeLog c.σ.mem (ccallnLog sp domain nativeSp next env accu))
    (x2 : gpr after 2 = gpr c 2) : NativePlaced after := by
  obtain ⟨D, inv, valid⟩ := n
  have same : BitVec.ofNat 64 nativeSp = BitVec.ofNat 64 D.nativeSp :=
    Option.some.inj (nativeReg.symm.trans inv.stack)
  have top : D.nativeSp < 2^64 := by
    have := valid.high
    simp only [Layout.sym_stack_top] at this
    omega
  have hsp : nativeSp = D.nativeSp := by
    have h1 := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.nativeNat; omega),
      Nat.mod_eq_of_lt top] at h1
    exact h1
  have hs := stack.1
  have ha := g.arena
  have hd := g.domainArena
  have hn := space.domainNat
  have low := valid.low
  rw [domainWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hd
  have off : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
  refine ⟨D, inv.frame_log ⟨space.payload.domain, ?_⟩ memory x2, valid⟩
  intro r hr
  simp only [invocationRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have room := space.room
  rcases hr with rfl | rfl <;>
    simp only [ccallnLog, OutLRange, Layout.interpSavedRootsOffset, Layout.interpFrameBytes,
      Layout.camlMainFrameBytes, and_true] <;>
    simp only [Vsa.Sim.DlHeap.heapEnd] at low ha hd <;> omega

/-- Native decrement for the accumulator plus the two-word saved VM frame. -/
theorem ccalln_frame_address {sp : Nat} (room : 24 ≤ sp) :
    BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfe8#12) = BitVec.ofNat 64 (sp - 24) :=
  stack_decrement room (by decide) (by decide)

/-- Positive bytecode counts use their natural value in the C ABI register. -/
theorem ccalln_count_word (count : BitVec 32) (nonnegative : 0 ≤ count.toInt) :
    sign_extend (m := 64) count = BitVec.ofNat 64 count.toInt.toNat := by
  exact nonnegative_word32 count nonnegative

end OCaml.Vm.Sim
