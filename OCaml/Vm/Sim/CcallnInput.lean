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

/-- Native decrement for the accumulator plus the two-word saved VM frame. -/
theorem ccalln_frame_address {sp : Nat} (room : 24 ≤ sp) :
    BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfe8#12) = BitVec.ofNat 64 (sp - 24) :=
  stack_decrement room (by decide) (by decide)

/-- Positive bytecode counts use their natural value in the C ABI register. -/
theorem ccalln_count_word (count : BitVec 32) (nonnegative : 0 ≤ count.toInt) :
    sign_extend (m := 64) count = BitVec.ofNat 64 count.toInt.toNat := by
  change BitVec.ofInt 64 count.toInt = _
  have cast := congrArg (BitVec.ofInt 64) (Int.toNat_of_nonneg nonnegative)
  exact cast.symm

end OCaml.Vm.Sim
