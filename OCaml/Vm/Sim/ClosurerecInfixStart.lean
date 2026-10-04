import OCaml.Vm.Sim.ClosurerecInfix

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- The first metadata span's natural arity equals the loop's modular form. -/
theorem infix_arity_first (functions : Nat) (more : 1 < functions) :
    infixArityWord functions 1 = BitVec.ofNat 64 (2 * (3 * functions - 4) + 1) := by
  unfold infixArityWord
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  congr 1
  omega

/-- First-function metadata establishes the remaining-function loop at index zero. -/
theorem ClosurerecFirst.infix_start {pl : Place} {pc sp count dest a domain : Nat}
    {targets : List Nat} {accu : BitVec 64} {before after : Config}
    (front : ClosurerecFirst before pl pc sp (targets.length + 1) count dest a domain accu after)
    (more : 0 < targets.length) :
    InfixAt pl pc a (closurerecStackStart sp count) targets after 0 after := by
  have positive : 1 < targets.length + 1 := by omega
  have regs := front.infixRegisters positive
  refine ⟨front.good, front.tick, front.image, Nat.zero_le _, ?_, ⟨?_, ?_, ?_, ?_, ?_, front.fields.codeBase, regs.limit⟩,
    rfl, (StepFrameOut.refl after.σ).widenChecked (allowed := infixWrites) (by decide)⟩
  · simpa only [positive, more, ite_true] using front.pcAt
  · exact regs.counter
  · simpa only [Nat.zero_add, Nat.mul_one] using regs.targetReg
  · simpa only [Nat.mul_zero, Nat.sub_zero] using regs.stackReg
  · simpa only [Nat.add_zero] using regs.codeReg
  · rw [infix_arity_first _ positive]
    exact regs.arity

end OCaml.Vm.Sim
