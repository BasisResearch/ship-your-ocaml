import OCaml.Vm.Gc.CopyNonYoung
import OCaml.Vm.Gc.ForwardedContext

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Copying changes the source/index while retaining the incoming return
address; unlike oldify, it executes no JAL. -/
def copyNext (R : Nat → BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 8 then R 8 + 8#64 else if n = 9 then R 9 + 1#64 else R n

/-- The exact one-slot log preserves the oldify image needed by later fields. -/
theorem CopyEffect.oldifyCode_after {writes slot delta target index before after}
    (post : CopyEffect writes slot delta target index before after)
    (code : Code.Caml_oldify_oneLoaded before.σ.mem)
    (destination : WriteWindow (delta + slot) 8) :
    Code.Caml_oldify_oneLoaded after.σ.mem := by
  rw [post.memory]
  apply image_writeLog Code.caml_oldify_one_transport code
  intro e member
  have same : e = ((delta + slot).toNat, 8, word before slot.toNat) := List.mem_singleton.mp member
  subst e
  have high := destination.htif
  have codeHigh : (0x80009cb4 : Nat) ≤ Layout.sym_tohost := by decide
  change (0x80009cb4 : Nat) ≤ (delta + slot).toNat
  omega

/-- The copy route supplies the same native context interface as oldify,
with its preserved return register and concretely advanced scan registers. -/
theorem CopyEffect.next_registers {R before after}
    (post : CopyEffect copyWrites (R 8) (R 18) (R 19) (R 9) before after)
    (holds : GHolds before.σ (ForwardedField.carried R)) :
    GHolds after.σ (ForwardedField.carried (copyNext R)) := by
  have selected : GHolds before.σ ((1,R 1) :: ForwardedField.stable R) := by
    apply gholds_select holds
    intro n v member
    simp only [ForwardedField.stable, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl
  have kept : GHolds after.σ ((1,R 1) :: ForwardedField.stable R) := by
    apply gholds_of_frame post.native _ (by change KeysOK [1,2,18,19,20,21,22,23,24,25]; decide)
      ?_ ?_ selected
    · change ∀ n ∈ [1,2,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · change ∀ n ∈ [1,2,18,19,20,21,22,23,24,25], ∀ m ∈ copyWrites, (gprReg m == gprReg n) = false
      decide
  have combined := (gholds_append _ _).mpr ⟨post.registers, kept⟩
  apply gholds_select combined
  intro n v member
  simp only [ForwardedField.carried, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

end OCaml.Vm.Gc.FieldCopy
