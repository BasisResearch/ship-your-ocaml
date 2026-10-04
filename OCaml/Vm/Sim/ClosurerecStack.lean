import OCaml.Vm.Sim.ClosurerecDone
import OCaml.Vm.Sim.ClosurerecStackSegment
import OCaml.Vm.Sim.ClosurerecStackPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The actual post-loop stack adjustment accounts for every pushed infix pointer. -/
theorem closurerec_stack {pl : Place} {pc sp count dest a domain : Nat} {targets : List Nat}
    {accu : BitVec 64} {before first copied : Config}
    (front : ClosurerecFirst before pl pc sp (targets.length + 1) count dest a domain accu first)
    (back : InfixAt pl pc a (closurerecStackStart sp count) targets first targets.length copied)
    (room : 8 * targets.length ≤ closurerecStackStart sp count) :
    ∃ nb after, StepsN nb copied after ∧ ClosurerecDone before pl pc sp count dest a domain accu targets after := by
  have small := front.fields.nurseryBound
  unfold closurerecSize at small
  have countWord := addiw_nat_pred (targets.length + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at countWord
  have scale := infix_stack_scale targets.length (by omega)
  have stackAddress : BitVec.ofNat 64 (closurerecStackStart sp count) - BitVec.ofNat 64 (8 * targets.length) =
      BitVec.ofNat 64 (closurerecStackStart sp count - 8 * targets.length) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) room
  have bp : SegSt (0x800029a8#64)
      [⟨Register.x17, BitVec.ofNat 64 (targets.length + 1)⟩,
       ⟨Register.x9, BitVec.ofNat 64 (closurerecStackStart sp count)⟩]
      (fun σ => Vsa.Sim.Code.CamlClosurerecStackLoaded σ.mem ∧ σ.mem = copied.σ.mem ∧ σ = copied.σ) copied :=
    ⟨back.good, by change pcOf copied = some (0x800029a8#64); simpa only [Nat.lt_irrefl, ite_false] using back.pcAt,
      ⟨(back.frame.frame Register.x17 (by decide)).trans front.fields.functionsReg,
        (back.frame.frame Register.x9 (by decide)).trans front.stackReg, trivial⟩,
      back.good.minstret, back.tick, closurerec_stack_loaded back.image, rfl, rfl⟩
  have run := tr_closurerec_stack (BitVec.ofNat 64 (targets.length + 1))
    (BitVec.ofNat 64 (closurerecStackStart sp count)) copied.σ.mem copied.σ
  simp only [countWord, scale, stackAddress] at run
  obtain ⟨nb, after, _, steps, post⟩ := run copied bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked (allowed := [Register.x9, Register.x14, Register.x15] ++ noiseRegs) (by decide)
  have whole := (back.frame.trans frame).widenChecked (allowed := infixWrites ++ [Register.x9]) (by decide)
  refine ⟨nb, after, steps, post.good, post.tick, image_of_writeLog (log := []) back.image ⟨trivial, trivial⟩ memory, post.pcAt,
    (front.fields.frame back.frame (by decide)).frame frame (by decide),
    (whole.frame Register.x21 (by decide)).trans front.accu, PinsHold.get post.pins ⟨0, by simp⟩, ?_,
    (front.frame.trans whole).widenChecked (allowed := closurerecMetadataWrites) (by decide)⟩
  rw [memory, back.memory, show targets.length = (infixGroups pl a (closurerecStackStart sp count) targets).length from
    (infix_groups_length _ _ _ _).symm, grouped_log_complete, front.memory, closurerecFullLog]
  simp only [writeLog_append]

end OCaml.Vm.Sim
