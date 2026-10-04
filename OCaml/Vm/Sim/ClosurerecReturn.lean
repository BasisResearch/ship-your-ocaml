import OCaml.Vm.Sim.ClosurerecDone
import OCaml.Vm.Sim.ClosurerecSuffixSegment
import OCaml.Vm.Sim.ClosurerecSuffixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Native loop-head result; heap and abstract-stack readback are separate obligations. -/
structure ClosurerecReturned (before : Config) (pl : Place) (pc sp count dest a domain : Nat)
    (accuWord : BitVec 64) (targets : List Nat) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (BitVec.ofNat 64 Layout.loopHead)
  codeReg : gpr after 8 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3 + (targets.length + 1))))
  stackReg : gpr after 9 = some (BitVec.ofNat 64 (closurerecStackStart sp count - 8 * targets.length))
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  memory : after.σ.mem = writeLog before.σ.mem (closurerecFullLog before pl sp count dest a domain accuWord targets)
  frame : StepFrameOut closurerecMetadataWrites before.σ after.σ

/-- The actual shared suffix skips every offset-table word and returns to dispatch. -/
theorem closurerec_return {pl : Place} {pc sp count dest a domain : Nat} {targets : List Nat}
    {accu : BitVec 64} {before d : Config}
    (front : ClosurerecDone before pl pc sp count dest a domain accu targets d) :
    ∃ nb after, StepsN nb d after ∧ ClosurerecReturned before pl pc sp count dest a domain accu targets after := by
  have shift : Sail.shift_bits_left (BitVec.ofNat 64 (targets.length + 1)) (Sail.BitVec.extractLsb (0x02#6) 5 0) =
      BitVec.ofNat 64 (4 * (targets.length + 1)) := by
    change (BitVec.ofNat 64 (targets.length + 1) <<< (2 : Nat)) = _
    exact nat_shift_word _ 2
  have bp : SegSt (0x800029b8#64)
      [⟨Register.x17, BitVec.ofNat 64 (targets.length + 1)⟩,
       ⟨Register.x16, BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3))⟩]
      (fun σ => Vsa.Sim.Code.CamlClosurerecSuffixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨front.good, front.pcAt, ⟨front.fields.functionsReg, front.fields.codeBase, trivial⟩,
      front.good.minstret, front.tick, closurerec_suffix_loaded front.image, rfl, rfl⟩
  have run := tr_closurerec_suffix (BitVec.ofNat 64 (targets.length + 1))
    (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3))) d.σ.mem d.σ
  simp only [shift, codePc_add pl (pc + 3) (targets.length + 1)] at run
  obtain ⟨nb, after, _, steps, post⟩ := run d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked (allowed := [Register.x8, Register.x17] ++ noiseRegs) (by decide)
  exact ⟨nb, after, steps, post.good, post.tick, image_of_writeLog (log := []) front.image ⟨trivial, trivial⟩ memory,
    post.pcAt, PinsHold.get post.pins ⟨0, by simp⟩,
    (frame.frame Register.x9 (by decide)).trans front.stackReg,
    (frame.frame Register.x21 (by decide)).trans front.accu, memory.trans front.memory,
    (front.frame.trans frame).widenChecked (allowed := closurerecMetadataWrites) (by decide)⟩

end OCaml.Vm.Sim
