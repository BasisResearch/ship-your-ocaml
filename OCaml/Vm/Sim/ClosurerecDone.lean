import OCaml.Vm.Sim.ClosurerecInfixStart

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- All recursive closure effects, in actual machine write order. -/
def closurerecFullLog (before : Config) (pl : Place) (sp count dest a domain : Nat)
    (accu : BitVec 64) (targets : List Nat) : List WEntry :=
  (closurerecReadyLog before sp (targets.length + 1) count a domain accu ++
    closurerecFirstLog pl sp (targets.length + 1) count dest a) ++
      (infixGroups pl a (closurerecStackStart sp count) targets).flatten

/-- Single-function and completed multi-function paths share the final return. -/
structure ClosurerecDone (before : Config) (pl : Place) (pc sp count dest a domain : Nat)
    (accuWord : BitVec 64) (targets : List Nat) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x800029b8#64)
  fields : ClosurerecFields pl pc sp (targets.length + 1) count after
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  stackReg : gpr after 9 = some (BitVec.ofNat 64 (closurerecStackStart sp count - 8 * targets.length))
  memory : after.σ.mem = writeLog before.σ.mem (closurerecFullLog before pl sp count dest a domain accuWord targets)
  frame : StepFrameOut closurerecMetadataWrites before.σ after.σ

theorem ClosurerecFirst.done_one {pl : Place} {pc sp count dest a domain : Nat}
    {accu : BitVec 64} {before after : Config}
    (front : ClosurerecFirst before pl pc sp 1 count dest a domain accu after) :
    ClosurerecDone before pl pc sp count dest a domain accu [] after := by
  refine ⟨front.good, front.tick, front.image, ?_, front.fields, front.accu, front.stackReg, ?_, front.frame⟩
  · simpa only [Nat.lt_irrefl, ite_false] using front.pcAt
  · simpa only [closurerecFullLog, infixGroups, List.length_nil, List.range_zero, List.map_nil,
      List.flatten_nil, List.append_nil] using front.memory

end OCaml.Vm.Sim
