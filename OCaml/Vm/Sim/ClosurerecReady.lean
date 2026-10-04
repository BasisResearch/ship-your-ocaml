import OCaml.Vm.Sim.ClosurerecInitInput

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closurerecReadyLog (c : Config) (sp functions count a domain : Nat) (accu : BitVec 64) : List WEntry :=
  closurerecSetupLog sp functions count a domain accu ++ valueLog (closurerecCaptureBase a functions) (closureWords c sp count accu)

/-- Zero captures and a completed native copy share one metadata/return suffix. -/
structure ClosurerecReady (before : Config) (pl : Place) (pc sp functions count a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x8000291c#64)
  fields : ClosurerecFields pl pc sp functions count after
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  value : gpr after 15 = some (BitVec.ofNat 64 a)
  memory : after.σ.mem = writeLog before.σ.mem (closurerecReadyLog before sp functions count a domain accuWord)
  frame : StepFrameOut closurerecSetupWrites before.σ after.σ

theorem ClosurerecInitialized.ready_zero {before after : Config} {pl : Place}
    {pc sp functions count a domain : Nat} {accu : BitVec 64}
    (front : ClosurerecInitialized before pl pc sp functions count a domain accu after) (zero : count = 0) :
    ClosurerecReady before pl pc sp functions count a domain accu after := by
  refine ⟨front.good, front.tick, front.image, ?_, front.fields, front.accu, front.value, ?_, front.frame⟩
  · simpa only [zero, Nat.lt_irrefl, ite_false] using front.pcAt
  · simp only [closurerecReadyLog, closureWords, zero, Nat.lt_irrefl, ite_false, valueLog, valueEntries,
      indexedLog, List.length_nil, List.range_zero, List.map_nil, List.append_nil]
    simpa only [zero] using front.memory

theorem ClosurerecInitialized.ready_copy {before middle after : Config} {pl : Place}
    {pc sp functions count a domain : Nat} {accu : BitVec 64}
    (front : ClosurerecInitialized before pl pc sp functions count a domain accu middle)
    (back : ClosurerecCopyAt (closureSource sp count) (closurerecCaptureBase a functions) (closureWords before sp count accu) middle
      (closureWords before sp count accu).length after) :
    ClosurerecReady before pl pc sp functions count a domain accu after := by
  refine ⟨back.good, back.tick, back.image, ?_, front.fields.frame back.frame (by decide),
    (back.frame.frame Register.x21 (by decide)).trans front.accu,
    (back.frame.frame Register.x15 (by decide)).trans front.value,
    ?_,
    (front.frame.trans back.frame).widenChecked (allowed := closurerecSetupWrites) (by decide)⟩
  · simpa only [Nat.lt_irrefl, ite_false] using back.pc
  · change after.σ.mem = writeLog before.σ.mem (closurerecSetupLog sp functions count a domain accu ++
      valueLog (closurerecCaptureBase a functions) (closureWords before sp count accu))
    rw [back.memory, forward_copy_log_complete, front.memory, writeLog_append]

end OCaml.Vm.Sim
