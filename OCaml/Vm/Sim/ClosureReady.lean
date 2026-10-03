import OCaml.Vm.Sim.ClosureInitInput

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closureReadyLog (c : Config) (sp count a domain : Nat) (accu : BitVec 64) : List WEntry :=
  closureSetupLog sp count a domain accu ++ valueLog (a + 16) (closureWords c sp count accu)

def closureSuffixLog (pl : Place) (a dest : Nat) : List WEntry :=
  [(a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * dest)), (a + 8, 8, 5#64)]

theorem closure_allocation_log_parts (c : Config) (pl : Place) (sp count dest a domain : Nat) (accu : BitVec 64) :
    closureReadyLog c sp count a domain accu ++ closureSuffixLog pl a dest =
      closureAllocationLog c pl sp count dest a domain accu := by
  simp only [closureReadyLog, closureSetupLog, closureHeaderLog, closureSuffixLog,
    closureAllocationLog, closureLog, closure_words_length, List.append_assoc, List.cons_append, List.nil_append]

/-- Zero captures and a completed native copy share one metadata/return suffix. -/
structure ClosureReady (before : Config) (pl : Place) (pc sp count a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x80002a60#64)
  fields : ClosureFields pl pc sp count after
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  value : gpr after 10 = some (BitVec.ofNat 64 a)
  targetReg : gpr after 16 = some (BitVec.ofNat 64 a)
  memory : after.σ.mem = writeLog before.σ.mem (closureReadyLog before sp count a domain accuWord)
  frame : StepFrameOut closureSetupWrites before.σ after.σ

theorem ClosureInitialized.ready_zero {before after : Config} {pl : Place}
    {pc sp count a domain : Nat} {accu : BitVec 64}
    (front : ClosureInitialized before pl pc sp count a domain accu after) (zero : count = 0) :
    ClosureReady before pl pc sp count a domain accu after := by
  refine ⟨front.good, front.tick, front.image, ?_, front.fields, front.accu, front.value, front.targetReg, ?_, front.frame⟩
  · simpa only [zero, Nat.lt_irrefl, ite_false] using front.pcAt
  · simp only [closureReadyLog, closureWords, zero, Nat.lt_irrefl, ite_false, valueLog, valueEntries,
      indexedLog, List.length_nil, List.range_zero, List.map_nil, List.append_nil]
    simpa only [zero] using front.memory

theorem ClosureInitialized.ready_copy {before middle after : Config} {pl : Place}
    {pc sp count a domain : Nat} {accu : BitVec 64}
    (front : ClosureInitialized before pl pc sp count a domain accu middle)
    (back : ClosureCopyAt (closureSource sp count) a (closureWords before sp count accu) middle
      (closureWords before sp count accu).length after) :
    ClosureReady before pl pc sp count a domain accu after := by
  refine ⟨back.good, back.tick, back.image, ?_, front.fields.frame back.frame (by decide),
    (back.frame.frame Register.x21 (by decide)).trans front.accu,
    (back.frame.frame Register.x10 (by decide)).trans front.value,
    (back.frame.frame Register.x16 (by decide)).trans front.targetReg, ?_,
    (front.frame.trans back.frame).widenChecked (allowed := closureSetupWrites) (by decide)⟩
  · simpa only [Nat.lt_irrefl, ite_false] using back.pc
  · change after.σ.mem = writeLog before.σ.mem (closureSetupLog sp count a domain accu ++
      valueLog (a + 16) (closureWords before sp count accu))
    rw [back.memory, forward_copy_log_complete, front.memory, writeLog_append]
    rfl

end OCaml.Vm.Sim
