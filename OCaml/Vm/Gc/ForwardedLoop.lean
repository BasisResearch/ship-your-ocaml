import OCaml.Vm.Gc.ForwardedLoopState

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- One complete machine iteration preserves both the relocated scan and
the native/runtime context required to derive the following field's input. -/
theorem LoopAt.step {R domain a b count start initial expected i c}
    (data : LoopData R domain a b count start initial expected)
    (atHead : LoopAt R a b count start initial expected i c) (bound : i < count) :
    ∃ d, Steps c d ∧ LoopAt R a b count start initial expected (i + 1) d := by
  have input := atHead.input data bound
  have header : (word c (b - 8)).toNat / 1024 = count := by
    rw [frame_word atHead.scan.memory data.headerOutside]
    exact data.header
  have forwarding : word c (word c (scanPtr a i).toNat).toNat = expected i := by
    rw [atHead.source data bound,
      frame_word atHead.scan.memory (data.forwardingOutside i atHead.scan.lower bound)]
    exact data.forwarding i atHead.scan.lower bound
  obtain ⟨d, run, post⟩ := (forwarded_field input).run c
    ⟨by simpa [bound] using atHead.scan.pc, rfl⟩
  have progress := input.scan_progress post data.geometry rfl data.delta data.target rfl
    data.stack header forwarding atHead.scan.lower bound
  refine ⟨d, run, ⟨atHead.scan.advance_progress bound progress, input.oldifyCode_after post, ?_⟩⟩
  have registers := input.next_registers post
  rw [cursor_next atHead.scan.lower] at registers
  exact registers

/-- Complete already-forwarded young-field suffix. Every iteration executes
the real load/classifier/callee/advance route; fixed heap observations and
separation derive its input, and the observed counter supplies termination. -/
theorem forwarded_scan {R domain a b count start initial expected}
    (data : LoopData R domain a b count start initial expected) :
    Triple (LoopAt R a b count start initial expected start)
      (LoopAt R a b count start initial expected count) := by
  apply indexedLoop (index := FieldCopy.scanIndex)
    (fun _ _ h => h.scan.index_eq data.geometry) (fun _ _ h => h.scan.upper)
  intro i c ⟨atHead, bound⟩
  exact atHead.step data bound

end OCaml.Vm.Gc.ForwardedField
