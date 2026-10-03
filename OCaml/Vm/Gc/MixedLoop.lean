import OCaml.Vm.Gc.MixedLoopState

namespace OCaml.Vm.Gc.MixedField
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- The expected word is supplied by the actual copying/forwarding
observation, framed from the fixed initial boundary. -/
theorem LoopAt.value {maps domain a b count start initial expected i c}
    (data : LoopData maps domain a b count start initial expected)
    (atHead : LoopAt maps a b count start initial expected i c) (bound : i < count) :
    expected i = if needsOldify domain (word c (maps i 8).toNat) c
      then word c (word c (maps i 8).toNat).toNat else word c (maps i 8).toNat := by
  have lower := atHead.scan.lower
  simp only [atHead.route data bound]
  rw [data.slot i lower bound, atHead.source data bound]
  by_cases young : needsOldify domain (word initial (scanPtr a i).toNat) initial
  · rw [ite_eq_left young, frame_word atHead.scan.memory (data.forwardingOutside i lower bound young)]
    simpa only [ite_eq_left young] using data.value i lower bound
  · simpa only [ite_eq_right young] using data.value i lower bound

/-- Every mixed iteration establishes the following native interface and
shared scan invariant by executing the selected machine route. -/
theorem LoopAt.step {maps domain a b count start initial expected i c}
    (data : LoopData maps domain a b count start initial expected)
    (atHead : LoopAt maps a b count start initial expected i c) (bound : i < count) :
    ∃ d, Steps c d ∧ LoopAt maps a b count start initial expected (i + 1) d := by
  have lower := atHead.scan.lower
  have window := data.nativeWindow i lower bound
  have stack : (MopupCall.nativeWindow (maps i)).hi ≤ b - 8 ∨
      b + 8 * count ≤ (MopupCall.nativeWindow (maps i)).lo := by
    rw [window]
    exact data.stack
  have header : (word c (b - 8)).toNat / 1024 = count := by
    rw [frame_word atHead.scan.memory data.headerOutside]
    exact data.header
  obtain ⟨d, run, post⟩ := (MixedField.step (atHead.input data bound) data.geometry
    (data.slot i lower bound) (data.delta i lower bound) (data.target i lower bound)
    (data.index i lower bound) stack header (atHead.value data bound) lower bound).run c
    ⟨by simpa [bound] using atHead.scan.pc, rfl⟩
  have footprint : MopupCall.scanFootprint (maps i) b start count =
      MopupCall.scanFootprint (maps start) b start count := by
    simp only [MopupCall.scanFootprint, window]
  have progress : FieldCopy.ScanProgress [1,8,9,10,11,12,14,15] a b count start i
      (MopupCall.scanFootprint (maps start) b start count) expected c d :=
    footprint ▸ post.progress
  refine ⟨d, run, ⟨atHead.scan.advance_progress bound progress, post.oldifyCode, ?_⟩⟩
  rw [data.advance i lower bound]
  simpa only [atHead.route data bound] using post.registers

/-- Complete suffix with an arbitrary mixture of immediate, non-young and
already-forwarded young fields. The observed scan counter proves termination;
all per-field execution inputs follow from initial observations and frames. -/
theorem mixed_scan {maps domain a b count start initial expected}
    (data : LoopData maps domain a b count start initial expected) :
    Triple (LoopAt maps a b count start initial expected start)
      (LoopAt maps a b count start initial expected count) := by
  apply indexedLoop (index := FieldCopy.scanIndex)
    (fun _ _ h => h.scan.index_eq data.geometry) (fun _ _ h => h.scan.upper)
  intro i c ⟨atHead, bound⟩
  exact atHead.step data bound

end OCaml.Vm.Gc.MixedField
