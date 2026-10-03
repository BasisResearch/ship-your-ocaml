import OCaml.Vm.Gc.MixedSetup
import OCaml.Vm.Gc.QueueForwarded

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc LeanRV64DExecutable

/-- Initial conditions for a pending object with an already-forwarded young
first child and a mixed copied/forwarded suffix. Heap geometry, native-stack
ownership and the typed partial relocation supply these observations. -/
structure MixedPending (R : Nat → BitVec 64) (maps : Nat → Nat → BitVec 64)
    (domain : BitVec 64) (q : PendingCopy) (qs : List PendingCopy) (fields : List Val)
    (pl : Place) (μ : Nat → Nat) (tag : Nat) (c : Config) (expected : Nat → BitVec 64) : Prop where
  pop : PopInput q qs pl c
  ready : FirstReady R domain q c
  separate : FirstSeparation R q qs c
  data : MixedField.LoopData maps domain q.source.toNat q.target.toNat fields.length 1 c expected
  initialMap : maps 1 = suffixRegs R q c
  outside : MixedField.LoopOutside maps domain q.source.toNat q.target.toNat fields.length 1 c (firstFootprint R q)
  queueOutside : OutsideWindows qs (MopupCall.scanFootprint R q.target.toNat 1 fields.length)
  large : 1 < fields.length
  one : R 24 = 1#64
  header : HeaderOk (word c (q.target.toNat - 8)) fields.length tag
  grey : (pendingPayload q fields).P pl q.target.toNat c
  firstForwarding : ∀ v, fields[0]? = some v →
    word c (word c q.target.toNat).toNat = relocWord μ pl v (word c q.target.toNat)
  observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
    expected i = relocWord μ pl v (word c (q.source.toNat + 8 * i))

/-- The actual first-field result supplies the mixed setup and typed grey
boundary. All suffix observations are framed from the original queue entry. -/
theorem mixed_after_first {R maps domain q qs fields pl μ cp tag c expected}
    (input : MixedPending R maps domain q qs fields pl μ tag c expected) :
    Vsa.Logic.Triple (PopFirstPost R q qs pl c) (PopForwardedPost R q qs fields pl μ cp tag c) := by
  intro middle poppedFirst
  have memory := poppedFirst.memory_frame input.ready
  have setupInput := poppedFirst.setup_input input.ready input.data.geometry input.large input.one
    input.data.header input.outside.header
  have middleGrey := poppedFirst.grey_frame input.ready input.data.geometry input.grey
    input.firstForwarding input.outside.source
  have middleHeader : HeaderOk (word middle (q.target.toNat - 8)) fields.length tag := by
    rw [frame_word memory input.outside.header]
    exact input.header
  have middleObserved : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word middle (q.source.toNat + 8 * i)) := by
    intro i v member lower
    have bound : i < fields.length := (List.getElem?_eq_some_iff.mp member).1
    have same := frame_word memory (input.outside.source i lower bound)
    rw [input.data.geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)] at same
    rw [same]
    exact input.observed i v member lower
  have firstOutside := MopupCall.first_outside_of_stack input.data.stack input.large
  rw [input.initialMap] at firstOutside
  obtain ⟨after, run, scanned⟩ := (MixedField.setup_relocated (cp := cp)
    setupInput (input.data.frame input.outside memory) input.initialMap
    poppedFirst.setup_carried poppedFirst.oldifyCode middleGrey firstOutside middleHeader middleObserved).run middle
    ⟨poppedFirst.pc,rfl⟩
  exact ⟨after, run, poppedFirst.traversal_result input.ready input.queueOutside scanned⟩

/-- Initial queue pop and complete traversal with a mixed suffix. -/
theorem pop_mixed {R maps domain q qs fields pl μ cp tag c expected}
    (input : MixedPending R maps domain q qs fields pl μ tag c expected) :
    FnSummary MopupPop.pc (fun d => d = c) (PopForwardedPost R q qs fields pl μ cp tag c) :=
  ⟨Vsa.Logic.Triple.seq (pop_first input.pop input.ready input.separate).run (mixed_after_first input)⟩

/-- Subsequent queue visit and the same complete mixed suffix traversal. -/
theorem resume_mixed {R maps domain q qs fields pl μ cp tag c expected}
    (input : MixedPending R maps domain q qs fields pl μ tag c expected) :
    FnSummary MopupPop.resumePc (fun d => d = c) (PopForwardedPost R q qs fields pl μ cp tag c) :=
  ⟨Vsa.Logic.Triple.seq (resume_first input.pop input.ready input.separate).run (mixed_after_first input)⟩

end OCaml.Vm.Gc.WorkQueue
