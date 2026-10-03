import OCaml.Vm.Gc.QueueResume
import OCaml.Vm.Gc.PopForwarded

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc LeanRV64DExecutable

/-- A nonempty backedge visit uses its own generated pop certificate and
then the same verified first-field continuation as initial entry. -/
theorem resume_first {R domain q qs pl c} (input : PopInput q qs pl c)
    (ready : FirstReady R domain q c) (separate : FirstSeparation R q qs c) :
    FnSummary MopupPop.resumePc (fun d => d = c) (PopFirstPost R q qs pl c) :=
  ⟨Vsa.Logic.Triple.seq (resume_machine input).run (first_after_pop input ready separate)⟩

/-- A subsequent work-queue visit completely traverses an already-forwarded
pending object and returns to the outer queue test with its tail preserved. -/
theorem resume_forwarded {R domain q qs fields pl μ cp tag c expected}
    (input : PopInput q qs pl c) (ready : FirstReady R domain q c)
    (separate : FirstSeparation R q qs c)
    (data : ForwardedField.LoopData (suffixRegs R q c) domain q.source.toNat q.target.toNat fields.length 1 c expected)
    (outside : ForwardedField.LoopOutside (suffixRegs R q c) domain q.source.toNat q.target.toNat fields.length 1 c
      (firstFootprint R q))
    (queueOutside : OutsideWindows qs (MopupCall.scanFootprint R q.target.toNat 1 fields.length))
    (large : 1 < fields.length) (one : R 24 = 1#64)
    (header : HeaderOk (word c (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat c)
    (firstForwarding : ∀ v, fields[0]? = some v →
      word c (word c q.target.toNat).toNat = relocWord μ pl v (word c q.target.toNat))
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word c (q.source.toNat + 8 * i))) :
    FnSummary MopupPop.resumePc (fun d => d = c) (PopForwardedPost R q qs fields pl μ cp tag c) :=
  ⟨Vsa.Logic.Triple.seq (resume_first input ready separate).run
    (forwarded_after_first ready data outside queueOutside large one header grey firstForwarding observed)⟩

end OCaml.Vm.Gc.WorkQueue
