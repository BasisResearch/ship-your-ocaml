import OCaml.Vm.Gc.PopScan

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable MopupPop

/-- The bottom-test head load has the same data access as the initial test. -/
theorem resume_head_access (q : PendingCopy) (c : Config) :
    AccessPlan c.σ.mem regs (loads q c) resumeHead.body := by
  exact head_access q c

theorem resume_head_control {q qs pl c} (view : View (q :: qs) pl c)
    (nonzero : q.source ≠ 0) :
    TermFactsO (runGM resumeHead.body regs (loads q c)) resumeHead.term := by
  change TermFactsO (runGM headBlock.body regs (loads q c)) resumeHead.term
  rw [head_regs view]
  simpa [resumeHead, caml_oldify_mopupX9d88TSeg, TermFactsO, TermFactsT,
    guardB, srcVal, lookupG] using nonzero

theorem resume_access {q qs pl c} (view : View (q :: qs) pl c)
    (windows : PopWindows q) (nonzero : q.source ≠ 0) :
    ChainAccess c.σ.mem regs (loads q c) (resumeBlocks (firstImmediate q c)) := by
  apply ChainAccess.cons ⟨resume_head_access q c, resume_head_control view nonzero⟩
  change ChainAccess c.σ.mem (runGM headBlock.body regs (loads q c))
    (loads q c).tail [childBlock (firstImmediate q c)]
  rw [head_regs view]
  exact ChainAccess.cons ⟨child_access view windows _, child_control q c⟩ ChainAccess.nil

/-- Actual execution from the bottom queue test, reusing the shared exact
pop effect only after certifying this entry's own code and branch. -/
theorem resume_machine {q qs pl c} (input : PopInput q qs pl c) :
    FnSummary resumePc (fun d => d = c) (PopPost q qs pl c) := by
  have summary := block_summary (resumeBlocks (firstImmediate q c)) resumePc regs (loads q c) c
    ⟨input.good, input.minstret, input.registers, by decide,
      chainPlan_facts (resume_code _ input.code) (resume_access input.queue input.windows input.nonzero),
      resume_ok _, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after effects
  have common := resume_effects effects
  have post : MopupPop.Post (firstImmediate q c) (loads q c) c.σ.mem after :=
    segmentPost_of_block common
  exact ⟨post, pop_loaded input.queue post input.separate, common⟩

/-- Every subsequent queue visit uses the same verified scan continuation. -/
theorem resume_scan {q qs fields pl cp tag c}
    (input : PopInput q qs pl c)
    (geometry : FieldCopy.Geometry q.source.toNat q.target.toNat fields.length)
    (large : 1 < fields.length)
    (header : HeaderOk (word c (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat c)
    (integers : ∀ (i : Nat) v, fields[i]? = some v → ∃ n, v = Val.int n)
    (outside : PayloadOutsideTodo q fields.length)
    (queueOutside : QueueOutsideScan qs q.target.toNat fields.length)
    (s8 : gprGet c.σ 24 = some 1#64) :
    FnSummary resumePc (fun d => d = c) (PopScanPost q qs fields pl cp tag c) :=
  ⟨Vsa.Logic.Triple.seq (resume_machine input).run
    (scan_after_pop input geometry large header grey integers outside queueOutside s8)⟩

end OCaml.Vm.Gc.WorkQueue
