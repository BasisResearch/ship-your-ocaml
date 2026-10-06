import OCaml.Vm.Boot.Startup.SearchExeReset
import OCaml.Vm.Boot.Startup.AttemptOpenCalls
import OCaml.Vm.Boot.Startup.GcMessageQuiet
import OCaml.Vm.Boot.Startup.Strdup
import OCaml.Vm.Boot.Startup.StatFree
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- The heap copy of `argv[0]` is a C string of eight bytes. -/
theorem ResetSearchExeReturned.copy_bytes {initial after} (w : ResetSearchExeReturned initial after) :
    CBytes after.σ.mem w.copy.toNat 8 where
  nz := fun i hi => by
    change (after.σ.mem[w.copy.toNat + i]?).getD 0 ≠ 0
    rw [w.name i (by omega)]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  nul := by
    change (after.σ.mem[w.copy.toNat + 8]?).getD 0 = 0
    rw [w.name 8 (by decide)]; decide
  lo := by have := w.fresh.1; unfold heapStart at this; omega
  hi := by have := w.fresh.2; unfold heapEnd at this; omega
  htif := Or.inr (by have := w.fresh.1; unfold heapStart at this; omega)

/-- Actual reset execution from the search's return through the duplicated
name, the quiet opening message and its free, up to `open(truename, O_RDONLY)`. -/
structure ResetOpenCall (initial after : Config) where
  atSearch : Config
  search : ResetSearchExeReturned initial atSearch
  pc : PCAt 0x80042590#64 after
  link : gprGet after.σ 1 = some jal_80004920_call.link
  path : gprGet after.σ 10 = some search.copy
  flags : gprGet after.σ 11 = some 0#64
  stack : gprGet after.σ 2 = some attemptStack
  truename : gprGet after.σ 18 = some search.copy
  ready : RuntimeReady ((search.copy.toNat, 9) :: search.path.table.H) (startupAllocatorCredits - 480)
    attemptStack jal_80004920_call.link after
  name : ∀ k, k ≤ 8 →
    (after.σ.mem[search.copy.toNat + k]?).getD 0 = BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars k)
  kept : KeptImage after
  run : Steps (Vsa.Densify.fillZero initial) after
  /-- caml_attempt_open's frame is kept since its saves. -/
  caller : CallerFrame attemptStack search.path.table.atSaved after

theorem reset_open_call_exists : ∃ initial after, Nonempty (ResetOpenCall initial after) := by
  obtain ⟨initial, atS, ⟨w⟩⟩ := reset_search_exe_returned_exists
  have readyS := w.ready
  have frameS : NativeFrame attemptStack (48 + allocHeadroom) := by constructor <;> decide
  -- caml_stat_strdup(truename)
  obtain ⟨atDup, run1, dcall⟩ := (attempt_open_strdup atS _ attemptStack w.copy readyS.toLeafInput
    ⟨w.result, w.stack, trivial⟩).run atS ⟨w.pc, rfl⟩
  have readyDup := readyS.stack_log dcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dcall.regs (by rfl)) (gholds_lookup (n := 1) _ dcall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  have credits : startupAllocatorCredits - 464 = (startupAllocatorCredits - 480) + 16 := by decide
  have readyDup16 : RuntimeReady ((w.copy.toNat, 9) :: w.path.table.H) ((startupAllocatorCredits - 480) + 16)
      attemptStack jal_800048f4_call.link atDup := by
    rw [← credits]; exact readyDup
  have sameDup : atDup.σ.mem = atS.σ.mem := dcall.memory
  have toDup (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [18] ++ [1])
      (hv : gprGet atS.σ n = some v) : gprGet atDup.σ n = some v :=
    (dcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  obtain ⟨atMsg, run2, ⟨D⟩⟩ := (strdup_full atDup _ (startupAllocatorCredits - 480) 16 attemptStack
    jal_800048f4_call.link trailSlot (BitVec.ofNat 64 WhileMinImage.argvArray) w.copy 8 readyDup16 frameS
    ⟨toDup 9 _ (by decide) (by decide) (by decide) w.saved1, toDup 8 _ (by decide) (by decide) (by decide) w.saved0,
      gholds_lookup (n := 10) _ dcall.regs (by rfl), trivial⟩
    (by rw [sameDup]; exact w.copy_bytes)
    (fun k hk => Or.inr (Or.inr (Or.inr ⟨w.copy.toNat, 9, List.mem_cons_self .., w.fresh.1, w.fresh.2,
      by omega, by omega⟩)))
    (Or.inr (by have := w.fresh.1; unfold heapStart at this; unfold Layout.sym_tohost; omega)) (by decide)
    ⟨by decide, by decide⟩).run atDup ⟨dcall.pc, rfl⟩
  have keptMsg : KeptImage atMsg :=
    w.kept.frame ((EmbedFrame.of_memory sameDup).trans ⟨fun a ha => D.kept a (ha.strdup_kept (by decide))⟩)
  -- caml_gc_message(0x100, fmt, copy2)
  obtain ⟨atGc, run3, mcall⟩ := (attempt_open_message atMsg _ attemptStack D.copy D.ready.toLeafInput
    ⟨D.result, D.stack, trivial⟩).run atMsg ⟨D.pc, rfl⟩
  have readyGc := D.ready.stack_log mcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ mcall.regs (by rfl)) (gholds_lookup (n := 1) _ mcall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  have frameGc : NativeFrame attemptStack 80 := by constructor <;> decide
  obtain ⟨atFree, run4, gc⟩ := (gc_message_quiet atGc attemptStack _ D.copy (vsaReg atGc 13) (vsaReg atGc 14)
    (vsaReg atGc 15) (vsaReg atGc 16) (vsaReg atGc 17) 0x100#64 readyGc.toLeafInput frameGc
    ⟨gholds_lookup (n := 2) _ mcall.regs (by rfl), gholds_lookup (n := 1) _ mcall.regs (by rfl),
      gholds_lookup (n := 12) _ mcall.regs (by rfl), gpr_of_ready readyGc 13 (by decide) (by decide),
      gpr_of_ready readyGc 14 (by decide) (by decide), gpr_of_ready readyGc 15 (by decide) (by decide),
      gpr_of_ready readyGc 16 (by decide) (by decide), gpr_of_ready readyGc 17 (by decide) (by decide),
      gholds_lookup (n := 10) _ mcall.regs (by rfl), trivial⟩
    (keptMsg.frame (EmbedFrame.of_memory mcall.memory)).verbGc).run atGc ⟨mcall.pc, rfl⟩
  have readyFree := readyGc.stack_log gc (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ gc.regs (by rfl)) (gholds_lookup (n := 1) _ gc.regs (by rfl))
    (by decide) frameGc (gcMessageLog_inside frameGc)
  -- caml_stat_free(copy2)
  obtain ⟨atStat, run5, fcall⟩ := (attempt_open_free_copy atFree _ attemptStack D.copy readyFree.toLeafInput
    ⟨(gc.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 9) _ mcall.regs (by rfl)), readyFree.stack, trivial⟩).run atFree ⟨gc.pc, rfl⟩
  have readyStat := readyFree.stack_log fcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ fcall.regs (by rfl)) (gholds_lookup (n := 1) _ fcall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  obtain ⟨atOpen, run6, ⟨freed⟩⟩ := (stat_free_block atStat _ D.copy (8 + 1) (startupAllocatorCredits - 480)
    attemptStack jal_80004914_call.link readyStat (gholds_lookup (n := 10) _ fcall.regs (by rfl))
    (frameS.resize (by decide) (by decide)) D.fresh.1 D.fresh.2).run atStat ⟨fcall.pc, rfl⟩
  -- open(truename, O_RDONLY)
  have truenameO : gprGet atOpen.σ 18 = some w.copy :=
    (freed.saved_gpr (k := 18) (by decide)).trans
      ((fcall.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
        ((gc.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
          ((mcall.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
            ((D.saved23 18 (by decide)).trans (gholds_lookup (n := 18) _ dcall.regs (by rfl))))))
  obtain ⟨atCall, run7, ocall⟩ := (attempt_open_open atOpen _ attemptStack w.copy freed.ready.toLeafInput
    ⟨truenameO, freed.ready.stack, trivial⟩).run atOpen
    ⟨library_pc freed.free.good freed.free.result.frame.pc, rfl⟩
  have readyCall := freed.ready.stack_log ocall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ ocall.regs (by rfl)) (gholds_lookup (n := 1) _ ocall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  have frameA : NativeFrame attemptStack allocHeadroom := frameS.resize (by decide) (by decide)
  refine ⟨initial, atCall, ⟨atS, w, ocall.pc, gholds_lookup (n := 1) _ ocall.regs (by rfl),
    gholds_lookup (n := 10) _ ocall.regs (by rfl), gholds_lookup (n := 11) _ ocall.regs (by rfl),
    gholds_lookup (n := 2) _ ocall.regs (by rfl), gholds_lookup (n := 18) _ ocall.regs (by rfl), readyCall, ?_, ?_,
    w.run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))), ?_⟩⟩
  · intro k hk
    have inside : InExt (w.copy.toNat, 9) (w.copy.toNat + k) := ⟨by omega, by omega⟩
    have apart : ¬ InExt (D.copy.toNat, 8 + 1) (w.copy.toNat + k) := fun copy2 =>
      D.disjoint _ (List.mem_cons_self ..) _ copy2 inside
    have arena : heapStart ≤ w.copy.toNat + k ∧ w.copy.toNat + k < heapEnd :=
      ⟨by have := w.fresh.1; omega, by have := w.fresh.2; omega⟩
    have lower : heapEnd ≤ nativeFrameBase attemptStack 80 := by decide
    rw [show atCall.σ.mem = atOpen.σ.mem from ocall.memory,
      freed.live_byte frameA (List.mem_cons_self ..) inside apart arena,
      show atStat.σ.mem = atFree.σ.mem from fcall.memory, gc.memory,
      frameOn_writeLog _ _ _ (gcMessageLog_inside frameGc) _ ⟨Or.inl (by dsimp only; omega),
        trivial⟩,
      show atGc.σ.mem = atMsg.σ.mem from mcall.memory,
      D.kept _ (Or.inr (Or.inr (Or.inr ⟨w.copy.toNat, 9, List.mem_cons_self .., w.fresh.1, w.fresh.2,
        by omega, by omega⟩))), sameDup]
    exact w.name k hk
  · exact ((keptMsg.frame (EmbedFrame.of_memory mcall.memory)).frame
      ((EmbedFrame.stack gc.memory (gcMessageLog_inside frameGc) (by decide)).trans
        ((EmbedFrame.of_memory fcall.memory).trans ((freed.embed_frame frameA (by decide) D.fresh.1 D.fresh.2).trans
          (EmbedFrame.of_memory ocall.memory)))))
  · refine w.caller.trans ⟨fun a bound => ?_⟩
    rw [show atCall.σ.mem = atOpen.σ.mem from ocall.memory,
      freed.byte frameA (by decide) D.fresh.1 D.fresh.2 (Or.inl bound),
      show atStat.σ.mem = atFree.σ.mem from fcall.memory, gc.memory,
      frameOn_writeLog _ _ _ (gcMessageLog_inside frameGc) _ ⟨Or.inr bound, trivial⟩,
      show atGc.σ.mem = atMsg.σ.mem from mcall.memory, D.kept a (Or.inl bound), sameDup]
end OCaml.Vm.Boot.WhileMinElfParse
