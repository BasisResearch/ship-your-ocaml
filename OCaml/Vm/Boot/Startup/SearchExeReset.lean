import OCaml.Vm.Boot.Startup.PathReset
import OCaml.Vm.Boot.Startup.SearchExeTail
import OCaml.Vm.Boot.Startup.SearchExeFrames
import OCaml.Vm.Boot.Startup.DecomposeNull
import OCaml.Vm.Boot.Startup.FreeNull
import OCaml.Vm.Boot.Startup.ReadyPerm
import OCaml.Vm.Boot.Startup.Argv0Name
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Actual reset execution through `caml_search_exe_in_path("ocamlrun")`: PATH
is unset, so the search returns a fresh heap copy of the name. -/
structure ResetSearchExeReturned (initial after : Config) where
  atPath : Config
  path : ResetPathMissed initial atPath
  copy : BitVec 64
  result : gprGet after.σ 10 = some copy
  pc : PCAt jal_800048ec_call.link after
  stack : gprGet after.σ 2 = some attemptStack
  saved0 : gprGet after.σ 8 = some trailSlot
  saved1 : gprGet after.σ 9 = some (BitVec.ofNat 64 WhileMinImage.argvArray)
  saved2 : gprGet after.σ 18 = some (vsaReg path.source 18)
  saved3 : gprGet after.σ 19 = some (vsaReg path.source 19)
  ready : RuntimeReady ((copy.toNat, 9) :: path.table.H) (startupAllocatorCredits - 464) attemptStack
    jal_800048ec_call.link after
  fresh : heapStart ≤ copy.toNat ∧ copy.toNat + 9 ≤ heapEnd
  name : ∀ k, k ≤ 8 →
    (after.σ.mem[copy.toNat + k]?).getD 0 = BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars k)
  kept : KeptImage after
  run : Steps (Vsa.Densify.fillZero initial) after
  aligned : copy.toNat % 16 = 0
  /-- caml_attempt_open's frame is kept since its saves. -/
  caller : CallerFrame attemptStack path.table.atSaved after

theorem reset_search_exe_returned_exists : ∃ initial after, Nonempty (ResetSearchExeReturned initial after) := by
  obtain ⟨initial, atD, ⟨w⟩⟩ := reset_path_missed_exists
  have frame112 : NativeFrame searchStack 112 := by constructor <;> decide
  have frame32 : NativeFrame searchStack 32 := by constructor <;> decide
  have readyS := w.table.returned.ready
  have readyG := readyS.stack_log w.call (by decide) (by simp only [keysG]; decide) (by decide)
    ((w.call.frame .x2 (by decide) (by decide)).trans readyS.stack) (gholds_lookup (n := 1) _ w.call.regs (by rfl))
    (by decide) frame112 (by simp only [LogInW])
  have readyD := readyG.stack_log w.missed (by decide)
    (by simp only [getenvReturnRegs, getenvMissKeptRegs, getenvSavedRegs, findMissScratch, List.cons_append,
      List.nil_append, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ w.missed.regs (by rfl)) (gholds_lookup (n := 1) _ w.missed.regs (by rfl))
    (by decide) frame112 (getenvMissLog_inside frame112)
  -- caml_decompose_path(&path, NULL)
  obtain ⟨atDec, run1, dcall⟩ := (search_exe_decompose atD _ searchStack 0#64 readyD.toLeafInput
    ⟨gholds_lookup (n := 10) _ w.missed.regs (by rfl), gholds_lookup (n := 2) _ w.missed.regs (by rfl),
      trivial⟩).run atD ⟨w.missed.pc, rfl⟩
  have readyDec := readyD.stack_log dcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dcall.regs (by rfl)) (gholds_lookup (n := 1) _ dcall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  have s2D : gprGet atDec.σ 18 = some (vsaReg w.source 18) :=
    (dcall.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 18) _ w.missed.regs (by rfl))
  obtain ⟨atS, run2, dnull⟩ := (decompose_null atDec searchStack jal_80025564_call.link (vsaReg w.source 18)
    searchStack readyDec.toLeafInput frame32
    ⟨gholds_lookup (n := 2) _ dcall.regs (by rfl), gholds_lookup (n := 1) _ dcall.regs (by rfl), s2D,
      gholds_lookup (n := 11) _ dcall.regs (by rfl), gholds_lookup (n := 10) _ dcall.regs (by rfl),
      trivial⟩).run atDec ⟨dcall.pc, rfl⟩
  have readyS2 := readyDec.stack_log dnull (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dnull.regs (by rfl)) (gholds_lookup (n := 1) _ dnull.regs (by rfl))
    (by decide) frame32 (decomposeLog_inside frame32)
  -- registers carried from getenv's return through the decomposition
  have carried (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [2, 1, 18, 10] ∧ n ∉ [11, 10] ++ [1]) (hv : gprGet atD.σ n = some v) :
      gprGet atS.σ n = some v :=
    (dnull.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans
      ((dcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2).trans hv)
  have s0S : gprGet atS.σ 8 = some argv0Ptr := by
    rw [← w.table.exe_name]
    exact carried 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ w.missed.regs (by rfl))
  -- caml_search_in_path(&path, name)
  obtain ⟨atP, run3, scall⟩ := (search_exe_search atS _ searchStack argv0Ptr 0#64 readyS2.toLeafInput
    ⟨s0S, gholds_lookup (n := 10) _ dnull.regs (by rfl), gholds_lookup (n := 2) _ dnull.regs (by rfl),
      trivial⟩).run atS ⟨dnull.pc, rfl⟩
  have readyP := readyS2.stack_log scall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ scall.regs (by rfl)) (gholds_lookup (n := 1) _ scall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  have toP (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [11, 9, 10] ++ [1])
      (hv : gprGet atS.σ n = some v) : gprGet atP.σ n = some v :=
    (scall.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  -- memory: the caller frame and the kept image up to the search
  have callerP : CallerFrame searchStack w.source atP :=
    (CallerFrame.of_memory w.call.memory).trans ((CallerFrame.of_log w.missed.memory
      (getenvMissLog_inside frame112)).trans ((CallerFrame.of_memory dcall.memory).trans
      ((CallerFrame.of_log dnull.memory (decomposeLog_inside frame32)).trans (CallerFrame.of_memory scall.memory))))
  have keptP : KeptImage atP :=
    w.table.kept.frame ((EmbedFrame.of_memory w.call.memory).trans ((EmbedFrame.stack w.missed.memory
      (getenvMissLog_inside frame112) (by decide)).trans ((EmbedFrame.of_memory dcall.memory).trans
      ((EmbedFrame.stack dnull.memory (decomposeLog_inside frame32) (by decide)).trans
        (EmbedFrame.of_memory scall.memory)))))
  have frameP : NativeFrame searchStack (176 + (48 + allocHeadroom)) := by constructor <;> decide
  have credits : startupAllocatorCredits - 448 = (startupAllocatorCredits - 464) + 16 := by decide
  have readyP16 : RuntimeReady (((vsaReg w.table.returned.allocation.allocation.allocated 10).toNat,
      (extTableRequest 8#64).toNat) :: w.table.H) ((startupAllocatorCredits - 464) + 16) searchStack
      jal_80025574_call.link atP := by
    rw [← credits]; exact readyP
  have empty : LPins4 atP.σ.mem searchStack.toNat (List.replicate 4 0#8) := by
    have zero (i : Nat) (hi : i < 4) : (atP.σ.mem[searchStack.toNat + i]?).getD 0 = 0#8 :=
      (callerP.byte _ (Nat.le_add_right _ _)).trans
        (w.table.returned.size_byte (by constructor <;> decide)
          (ExtTableSite.at_sp ((show NativeFrame searchStack 560 by constructor <;> decide).resize (by decide)
            (by decide)) (by decide)) i hi)
    exact ⟨zero 0 (by decide), zero 1 (by decide), zero 2 (by decide), zero 3 (by decide)⟩
  obtain ⟨atF, run4, ⟨found⟩⟩ := (search_in_path_plain atP _ (startupAllocatorCredits - 464) 16 searchStack
    jal_80025574_call.link argv0Ptr 0#64 (vsaReg w.source 18) (vsaReg w.source 19) searchStack argv0Ptr 8 readyP16
    frameP
    ⟨gholds_lookup (n := 8) _ scall.regs (by rfl), gholds_lookup (n := 9) _ scall.regs (by rfl),
      toP 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ dnull.regs (by rfl)),
      toP 19 _ (by decide) (by decide) (by decide)
        (carried 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ w.missed.regs (by rfl))),
      gholds_lookup (n := 10) _ scall.regs (by rfl), gholds_lookup (n := 11) _ scall.regs (by rfl), trivial⟩
    (argv0_plain keptP.embed)
    (fun k hk => Or.inr (Or.inl ⟨by unfold argv0Ptr; simp only [BitVec.toNat_ofNat]; decide +revert, by
      unfold argv0Ptr; simp only [BitVec.toNat_ofNat]; decide +revert⟩))
    (fun k hk => Or.inl (by unfold argv0Ptr; simp only [BitVec.toNat_ofNat]; decide +revert))
    (by decide) (by constructor <;> decide) (Nat.le_refl _) empty (by decide) ⟨by decide, by decide⟩).run atP
    ⟨scall.pc, rfl⟩
  -- s0 = the copy; caml_stat_free(tofree = NULL)
  have readyF := found.ready
  obtain ⟨atFree, run5, fcall⟩ := (search_exe_free_tofree atF _ found.copy 0#64 readyF.toLeafInput
    ⟨found.result, found.saved1, trivial⟩).run atF ⟨found.pc, rfl⟩
  have readyFree := readyF.stack_log fcall (by decide) (by simp only [keysG]; decide) (by decide)
    ((fcall.frame .x2 (by decide) (by decide)).trans found.stack) (gholds_lookup (n := 1) _ fcall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  obtain ⟨atT, run6, freedNull⟩ := (stat_free_null atFree _ readyFree.toLeafInput
    ⟨gholds_lookup (n := 10) _ fcall.regs (by rfl), trivial⟩ readyFree.poolZero).run atFree ⟨fcall.pc, rfl⟩
  have readyT := readyFree.effect freedNull (by decide) (by simp only [keysG]; decide) (by decide)
    ((freedNull.frame .x2 (by decide) (by decide)).trans readyFree.stack)
    (gholds_lookup (n := 1) _ freedNull.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  -- caml_ext_table_free(&path, 0)
  obtain ⟨atE, run7, tcall⟩ := (search_exe_free_table atT _ searchStack readyT.toLeafInput
    ⟨readyT.stack, trivial⟩).run atT ⟨freedNull.pc, rfl⟩
  have readyE := readyT.stack_log tcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ tcall.regs (by rfl)) (gholds_lookup (n := 1) _ tcall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  have toE (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [10, 11] ++ [1] ∧ n ∉ [15, 14, 11, 10] ∧ n ∉ [8, 10] ++ [1])
      (hv : gprGet atF.σ n = some v) : gprGet atE.σ n = some v :=
    (tcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans
      ((freedNull.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2.1).trans
        ((fcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2.2).trans hv))
  have callerF : CallerFrame searchStack atP atF :=
    ⟨fun a bound => found.kept a (Or.inl (Nat.le_trans (by decide) bound)) (Or.inr bound)⟩
  have callerE : CallerFrame searchStack w.source atE :=
    callerP.trans (callerF.trans ((CallerFrame.of_memory fcall.memory).trans
      ((CallerFrame.of_memory freedNull.memory).trans (CallerFrame.of_memory tcall.memory))))
  have contentsE : bytesT atE.σ.mem (searchStack + 8#64).toNat 8 =
      vsaReg w.table.returned.allocation.allocation.allocated 10 := by
    rw [show (searchStack + 8#64).toNat = searchStack.toNat + Layout.off_ext_table_contents from by decide,
      word_observed _ (fun i _ => callerE.byte _ (by omega))]
    exact w.table.returned.contents_word
  have bounds := readyE.block_bounds (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨atR, run8, ⟨tableFreed⟩⟩ := (ext_table_free_empty atE _ _ _ _ searchStack _ 0#64 searchStack
    (readyE.perm (List.Perm.swap _ _ _)) (by constructor <;> decide)
    (ExtTableSite.at_sp (by constructor <;> decide) (by decide)) (Nat.le_refl _)
    ⟨gholds_lookup (n := 2) _ tcall.regs (by rfl),
      toE 9 _ (by decide) (by decide) (by decide) found.saved1,
      gholds_lookup (n := 1) _ tcall.regs (by rfl), gholds_lookup (n := 10) _ tcall.regs (by rfl),
      gholds_lookup (n := 11) _ tcall.regs (by rfl), trivial⟩
    (by constructor <;> decide) contentsE bounds.1 bounds.2).run atE ⟨tcall.pc, rfl⟩
  -- the saved slots of caml_search_exe_in_path survive every call
  have searchFrame : NativeFrame attemptStack 48 := by constructor <;> decide
  have base : nativeFrameBase attemptStack 48 = searchStack.toNat := by decide
  have slotWord (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ searchExeSlots jal_800048ec_call.link trailSlot
        (BitVec.ofNat 64 WhileMinImage.argvArray)) :
      bytesT atR.σ.mem (nativeFrameBase attemptStack 48 + off) 8 = value := by
    have range : 24 ≤ off ∧ off + 8 ≤ 48 := by
      simp only [searchExeSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
    rw [word_observed (m := w.table.atTable.σ.mem) _ (fun i _ => by
      rw [tableFreed.byte (by constructor <;> decide) (by decide) (Nat.le_refl _) bounds.1 bounds.2
          (Or.inl (by rw [base]; omega)),
        callerE.byte _ (by rw [base]; omega),
        w.table.returned.above (by constructor <;> decide) (by rw [base]; omega)
          (by rw [base]; unfold Layout.ext_table_bytes; omega)]),
      w.table.search.memory]
    apply searchFrame.word_log_read
    · intro k v hk
      simp only [searchExeSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp [searchExeSlots]
    · exact member
  have copyE : gprGet atE.σ 8 = some found.copy :=
    (tcall.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans
      ((freedNull.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 8) _ fcall.regs (by rfl)))
  obtain ⟨atRet, run9, returned⟩ := (search_exe_return atR attemptStack jal_800048ec_call.link trailSlot
    (BitVec.ofNat 64 WhileMinImage.argvArray) found.copy _ tableFreed.ready.toLeafInput searchFrame
    ⟨tableFreed.ready.stack, (tableFreed.saved_gpr (k := 8) (by decide)).trans copyE, trivial⟩
    (slotWord 40 _ (by simp [searchExeSlots])) (slotWord 32 _ (by simp [searchExeSlots]))
    (slotWord 24 _ (by simp [searchExeSlots])) (by decide)).run atR
    ⟨library_pc tableFreed.freed.free.good tableFreed.freed.free.result.frame.pc, rfl⟩
  have readyRet := tableFreed.ready.stack_log returned (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ returned.regs (by rfl)) (gholds_lookup (n := 1) _ returned.regs (by rfl))
    (by decide) searchFrame (by simp only [LogInW])
  have sameRet : atRet.σ.mem = atR.σ.mem := returned.memory
  have sameE : atE.σ.mem = atF.σ.mem :=
    (show atE.σ.mem = atT.σ.mem from tcall.memory).trans
      ((show atT.σ.mem = atFree.σ.mem from freedNull.memory).trans fcall.memory)
  have frameFree : NativeFrame searchStack (32 + allocHeadroom) := by constructor <;> decide
  -- the callee-saved registers of caml_attempt_open
  have toR (n : Nat) (member : n ∈ [18, 19]) (v : BitVec 64) (hv : gprGet atF.σ n = some v) :
      gprGet atRet.σ n = some v := by
    have range : 1 ≤ n ∧ n ≤ 31 := by simp at member; omega
    have unwritten : n ∉ [1, 10, 8, 9, 2] := by simp at member ⊢; omega
    exact (returned.toEffectPost.gpr_frame (by decide) n range.1 range.2 unwritten).trans
      ((tableFreed.saved_gpr (k := n) (by simp at member ⊢; omega)).trans
        (toE n v range.1 range.2 (by simp at member ⊢; omega) hv))
  have callerA : CallerFrame attemptStack w.table.atSaved atRet := by
    constructor
    intro a bound
    have above : searchStack.toNat + 48 ≤ a := by
      have : searchStack.toNat + 48 = attemptStack.toNat := by decide
      omega
    rw [sameRet, tableFreed.byte (by constructor <;> decide) (by decide) (Nat.le_refl _) bounds.1 bounds.2
        (Or.inl (by omega)),
      callerE.byte _ (by omega),
      w.table.returned.above (by constructor <;> decide) (by omega) (by unfold Layout.ext_table_bytes; omega),
      w.table.search.memory, frameOn_writeLog _ _ _ (searchExeLog_inside searchFrame) a ⟨Or.inr bound, trivial⟩,
      w.table.name.memory]
    rfl
  refine ⟨initial, atRet, ⟨atD, w, found.copy, gholds_lookup (n := 10) _ returned.regs (by rfl), returned.pc,
    gholds_lookup (n := 2) _ returned.regs (by rfl), gholds_lookup (n := 8) _ returned.regs (by rfl),
    gholds_lookup (n := 9) _ returned.regs (by rfl), toR 18 (by decide) _ found.saved2,
    toR 19 (by decide) _ found.saved3, readyRet, found.fresh, ?_, ?_,
    w.run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (run8.trans run9)))))))), found.aligned, callerA⟩⟩
  · intro k hk
    have inside : InExt (found.copy.toNat, 8 + 1) (found.copy.toNat + k) := ⟨by omega, by omega⟩
    rw [sameRet, tableFreed.live_byte frameFree (Nat.le_refl _) (List.mem_cons_self ..) inside
      (found.disjoint _ (List.mem_cons_self ..) _ inside) ⟨by have := found.fresh.1; omega,
        by have := found.fresh.2; omega⟩, sameE, found.bytes k hk]
    exact argv0_byte keptP.embed k hk
  · apply keptP.frame
    have strdup : EmbedFrame atP atF :=
      ⟨fun a ha => found.kept a (ha.strdup_kept (by decide))
        (Or.inl (by
          have := ha.lt
          have limit : embedLimit < nativeFrameBase searchStack 176 := by decide
          omega))⟩
    exact strdup.trans ((EmbedFrame.of_memory sameE).trans ((tableFreed.embed_frame frameFree (by decide)
      (Nat.le_refl _) bounds.1 bounds.2).trans (EmbedFrame.of_memory sameRet)))
end OCaml.Vm.Boot.WhileMinElfParse
