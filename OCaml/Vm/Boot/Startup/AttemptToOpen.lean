import OCaml.Vm.Boot.Startup.AttemptSearch
import OCaml.Vm.Boot.Startup.AttemptOpenCalls
import OCaml.Vm.Boot.Startup.GcMessageQuiet
import OCaml.Vm.Boot.Startup.StatFree
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

theorem SearchName.cbytes {m : Vsa.MemRepr.Mem} {p : BitVec 64} {len : Nat} (h : SearchName m p len) :
    CBytes m p.toNat len := by
  rcases h with plain | rooted
  · exact plain.bytes
  · exact rooted.bytes

/-- caml_attempt_open at `open(truename, O_RDONLY)`: the duplicated name, the
quiet opening message and its free are behind it. -/
structure AttemptAtOpen (H : List (Nat × Nat)) (capacity : Nat) (ra s0 s1 s2 s3 s4 flag name : BitVec 64)
    (len : Nat) (before after : Config) where
  copy : BitVec 64
  pc : PCAt 0x80042590#64 after
  link : gprGet after.σ 1 = some jal_80004920_call.link
  path : gprGet after.σ 10 = some copy
  flags : gprGet after.σ 11 = some 0#64
  stack : gprGet after.σ 2 = some attemptStack
  truename : gprGet after.σ 18 = some copy
  trail : gprGet after.σ 8 = some trailSlot
  slot : gprGet after.σ 19 = some exeNameSlot
  flagReg : gprGet after.σ 20 = some flag
  upper : ∀ k, 21 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  ready : RuntimeReady ((copy.toNat, len + 1) :: H) capacity attemptStack jal_80004920_call.link after
  fresh : heapStart ≤ copy.toNat ∧ copy.toNat + (len + 1) ≤ heapEnd
  aligned : copy.toNat % 16 = 0
  bytes : ∀ k, k ≤ len → (after.σ.mem[copy.toNat + k]?).getD 0 = (WhileMinImage.initialMem[name.toNat + k]?).getD 0
  slots : ∀ off value, (off, value) ∈ attemptOpenSlots ra s0 s1 s2 s3 s4 →
    bytesT after.σ.mem (nativeFrameBase parameterStack 64 + off) 8 = value
  caller : CallerFrame parameterStack before after
  late : LateImage after
  run : Steps before after

theorem attempt_open_to_open {c s : Config} {H : List (Nat × Nat)} {capacity charge : Nat}
    {ra s0 s1 s2 s3 s4 flag name : BitVec 64} {len : Nat}
    (S : AttemptSearched H (capacity + charge) ra s0 s1 s2 s3 s4 flag name len c s)
    (embedded : ∀ k, k ≤ len → EmbedByte (name.toNat + k))
    (kind : ∀ d : Config, EmbedImage d → SearchName d.σ.mem name len)
    (small : len ≤ 64) (charged : vsaChg (len + 1) charge) :
    ∃ after, Steps s after ∧ Nonempty (AttemptAtOpen H capacity ra s0 s1 s2 s3 s4 flag name len c after) := by
  have frameS : NativeFrame attemptStack (48 + allocHeadroom) := by constructor <;> decide
  have copyName (k : Nat) (hk : k ≤ len) :
      (s.σ.mem[S.copy.toNat + k]?).getD 0 = (s.σ.mem[name.toNat + k]?).getD 0 := by
    rw [S.bytes k hk, S.late.embed.byte _ (embedded k hk)]
  have copyBytes : CBytes s.σ.mem S.copy.toNat len := by
    have nameB := (kind s S.late.embed).cbytes
    exact {
      nz := fun i hi => by
        change (s.σ.mem[_]?).getD 0 ≠ 0
        rw [copyName i (by omega)]
        exact nameB.nz i hi
      nul := by
        change (s.σ.mem[_]?).getD 0 = 0
        rw [copyName len (Nat.le_refl _)]
        exact nameB.nul
      lo := by have := S.fresh.1; unfold heapStart at this; omega
      hi := by have := S.fresh.2; unfold heapEnd at this; omega
      htif := Or.inr (by have := S.fresh.1; unfold heapStart at this; omega) }
  -- caml_stat_strdup(truename)
  obtain ⟨atDup, run1, dcall⟩ := (attempt_open_strdup s _ attemptStack S.copy S.ready.toLeafInput
    ⟨S.result, S.stack, trivial⟩).run s ⟨S.pc, rfl⟩
  have readyDup := S.ready.stack_log dcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dcall.regs (by rfl)) (gholds_lookup (n := 1) _ dcall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  have sameDup : atDup.σ.mem = s.σ.mem := dcall.memory
  have toDup (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [18] ++ [1])
      (hv : gprGet s.σ n = some v) : gprGet atDup.σ n = some v :=
    (dcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  obtain ⟨atMsg, run2, ⟨D⟩⟩ := (strdup_full atDup _ capacity charge attemptStack
    jal_800048f4_call.link trailSlot (gprGet atDup.σ 9 |>.getD 0) S.copy len readyDup frameS
    ⟨by rw [gpr_of_ready readyDup 9 (by decide) (by decide)]; rfl,
      toDup 8 _ (by decide) (by decide) (by decide) S.trail,
      gholds_lookup (n := 10) _ dcall.regs (by rfl), trivial⟩
    (by rw [sameDup]; exact copyBytes)
    (fun k hk => Or.inr (Or.inr (Or.inr ⟨S.copy.toNat, len + 1, List.mem_cons_self .., S.fresh.1, S.fresh.2,
      by omega, by omega⟩)))
    (Or.inr (by have := S.fresh.1; unfold heapStart at this; unfold Layout.sym_tohost; omega)) (by omega)
    charged).run atDup ⟨dcall.pc, rfl⟩
  have lateMsg : LateImage atMsg :=
    S.late.frame ((EmbedFrame.of_memory sameDup).trans ⟨fun a ha => D.kept a (ha.strdup_kept (by decide))⟩)
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
    (lateMsg.frame (EmbedFrame.of_memory mcall.memory)).verbGc).run atGc ⟨mcall.pc, rfl⟩
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
  obtain ⟨atOpen, run6, ⟨freed⟩⟩ := (stat_free_block atStat _ D.copy (len + 1) capacity
    attemptStack jal_80004914_call.link readyStat (gholds_lookup (n := 10) _ fcall.regs (by rfl))
    (frameS.resize (by decide) (by decide)) D.fresh.1 D.fresh.2).run atStat ⟨fcall.pc, rfl⟩
  -- registers from the search's return to the open call
  have keepAll (n : Nat) (member : n ∈ abiSaved) (n9 : n ≠ 9) (n18 : n ≠ 18) (v : BitVec 64)
      (hv : gprGet s.σ n = some v) : gprGet atOpen.σ n = some v := by
    have range : 1 ≤ n ∧ n ≤ 31 := by simp [abiSaved] at member; omega
    have atMsgN : gprGet atMsg.σ n = some v := by
      by_cases n8 : n = 8
      · subst n8; rw [D.saved0]; exact congrArg some (Option.some.inj
          ((toDup 8 _ (by decide) (by decide) (by decide) S.trail).symm.trans
            (toDup 8 _ (by decide) (by decide) (by decide) hv)))
      · by_cases n19 : n = 19
        · subst n19; rw [D.saved23 19 (by decide)]; exact toDup 19 v (by decide) (by decide) (by decide) hv
        · rw [D.upper n (by simp [abiSaved] at member; omega) (by simp [abiSaved] at member; omega)]
          exact toDup n v range.1 range.2 (by simp [abiSaved] at member ⊢; omega) hv
    exact (freed.saved_gpr member).trans
      ((fcall.toEffectPost.gpr_frame (by decide) n range.1 range.2 (by simp [abiSaved] at member ⊢; omega)).trans
        ((gc.toEffectPost.gpr_frame (by decide) n range.1 range.2 (by simp [abiSaved] at member ⊢; omega)).trans
          ((mcall.toEffectPost.gpr_frame (by decide) n range.1 range.2 (by simp [abiSaved] at member ⊢; omega)).trans atMsgN)))
  have truenameO : gprGet atOpen.σ 18 = some S.copy :=
    (freed.saved_gpr (k := 18) (by decide)).trans
      ((fcall.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
        ((gc.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
          ((mcall.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
            ((D.saved23 18 (by decide)).trans (gholds_lookup (n := 18) _ dcall.regs (by rfl))))))
  obtain ⟨atCall, run7, ocall⟩ := (attempt_open_open atOpen _ attemptStack S.copy freed.ready.toLeafInput
    ⟨truenameO, freed.ready.stack, trivial⟩).run atOpen
    ⟨library_pc freed.free.good freed.free.result.frame.pc, rfl⟩
  have readyCall := freed.ready.stack_log ocall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ ocall.regs (by rfl)) (gholds_lookup (n := 1) _ ocall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  have frameA : NativeFrame attemptStack allocHeadroom := frameS.resize (by decide) (by decide)
  have keepCall (n : Nat) (member : n ∈ abiSaved) (n9 : n ≠ 9) (n18 : n ≠ 18) (v : BitVec 64)
      (hv : gprGet s.σ n = some v) : gprGet atCall.σ n = some v :=
    (ocall.toEffectPost.gpr_frame (by decide) n (by simp [abiSaved] at member; omega)
      (by simp [abiSaved] at member; omega) (by simp [abiSaved] at member ⊢; omega)).trans
      (keepAll n member n9 n18 v hv)
  -- memory: caml_attempt_open's frame and the copy's bytes
  have tail : CallerFrame attemptStack s atCall := by
    refine ⟨fun a bound => ?_⟩
    rw [show atCall.σ.mem = atOpen.σ.mem from ocall.memory,
      freed.byte frameA (by decide) D.fresh.1 D.fresh.2 (Or.inl bound),
      show atStat.σ.mem = atFree.σ.mem from fcall.memory, gc.memory,
      frameOn_writeLog _ _ _ (gcMessageLog_inside frameGc) _ ⟨Or.inr bound, trivial⟩,
      show atGc.σ.mem = atMsg.σ.mem from mcall.memory, D.kept a (Or.inl bound), sameDup]
  have upperS (k : Nat) (lo : 21 ≤ k) (hi : k ≤ 27) : gprGet atCall.σ k = gprGet c.σ k := by
    rw [← S.upper k lo hi, gpr_of_ready S.ready k (by omega) (by omega)]
    exact keepCall k (by simp [abiSaved]; omega) (by omega) (by omega) _
      (gpr_of_ready S.ready k (by omega) (by omega))
  refine ⟨atCall, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), ⟨{
      copy := S.copy
      pc := ocall.pc
      link := gholds_lookup (n := 1) _ ocall.regs (by rfl)
      path := gholds_lookup (n := 10) _ ocall.regs (by rfl)
      flags := gholds_lookup (n := 11) _ ocall.regs (by rfl)
      stack := gholds_lookup (n := 2) _ ocall.regs (by rfl)
      truename := gholds_lookup (n := 18) _ ocall.regs (by rfl)
      trail := keepCall 8 (by decide) (by decide) (by decide) _ S.trail
      slot := keepCall 19 (by decide) (by decide) (by decide) _ S.slot
      flagReg := keepCall 20 (by decide) (by decide) (by decide) _ S.flagReg
      upper := upperS
      ready := readyCall
      fresh := S.fresh
      aligned := S.aligned
      bytes := fun k hk => by
        have inside : InExt (S.copy.toNat, len + 1) (S.copy.toNat + k) := ⟨by omega, by omega⟩
        have apart : ¬ InExt (D.copy.toNat, len + 1) (S.copy.toNat + k) := fun copy2 =>
          D.disjoint _ (List.mem_cons_self ..) _ copy2 inside
        have arena : heapStart ≤ S.copy.toNat + k ∧ S.copy.toNat + k < heapEnd :=
          ⟨by have := S.fresh.1; omega, by have := S.fresh.2; omega⟩
        have lower : heapEnd ≤ nativeFrameBase attemptStack 80 := by decide
        rw [show atCall.σ.mem = atOpen.σ.mem from ocall.memory,
          freed.live_byte frameA (List.mem_cons_self ..) inside apart arena,
          show atStat.σ.mem = atFree.σ.mem from fcall.memory, gc.memory,
          frameOn_writeLog _ _ _ (gcMessageLog_inside frameGc) _ ⟨Or.inl (by dsimp only; omega), trivial⟩,
          show atGc.σ.mem = atMsg.σ.mem from mcall.memory,
          D.kept _ (Or.inr (Or.inr (Or.inr ⟨S.copy.toNat, len + 1, List.mem_cons_self .., S.fresh.1, S.fresh.2,
            by omega, by omega⟩))), sameDup]
        exact S.bytes k hk
      slots := fun off value member => by
        have base64 : nativeFrameBase parameterStack 64 = attemptStack.toNat := by decide
        have range : 16 ≤ off := by
          simp only [attemptOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
          omega
        rw [word_observed (m := s.σ.mem) _ (fun i _ => tail.byte _ (by rw [base64] at *; omega))]
        exact S.slots off value member
      caller := S.caller.trans (tail.mono (by decide))
      late := (lateMsg.frame (EmbedFrame.of_memory mcall.memory)).frame
        ((EmbedFrame.stack gc.memory (gcMessageLog_inside frameGc) (by decide)).trans
          ((EmbedFrame.of_memory fcall.memory).trans ((freed.embed_frame frameA (by decide) D.fresh.1 D.fresh.2).trans
            (EmbedFrame.of_memory ocall.memory))))
      run := S.run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))) }⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
