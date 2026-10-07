import OCaml.Vm.Gc.ReallocSuffix

/-!
# `caml_realloc_ref_table` on an unallocated table

The whole callee from its entry with `base == NULL` to its `ret`
(`realloc_run`): the prefix up to `caml_stat_alloc_noexc`, the install,
threshold/limit and end chains with their `__muldi3` calls, and the return.
The post (`Done`) names the fresh block `p`, readiness for the extended
live-block list, the restored callee-saved registers and all seven table
fields.
-/

namespace OCaml.Vm.Gc.Realloc
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris VsaIris.VsaHeap
  VsaIris.Inst LeanRV64DExecutable

/-- The allocation keeps the code bytes below the arena. -/
theorem alloc_lowKept {H capacity n sp ra before after} (w : StatAllocated H capacity n sp ra before after)
    (frame : NativeFrame sp allocHeadroom) : LowKept before.σ.mem after.σ.mem := by
  intro a live below notGlobal
  have unchanged := w.allocation.memory a (by
    intro owned
    rcases owned with scratch | foot
    · unfold stackWin InExt at scratch
      have := frame.lower
      simp only [heapStart, heapEnd, allocHeadroom] at *
      omega
    · rcases foot with g | ⟨h, _, _⟩
      · exact notGlobal g
      · have lo : vsaLayoutP.lo = heapStart := rfl
        omega)
  change (after.σ.mem[a]?).getD 0 = (w.atMalloc.σ.mem[a]?).getD 0 at unchanged
  rw [w.dispatch.memory] at unchanged
  have pa : (after.σ.mem[a]?).isSome := w.allocation.good.live a live
  have pb : (before.σ.mem[a]?).isSome := by
    have h := w.platform.live a live
    rwa [w.dispatch.memory] at h
  revert unchanged pa pb
  cases after.σ.mem[a]? <;> cases before.σ.mem[a]? <;> simp_all

theorem installLog_inside {sp tbl p : BitVec 64} (high : tbl.toNat + tableBytes ≤ heapEnd) :
    LogInW (windows sp tbl) (installLog tbl p) := by
  simp only [installLog, LogInW, windows, InsideW, field_nat high 0 (by decide), field_nat high 24 (by decide),
    tableBytes]
  refine ⟨?_, ?_, trivial⟩ <;> right <;> left <;> omega

theorem limitLog_inside {sp tbl v : BitVec 64} (high : tbl.toNat + tableBytes ≤ heapEnd) :
    LogInW (windows sp tbl) (limitLog tbl v) := by
  simp only [limitLog, LogInW, windows, InsideW, field_nat high 16 (by decide), field_nat high 32 (by decide),
    tableBytes]
  refine ⟨?_, ?_, trivial⟩ <;> right <;> left <;> omega

/-- The allocation keeps the callee-saved registers it never touches. -/
theorem stat_rest_gpr {H capacity n sp ra before after k}
    (w : StatAllocated H capacity n sp ra before after) (member : k ∈ calleeRest) :
    gprGet after.σ k = gprGet before.σ k := by
  have range : 1 ≤ k ∧ k ≤ 31 ∧ k ≠ 15 := by simp [calleeRest] at member; omega
  have notin : ∀ k ∈ calleeRest, k ∉ VsaIris.Sym.aRegs := by decide
  have mid : gprGet w.atMalloc.σ k = gprGet before.σ k := by
    apply gprGet_of_frame k range.1 range.2.1 (gpr_avoids_noise k (by omega) range.1)
    · intro m hm
      have hm15 : m = 15 := List.mem_singleton.1 hm
      subst hm15
      exact gprReg_beq_false 15 (by decide) k (by omega) (by decide) range.1 (fun e => range.2.2 e.symm)
    · intro r noise outside
      exact w.dispatch.frame r (fun m hm => by
        have ne := outside m hm
        exact fun e => by rw [e, beq_self_eq_true] at ne; contradiction) noise
  exact (library_register_frame w.platform w.allocation.good range.1 range.2.1
    (w.allocation.registers k (notin k member))).trans mid

/-- Bytes the callee never writes: its caller's stack, low memory outside
malloc's globals, and every live block but the table. -/
def Kept (H : List (Nat × Nat)) (sp tbl : BitVec 64) (a : Nat) : Prop :=
  sp.toNat ≤ a ∨ (a < heapStart ∧ ¬ allocGlobal a) ∨
    (∃ q n, (q, n) ∈ H ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ a ∧ a < q + n ∧
      (a < tbl.toNat ∨ tbl.toNat + tableBytes ≤ a))

theorem outWRange_one {ws : List W} {a : Nat} (h : OutW ws a) : OutWRange ws a 1 := by
  induction ws with
  | nil => trivial
  | cons w ws ih => exact ⟨by rcases h.1 with h | h <;> omega, ih h.2⟩

theorem outL_of_windows {ws : List W} {log : List WEntry} {a : Nat} (inside : LogInW ws log) (out : OutW ws a) :
    OutL log a :=
  outL_of_range (n := 1) (OCaml.Vm.Sim.outLRange_of_windows inside (outWRange_one out)) (Nat.le_refl a)
    (Nat.lt_succ_self a)

/-- A kept byte misses the callee's frame and the table. -/
theorem Kept.out_windows {H sp tbl a} (k : Kept H sp tbl a) (frame : NativeFrame sp (64 + allocHeadroom))
    (tLow : heapStart ≤ tbl.toNat) (tHigh : tbl.toNat + tableBytes ≤ heapEnd) :
    OutW (windows sp tbl) a := by
  have lower := frame.lower
  unfold Kept at k
  simp only [windows, OutW, heapStart, heapEnd, allocHeadroom, tableBytes] at *
  rcases k with h | ⟨h, -⟩ | ⟨q, n, -, hq, hn, ha, hb, ht⟩ <;> refine ⟨?_, ?_, trivial⟩ <;> omega

/-- A kept byte is outside the allocation's footprint. -/
theorem Kept.not_mS {H sp tbl a} (k : Kept H sp tbl a) (frame : NativeFrame sp (64 + allocHeadroom)) :
    ¬ mS H (sp + -64#64) a := by
  have lower := frame.lower
  have base : (sp + -64#64).toNat = sp.toNat - 64 := (frame.resize (small := 64) (by decide) (by decide)).stack_nat
  unfold Kept at k
  change ¬ (stackWin (sp + -64#64) allocHeadroom a ∨ vsaFoot H a)
  rintro (scratch | foot)
  · unfold stackWin InExt at scratch
    rw [base] at scratch
    simp only [heapStart, heapEnd, allocHeadroom] at *
    rcases k with h | ⟨h, -⟩ | ⟨q, n, -, hq, hn, ha, hb, -⟩ <;> omega
  · rcases k with h | ⟨h, g⟩ | ⟨q, n, member, hq, hn, ha, hb, -⟩
    · have := allocator_foot_below foot
      simp only [heapEnd, allocHeadroom] at *; omega
    · rcases foot with g' | ⟨h', _, _⟩
      · exact g g'
      · omega
    · rcases allocator_payload_outside member hq foot with h | h <;> omega

/-- The callee's result: the fresh table storage `p` and the filled table. -/
structure Done (H : List (Nat × Nat)) (capacity : Nat) (sp ra tbl s0 s1 s2 s3 wsz : BitVec 64)
    (before after : Config) where
  p : BitVec 64
  ready : RuntimeReady ((p.toNat, (request wsz).toNat) :: H) capacity sp ra after
  pc : after.σ.regs.get? Register.PC = some ra
  saved : GHolds after.σ [(8, s0), (9, s1), (18, s2), (19, s3)]
  nonzero : p.toNat ≠ 0
  low : heapStart ≤ p.toNat
  high : p.toNat + (request wsz).toNat ≤ heapEnd
  aligned : p.toNat % 16 = 0
  disjoint : ∀ e ∈ H, ∀ a, InExt (p.toNat, (request wsz).toNat) a → ¬ InExt e a
  base : bytesT after.σ.mem tbl.toNat 8 = p
  endField : bytesT after.σ.mem (tbl.toNat + 8) 8 = p + (size wsz + 0x100#64) * 0x8#64
  threshold : bytesT after.σ.mem (tbl.toNat + 16) 8 = p + 0x8#64 * size wsz
  ptr : bytesT after.σ.mem (tbl.toNat + 24) 8 = p
  limit : bytesT after.σ.mem (tbl.toNat + 32) 8 = p + 0x8#64 * size wsz
  size : bytesT after.σ.mem (tbl.toNat + 40) 8 = size wsz
  reserve : bytesT after.σ.mem (tbl.toNat + 48) 8 = 0x100#64
  kept : ∀ a, Kept H sp tbl a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  callee : ∀ k ∈ calleeRest, gprGet after.σ k = gprGet before.σ k
  out : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- **`caml_realloc_ref_table` on an unallocated table**, entry to return. -/
theorem realloc_run {H capacity charge sp ra tbl s0 s1 s2 s3 wsz} {c : Config}
    (e : Entry H capacity charge sp ra tbl s0 s1 s2 s3 wsz c) :
    FnSummary ReallocEntry.pc (fun d => d = c)
      (fun after => Nonempty (Done H capacity sp ra tbl s0 s1 s2 s3 wsz c after)) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have f64 : NativeFrame sp 64 := e.frame.resize (by decide) (by decide)
  have frameA : NativeFrame (sp + -64#64) allocHeadroom := e.frame.nested (front := 64) (by decide)
  obtain ⟨tLow, tHigh⟩ := e.ready.block_bounds e.table
  -- the prefix, through caml_stat_alloc_noexc
  obtain ⟨c4, run4, ⟨A⟩⟩ := (prefix_run e).run d ⟨pc, rfl⟩
  have S := A.stat
  obtain ⟨pNonzero, pLow, pHigh, pDisjoint⟩ := S.allocation.result.fresh.destruct
  change (vsaReg c4 10).toNat ≠ 0 at pNonzero
  change heapStart ≤ (vsaReg c4 10).toNat at pLow
  change (vsaReg c4 10).toNat + (request wsz).toNat ≤ heapEnd at pHigh
  have pReg : gprGet c4.σ 10 = some (vsaReg c4 10) := library_gpr S.ready.platform (by decide) (by decide) rfl
  have codeAt : Code.Realloc_generic_table_isra_0Loaded A.atAlloc.σ.mem := by
    rw [A.memory]; exact genCode_keep e.genCode (lowKept_windows f64 tLow (entryLog_inside f64 tHigh))
  have after : AfterAlloc ((((vsaReg c4 10).toNat, (request wsz).toNat)) :: H) capacity sp tbl s0 s1 s2 s3 ra wsz
      (vsaReg c4 10) c4 :=
    { ready := S.ready, frame := e.frame, table := List.mem_cons_of_mem _ e.table, tableAligned := e.tableAligned
      words := words_alloc S e.frame e.table tLow tHigh (by rw [A.memory]; exact words_entry e)
      result := pReg
      nonzero := fun h => pNonzero (by rw [h]; rfl)
      s0Reg := (S.saved_gpr (k := 8) (by decide)).trans A.s0Reg
      s3Reg := (S.saved_gpr (k := 19) (by decide)).trans A.s3Reg
      code := genCode_keep codeAt (alloc_lowKept S frameA) }
  -- base and ptr
  obtain ⟨c5, run5, I⟩ := (install_step after).run c4
    ⟨library_pc S.allocation.good S.allocation.result.frame.pc, rfl⟩
  have r5 := I.regs
  simp only [ReallocInstall.state3, GHolds] at r5
  obtain ⟨h10, h11, h18, h9, h8, h19, -⟩ := r5
  have code5 : Code.Realloc_generic_table_isra_0Loaded c5.σ.mem := by
    rw [I.memory]; exact genCode_keep after.code (lowKept_windows f64 tLow (installLog_inside tHigh))
  -- threshold product
  obtain ⟨c6, run6, M⟩ := (ready_muldi3 ReallocInstall.call_shape ReallocInstall.call_decode
    ReallocInstall.call_target (ReallocInstall.call_pins code5) I.ready h10 h11 (by decide)).run c5 ⟨I.pc, rfl⟩
  have keep6 (n : Nat) (h : n ∈ [8, 9, 18, 19]) : gprGet c6.σ n = gprGet c5.σ n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact M.frame n (by omega) (by omega) (by simp; omega)
  have before6 : BeforeLimit ((((vsaReg c4 10).toNat, (request wsz).toNat)) :: H) capacity sp tbl s0 s1 s2 s3 ra
      wsz (vsaReg c4 10) ReallocInstall.call.link c6 :=
    { ready := M.ready, frame := e.frame, table := List.mem_cons_of_mem _ e.table, tableAligned := e.tableAligned
      rest := by
        rw [M.memory, I.memory]
        apply after.words.rest.writeLog f64 tHigh
        intro x hx
        simp only [installLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;>
          simp only [field_nat tHigh 0 (by decide), field_nat tHigh 24 (by decide)] <;> omega
      s0Reg := (keep6 8 (by simp)).trans h8
      s1Reg := (keep6 9 (by simp)).trans h9
      result := M.result
      s3Reg := (keep6 19 (by simp)).trans h19
      s2Reg := (keep6 18 (by simp)).trans h18
      code := by rw [M.memory]; exact code5 }
  -- threshold and limit
  obtain ⟨c7, run7, L⟩ := (limit_step before6).run c6 ⟨M.pc, rfl⟩
  have r7 := L.regs
  simp only [ReallocLimit.state1, GHolds] at r7
  obtain ⟨l10, l11, -, -, l8, l9, -, -, -⟩ := r7
  have code7 : Code.Realloc_generic_table_isra_0Loaded c7.σ.mem := by
    rw [L.memory]; exact genCode_keep before6.code (lowKept_windows f64 tLow (limitLog_inside tHigh))
  -- end product
  obtain ⟨c8, run8, N⟩ := (ready_muldi3 ReallocLimit.call_shape ReallocLimit.call_decode
    ReallocLimit.call_target (ReallocLimit.call_pins code7) L.ready l10 l11 (by decide)).run c7 ⟨L.pc, rfl⟩
  have keep8 (n : Nat) (h : n ∈ [8, 9]) : gprGet c8.σ n = gprGet c7.σ n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact N.frame n (by omega) (by omega) (by simp; omega)
  have before8 : BeforeReturn ((((vsaReg c4 10).toNat, (request wsz).toNat)) :: H) capacity sp tbl s0 s1 s2 s3 ra
      wsz (vsaReg c4 10) ReallocLimit.call.link c8 :=
    { ready := N.ready, frame := e.frame, table := List.mem_cons_of_mem _ e.table, tableAligned := e.tableAligned
      rest := by
        rw [N.memory, L.memory]
        apply before6.rest.writeLog f64 tHigh
        intro x hx
        simp only [limitLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;>
          simp only [field_nat tHigh 16 (by decide), field_nat tHigh 32 (by decide)] <;> omega
      raAligned := e.ready.aligned
      s0Reg := (keep8 8 (by simp)).trans l8
      s1Reg := (keep8 9 (by simp)).trans l9
      result := N.result
      code := by rw [N.memory]; exact code7 }
  -- end, restore, return
  obtain ⟨c9, run9, R⟩ := (return_step before8).run c8 ⟨N.pc, rfl⟩
  have r9 := R.regs
  simp only [ReallocReturn.state1, GHolds] at r9
  obtain ⟨-, g19, g18, g9, g8, -, -⟩ := r9
  -- the table, read back through the three store logs
  have t0 := field_nat tHigh 0 (by decide)
  have t8 := field_nat tHigh 8 (by decide)
  have t16 := field_nat tHigh 16 (by decide)
  have t24 := field_nat tHigh 24 (by decide)
  have t32 := field_nat tHigh 32 (by decide)
  have tb : tbl.toNat + 56 ≤ heapEnd := tHigh
  have out {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} (x : Nat)
      (h : ∀ e ∈ log, x + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ x) : bytesT (writeLog m log) x 8 = bytesT m x 8 :=
    bytesT_writeLog_out _ (outLRange_of_forall h)
  have memory9 : c9.σ.mem = writeLog (writeLog (writeLog c4.σ.mem (installLog tbl (vsaReg c4 10)))
      (limitLog tbl (vsaReg c4 10 + 0x8#64 * size wsz)))
      (endLog tbl (vsaReg c4 10 + (size wsz + 0x100#64) * 0x8#64)) := by
    rw [R.memory, N.memory, L.memory, M.memory, I.memory]
  have rest9 := before8.rest.writeLog (log := endLog tbl (vsaReg c4 10 + (size wsz + 0x100#64) * 0x8#64))
    f64 tHigh (fun x hx => by
      simp only [endLog, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; simp only [t8]; omega)
  rw [← R.memory] at rest9
  have outEq : Vsa.Machine.output c9.σ = Vsa.Machine.output d.σ := by
    rw [R.out, show Vsa.Machine.output c8.σ = Vsa.Machine.output c7.σ by simp only [Vsa.Machine.output, N.output],
      L.out, show Vsa.Machine.output c6.σ = Vsa.Machine.output c5.σ by simp only [Vsa.Machine.output, M.output],
      I.out, A.out]
  refine ⟨c9, run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9)))), ⟨⟨vsaReg c4 10, R.ready, R.pc,
    ⟨g8, g9, g18, g19, trivial⟩, pNonzero, pLow, pHigh, S.allocation.result.align, pDisjoint, ?_, ?_, ?_, ?_, ?_, rest9.size, rest9.reserve,
    ?_, ?_, outEq⟩⟩⟩
  rotate_left 5
  · -- kept bytes
    intro a k
    have out := k.out_windows e.frame tLow tHigh
    have tableOut : ∀ x : WEntry, tbl.toNat ≤ x.1 → x.1 + x.2.1 ≤ tbl.toNat + 40 → OutL [x] a := by
      intro x lo hi
      refine ⟨?_, trivial⟩
      simp only [windows, OutW] at out
      have := e.frame.lower
      simp only [heapStart, heapEnd, allocHeadroom, tableBytes] at *
      omega
    have logOut : ∀ log : List WEntry, (∀ x ∈ log, tbl.toNat ≤ x.1 ∧ x.1 + x.2.1 ≤ tbl.toNat + 40) → OutL log a := by
      intro log h
      induction log with
      | nil => trivial
      | cons x rest ih =>
        have hx := h x List.mem_cons_self
        exact ⟨(tableOut x hx.1 hx.2).1, ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩
    have entryLogOut : OutL (entryLog sp tbl s0 s1 s2 s3 ra wsz) a := by
      have inside := entryLog_inside (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (ra := ra) (wsz := wsz) f64 tHigh
      exact outL_of_windows inside out
    rw [memory9, writeLog_out _ _ _ (logOut _ ?_), writeLog_out _ _ _ (logOut _ ?_), writeLog_out _ _ _ (logOut _ ?_)]
    · have alloc := S.allocation.memory a (k.not_mS e.frame)
      change (c4.σ.mem[a]?).getD 0 = (S.atMalloc.σ.mem[a]?).getD 0 at alloc
      rw [alloc, S.dispatch.memory, A.memory, writeLog_out _ _ _ entryLogOut]
    all_goals
      intro x hx
      simp only [installLog, limitLog, endLog, List.mem_cons, List.not_mem_nil, or_false] at hx
      first
        | (rcases hx with rfl | rfl <;> simp only [t0, t8, t16, t24, t32] <;> omega)
        | (subst hx; simp only [t0, t8, t16, t24, t32]; omega)
  · -- callee-saved registers
    intro k hk
    have b := calleeRest_bounds k hk
    have out : ∀ k ∈ calleeRest, k ∉ [1, 10, 11, 12, 13] := by decide
    exact (R.callee k hk).trans ((N.frame k b.1 b.2 (out k hk)).trans ((L.callee k hk).trans
      ((M.frame k b.1 b.2 (out k hk)).trans ((I.callee k hk).trans ((stat_rest_gpr S hk).trans (A.callee k hk))))))
  · -- base
    rw [memory9, out _ (fun x hx => by
        simp only [endLog, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp only [t8]; omega),
      out _ (fun x hx => by
        simp only [limitLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp only [t16, t32] <;> omega)]
    apply word_writeLog_at _ _ 0 _ _ (by simp only [installLog, t0]; rfl)
    apply outLRange_of_forall
    intro x hx
    simp only [installLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp only [t24]; omega
  · -- end
    rw [memory9]
    apply word_writeLog_at _ _ 0 _ _ (by simp only [endLog, t8]; rfl)
    exact trivial
  · -- threshold
    rw [memory9, out _ (fun x hx => by
        simp only [endLog, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp only [t8]; omega)]
    apply word_writeLog_at _ _ 0 _ _ (by simp only [limitLog, t16]; rfl)
    apply outLRange_of_forall
    intro x hx
    simp only [limitLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp only [t32]; omega
  · -- ptr
    rw [memory9, out _ (fun x hx => by
        simp only [endLog, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp only [t8]; omega),
      out _ (fun x hx => by
        simp only [limitLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp only [t16, t32] <;> omega)]
    apply word_writeLog_at _ _ 1 _ _ (by simp only [installLog, t24]; rfl)
    exact trivial
  · -- limit
    rw [memory9, out _ (fun x hx => by
        simp only [endLog, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp only [t8]; omega)]
    apply word_writeLog_at _ _ 1 _ _ (by simp only [limitLog, t32]; rfl)
    exact trivial

end OCaml.Vm.Gc.Realloc
