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
  disjoint : ∀ e ∈ H, ∀ a, InExt (p.toNat, (request wsz).toNat) a → ¬ InExt e a
  base : bytesT after.σ.mem tbl.toNat 8 = p
  endField : bytesT after.σ.mem (tbl.toNat + 8) 8 = p + (size wsz + 0x100#64) * 0x8#64
  threshold : bytesT after.σ.mem (tbl.toNat + 16) 8 = p + 0x8#64 * size wsz
  ptr : bytesT after.σ.mem (tbl.toNat + 24) 8 = p
  limit : bytesT after.σ.mem (tbl.toNat + 32) 8 = p + 0x8#64 * size wsz
  size : bytesT after.σ.mem (tbl.toNat + 40) 8 = size wsz
  reserve : bytesT after.σ.mem (tbl.toNat + 48) 8 = 0x100#64

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
  refine ⟨c9, run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9)))), ⟨⟨vsaReg c4 10, R.ready, R.pc,
    ⟨g8, g9, g18, g19, trivial⟩, pNonzero, pLow, pHigh, pDisjoint, ?_, ?_, ?_, ?_, ?_, rest9.size, rest9.reserve⟩⟩⟩
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
