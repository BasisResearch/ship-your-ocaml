import OCaml.Vm.Primitives.Uncaught.FormatAlloc

/-!
# `caml_format_exception` on a constant exception: the copy out and the return

`res != NULL` (`allocated_fast`), `memmove(res, data, len + 1)`
(`memmove_leaf`, `CopiedOut`), and the restoring return (`leave_fast`,
`Returned`). `SavedWords` names the six callee-saved words of the 432-byte
frame; the prologue's log writes them (`saved_frameLog`) and every later step
keeps them (`SavedWords.transport`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FormatException
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gprReg_ne_htif)

/-- The six callee-saved words of the 432-byte frame. -/
structure SavedWords (m : Std.ExtHashMap Nat (BitVec 8)) (sp ra s0 s1 s2 s4 s5 : BitVec 64) : Prop where
  savedRa : bytesT m (nativeFrameBase sp 432 + 424) 8 = ra
  saved0 : bytesT m (nativeFrameBase sp 432 + 416) 8 = s0
  saved1 : bytesT m (nativeFrameBase sp 432 + 408) 8 = s1
  saved2 : bytesT m (nativeFrameBase sp 432 + 400) 8 = s2
  saved4 : bytesT m (nativeFrameBase sp 432 + 384) 8 = s4
  saved5 : bytesT m (nativeFrameBase sp 432 + 376) 8 = s5

/-- The prologue's log writes the saved words. -/
theorem saved_frameLog {sp ra s0 s1 s2 s4 s5 : BitVec 64} (frame : NativeFrame sp 432) (m : Std.ExtHashMap Nat (BitVec 8)) :
    SavedWords (writeLog m (frameLog sp ra s0 s1 s2 s4 s5)) sp ra s0 s1 s2 s4 s5 := by
  have a400 := frame_sub frame 400 (by decide)
  have a384 := frame_sub frame 384 (by decide)
  have a424 := frame_sub frame 424 (by decide)
  have a416 := frame_sub frame 416 (by decide)
  have a408 := frame_sub frame 408 (by decide)
  have a376 := frame_sub frame 376 (by decide)
  have a80 := frame_sub frame 80 (by decide)
  have a88 := frame_sub frame 88 (by decide)
  constructor
  · rw [← a424]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 2 _ _ rfl (by
      simp only [frameLog, List.drop_succ_cons, List.drop_zero, OutLRange, a424, a416, a408, a376, a80, a88, and_true]
      omega)
  · rw [← a416]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 3 _ _ rfl (by
      simp only [frameLog, List.drop_succ_cons, List.drop_zero, OutLRange, a416, a408, a376, a80, a88, and_true]
      omega)
  · rw [← a408]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 4 _ _ rfl (by
      simp only [frameLog, List.drop_succ_cons, List.drop_zero, OutLRange, a408, a376, a80, a88, and_true]
      omega)
  · rw [← a400]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [frameLog, List.drop_succ_cons, List.drop_zero, OutLRange, a400, a384, a424, a416, a408, a376, a80,
        a88, and_true]
      omega)
  · rw [← a384]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 1 _ _ rfl (by
      simp only [frameLog, List.drop_succ_cons, List.drop_zero, OutLRange, a384, a424, a416, a408, a376, a80, a88,
        and_true]
      omega)
  · rw [← a376]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 5 _ _ rfl (by
      simp only [frameLog, List.drop_succ_cons, List.drop_zero, OutLRange, a376, a80, a88, and_true]
      omega)

/-- The saved words survive any change outside the frame's top 56 bytes. -/
theorem SavedWords.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {sp ra s0 s1 s2 s4 s5 : BitVec 64}
    (h : SavedWords m sp ra s0 s1 s2 s4 s5)
    (same : ∀ a, nativeFrameBase sp 432 + 376 ≤ a → a < nativeFrameBase sp 432 + 432 →
      (m'[a]?).getD 0 = (m[a]?).getD 0) : SavedWords m' sp ra s0 s1 s2 s4 s5 := by
  have near (off : Nat) (lo : 376 ≤ off) (hi : off + 8 ≤ 432) :
      bytesT m' (nativeFrameBase sp 432 + off) 8 = bytesT m (nativeFrameBase sp 432 + off) 8 :=
    word_observed _ fun i hi' => same _ (Nat.le_trans (Nat.add_le_add_left lo _) (Nat.le_add_right _ _))
      (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi' _) hi) _)
  exact ⟨(near 424 (by decide) (by decide)).trans h.savedRa, (near 416 (by decide) (by decide)).trans h.saved0,
    (near 408 (by decide) (by decide)).trans h.saved1, (near 400 (by decide) (by decide)).trans h.saved2,
    (near 384 (by decide) (by decide)).trans h.saved4, (near 376 (by decide) (by decide)).trans h.saved5⟩

/-- Outside the 432-byte frame, the filled state's memory is the entry's. -/
theorem filled_out {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c0 p f : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c0) (pd : ProDone c0 ra sp exn np s0 s1 s2 s4 s5 p)
    (filled : Filled c0 sp name p f) {a : Nat} (out : a < nativeFrameBase sp 432 ∨ sp.toNat ≤ a) :
    (f.σ.mem[a]?).getD 0 = (c0.σ.mem[a]?).getD 0 := by
  have lower := h.frame.lower
  have fits := h.fits
  unfold nativeFrameBase at out
  have outData : a < dataNat sp ∨ dataNat sp + name.length < a := by
    rcases out with o | o
    · exact Or.inl (show a < sp.toNat - 336 from Nat.lt_of_lt_of_le o (Nat.sub_le_sub_left (by decide) _))
    · exact Or.inr (show sp.toNat - 336 + name.length < a by omega)
  have outPtr : a < sp.toNat - 352 ∨ sp.toNat - 344 ≤ a :=
    out.elim (fun o => Or.inl (Nat.lt_of_lt_of_le o (Nat.sub_le_sub_left (by decide) _)))
      (fun o => Or.inr (Nat.le_trans (Nat.sub_le _ _) o))
  have window : OutWRange [⟨nativeFrameBase sp 432, sp.toNat⟩] a 1 := by
    simp only [OutWRange]; unfold nativeFrameBase; exact ⟨by omega, trivial⟩
  rw [filled.memory.rest a outData outPtr, pd.memory,
    writeLog_out _ _ _ (outL_of_range (OCaml.Vm.Sim.outLRange_of_windows (frameLog_inside h.frame) window)
      (Nat.le_refl _) (Nat.lt_succ_self _))]

/-- The filled state still holds the saved words. -/
theorem filled_saved {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c0 p f : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c0) (pd : ProDone c0 ra sp exn np s0 s1 s2 s4 s5 p)
    (filled : Filled c0 sp name p f) : SavedWords f.σ.mem sp ra s0 s1 s2 s4 s5 := by
  have words := saved_frameLog (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s4 := s4) (s5 := s5) h.frame c0.σ.mem
  rw [← pd.memory] at words
  have lower := h.frame.lower
  have fits := h.fits
  exact words.transport fun a lo hi =>
    filled.memory.rest a (Or.inr (by unfold dataNat; unfold nativeFrameBase at lo; omega))
      (Or.inr (by unfold nativeFrameBase at lo; omega))

theorem beq_of_ne {x y : BitVec 64} (h : x ≠ y) : guardB .BEQ x y = false := by
  simp [guardB, h]

/-- After `memmove(res, data, len + 1)`: back at `0x8000ddec`. -/
structure CopiedOut (H : List (Nat × Nat)) (capacity : Nat) (sp : BitVec 64) (len : Nat) (res : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, len + 1) :: H) capacity (sp + 18446744073709551184#64)
    0x8000ddec#64 after
  pc : PCAt 0x8000ddec#64 after
  result : gprGet after.σ 9 = some res
  copied : ∀ i, i < len + 1 → (after.σ.mem[res.toNat + i]?).getD 0 = (before.σ.mem[dataNat sp + i]?).getD 0
  kept : ∀ a, a < res.toNat ∨ res.toNat + (len + 1) ≤ a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  callee : ∀ k ∈ formatCallee, gprGet after.σ k = gprGet before.σ k
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- **`res != NULL`, then `memmove(res, data, len + 1)`.** -/
theorem format_out {H : List (Nat × Nat)} {capacity len : Nat} {sp res : BitVec 64} {f g : Config}
    (frame : NativeFrame sp 432) (A : Allocated H capacity sp len res f g)
    (size : gprGet g.σ 8 = some (BitVec.ofNat 64 (len + 1))) (data : gprGet g.σ 20 = some (bufData sp)) :
    ∃ e, Steps g e ∧ CopiedOut H capacity sp len res g e := by
  have leaf := A.ready.toLeafInput
  have l0 : LeafInput (regsAt g 1) g := by rw [regsAt_of leaf.raReg]; exact leaf
  have r10 := regsAt_of A.result
  obtain ⟨e1, run1, p1⟩ := (allocated_fast g (regsAt g) l0
    (by simp only [allocated_input, GHolds, r10]; exact ⟨A.result, trivial⟩)
    (by rw [r10]; exact beq_of_ne A.nonzero)).run g ⟨A.pc, rfl⟩
  have o1 := p1.regs
  simp only [allocated_regs, r10, GHolds] at o1
  obtain ⟨b9, b10, -⟩ := o1
  have k1 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [9] → gprGet e1.σ n = gprGet g.σ n :=
    fun n lo hi out => p1.gpr_frame (by decide) n lo hi out
  have e1_1 := (k1 1 (by decide) (by decide) (by decide)).trans leaf.raReg
  have e1_2 := (k1 2 (by decide) (by decide) (by decide)).trans A.ready.stack
  have e1_8 := (k1 8 (by decide) (by decide) (by decide)).trans size
  have e1_20 := (k1 20 (by decide) (by decide) (by decide)).trans data
  have l1 : LeafInput (regsAt e1 1) e1 := by
    rw [regsAt_of e1_1]; exact ⟨p1.good, p1.image, p1.minstret, e1_1, by decide, p1.tick⟩
  obtain ⟨e2, run2, p2⟩ := (copyOut_fast e1 (regsAt e1) l1 (by
      simp only [copyOut_input, GHolds, regsAt_of e1_1, regsAt_of e1_8, regsAt_of b10, regsAt_of e1_20]
      exact ⟨e1_1, e1_8, b10, e1_20, trivial⟩)).run e1 ⟨p1.pc, rfl⟩
  have o2 := p2.regs
  simp only [copyOut_regs, regsAt_of e1_1, regsAt_of e1_8, regsAt_of b10, regsAt_of e1_20,
    GHolds] at o2
  obtain ⟨c11, c12, -, -, c10, -, -⟩ := o2
  have k2 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [11, 12] → gprGet e2.σ n = gprGet e1.σ n :=
    fun n lo hi out => p2.gpr_frame (by decide) n lo hi out
  obtain ⟨e3, run3, p3⟩ := (call_registers_summary copyOut_call_shape copyOut_call_decode e2
    (copyOut_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(10, res), (11, bufData sp), (12, BitVec.ofNat 64 (len + 1)), (9, res), (2, sp + 18446744073709551184#64)]
    ⟨c10, c11, c12, (k2 9 (by decide) (by decide) (by decide)).trans b9,
      (k2 2 (by decide) (by decide) (by decide)).trans e1_2, trivial⟩
    (by change KeysOK [10, 11, 12, 9, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run e2 ⟨p2.pc, rfl⟩
  have ready3 := ((A.ready.library.carry p1.kept (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry
    p2.kept (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p3.kept
    (p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
  have leaf3 : LeafInput 0x8000ddec#64 e3 :=
    ⟨p3.good, p3.image, p3.minstret, gholds_lookup (n := 1) _ p3.regs rfl, by decide, p3.tick⟩
  have lo := frame.lower
  have up := frame.upper
  have rl := A.low
  have rh := A.high
  simp only [heapStart, heapEnd, Layout.sym_stack_top] at lo up rl rh
  obtain ⟨e4, run4, p4⟩ := (memmove_leaf (d := res.toNat) (src := dataNat sp) (len := len + 1) e3 leaf3 ready3
    ⟨by omega, ⟨Nat.le_refl _, Nat.le_refl _⟩, by omega, by unfold dataNat; omega, by unfold dataNat; omega,
      Or.inr (by unfold dataNat; omega), Or.inr (by unfold dataNat; omega)⟩
    (fun a lo' _ foot => by
      have := stdioFoot_high foot; simp only [Layout.sym_bss_end] at this; unfold dataNat at lo'; omega)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gholds_lookup (n := 10) _ p3.regs rfl)
    (by rw [← data_eq frame]; exact gholds_lookup (n := 11) _ p3.regs rfl)
    (gholds_lookup (n := 12) _ p3.regs rfl)).run e3
    ⟨by have := p3.pc; rw [copyOut_call_target] at this; exact this, rfl⟩
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ memmoveScratch → n ∉ [10] → gprGet e4.σ n = gprGet e3.σ n := p4.registers
  have m3 : ∀ x : Nat, (e3.σ.mem[x]?).getD (0 : BitVec 8) = (g.σ.mem[x]?).getD 0 := fun x => by
    rw [p3.memory, p2.memory, wl_nil, p1.memory, wl_nil]
  have kept (a : Nat) (out : a < res.toNat ∨ res.toNat + (len + 1) ≤ a) :
      (e4.σ.mem[a]?).getD 0 = (g.σ.mem[a]?).getD 0 := by
    have kp := p4.kept a out
    rw [byte_total, byte_total] at kp
    rw [kp, m3]
  refine ⟨e4, run1.trans (run2.trans (run3.trans run4)), ?_⟩
  exact
    { ready := ready_transport A.ready p4.toLeafInput
        ⟨p4.libraryGood.gpr, (k4 3 (by decide) (by decide) (by decide) (by decide)).trans ready3.gp,
          p4.libraryGood.htifIdle⟩
        (fun a ha => kept a (Or.inl (by have := A.low; omega)))
        (fun a ha => kept a (allocator_payload_outside List.mem_cons_self A.low ha))
        ((k4 2 (by decide) (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ p3.regs rfl))
      pc := p4.pc
      result := (k4 9 (by decide) (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ p3.regs rfl)
      copied := fun i hi => by
        have cp := p4.copied i hi
        rw [byte_total, byte_total] at cp
        rw [cp, m3]
      kept := kept
      callee := fun k hk => by
        have mem := hk
        simp only [formatCallee, List.mem_cons, List.not_mem_nil, or_false] at mem
        have out (l : List Nat) (hl : l = memmoveScratch ∨ l = [10] ∨ l = [1] ∨ l = [11, 12] ∨ l = [9]) : k ∉ l :=
          fun hm => by
            rcases hl with rfl | rfl | rfl | rfl | rfl <;>
              simp only [memmoveScratch, List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
        exact (k4 k (by omega) (by omega) (out _ (.inl rfl)) (out _ (.inr (.inl rfl)))).trans
          ((p3.gpr_frame (by decide) k (by omega) (by omega) (out _ (.inr (.inr (.inl rfl))))).trans
            ((k2 k (by omega) (by omega) (out _ (.inr (.inr (.inr (.inl rfl)))))).trans
              (k1 k (by omega) (by omega) (out _ (.inr (.inr (.inr (.inr rfl))))))))
      output := by
        rw [p4.output]
        simp only [Vsa.Machine.output]
        rw [p3.output, p2.output, p1.output] }

/-- After the restoring return. -/
structure Returned (H : List (Nat × Nat)) (capacity : Nat) (ra sp s0 s1 s2 s4 s5 : BitVec 64) (len : Nat)
    (res : BitVec 64) (before after : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, len + 1) :: H) capacity sp ra after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some res
  saved0 : gprGet after.σ 8 = some s0
  saved1 : gprGet after.σ 9 = some s1
  saved2 : gprGet after.σ 18 = some s2
  saved4 : gprGet after.σ 20 = some s4
  saved5 : gprGet after.σ 21 = some s5
  callee : ∀ k ∈ formatCallee, gprGet after.σ k = gprGet before.σ k
  memory : after.σ.mem = before.σ.mem
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- **The restoring return**: the saved words back, `a0 = res`, `ret`. -/
theorem format_leave {H : List (Nat × Nat)} {capacity len : Nat} {ra sp s0 s1 s2 s4 s5 res : BitVec 64}
    {g e : Config} (frame : NativeFrame sp 432) (aligned : ra.toNat % 4 = 0)
    (co : CopiedOut H capacity sp len res g e) (words : SavedWords e.σ.mem sp ra s0 s1 s2 s4 s5) :
    ∃ r, Steps e r ∧ Returned H capacity ra sp s0 s1 s2 s4 s5 len res e r := by
  have leaf := co.ready.toLeafInput
  have l0 : LeafInput (regsAt e 1) e := by rw [regsAt_of leaf.raReg]; exact leaf
  have r2 := regsAt_of co.ready.stack
  have slot (off : Nat) (bound : off + 8 ≤ 432) (al : off % 8 = 0) :
      ReadWindow (regsAt e 2 + BitVec.ofNat 64 off) 8 := by
    rw [r2, frame_slot frame off (by omega)]; exact (frame.word bound al).read
  have word (off : Nat) (bound : off ≤ 432) :
      bytesVal .ld (read8 e.σ.mem (regsAt e 2 + BitVec.ofNat 64 off).toNat) =
        bytesT e.σ.mem (nativeFrameBase sp 432 + off) 8 := by
    rw [read8_value, r2, frame_slot frame off bound, frame.slot_nat bound]
  have w424 := (word 424 (by decide)).trans words.savedRa
  have w416 := (word 416 (by decide)).trans words.saved0
  have w408 := (word 408 (by decide)).trans words.saved1
  have w400 := (word 400 (by decide)).trans words.saved2
  have w384 := (word 384 (by decide)).trans words.saved4
  have w376 := (word 376 (by decide)).trans words.saved5
  obtain ⟨r, run, p⟩ := (leave_fast e ra (regsAt e) l0
    (by simp only [leave_input, GHolds, r2, regsAt_of co.result]; exact ⟨co.ready.stack, co.result, trivial⟩)
    (slot 424 (by decide) (by decide)) (slot 416 (by decide) (by decide)) (slot 400 (by decide) (by decide))
    (slot 384 (by decide) (by decide)) (slot 376 (by decide) (by decide)) (slot 408 (by decide) (by decide))
    w424 aligned).run e ⟨co.pc, rfl⟩
  have spBack : sp + 18446744073709551184#64 + 432#64 = sp := by
    rw [BitVec.add_assoc, show (18446744073709551184#64 : BitVec 64) + 432#64 = 0#64 by decide, BitVec.add_zero]
  have o := p.regs
  simp only [leave_regs, leave_loads, List.getD_cons_zero, List.getD_cons_succ, w424, w416, w408, w400, w384, w376,
    regsAt_of co.result, GHolds] at o
  obtain ⟨g2, g9, g10, g21, g20, g18, g8, g1, -⟩ := o
  rw [r2, spBack] at g2
  refine ⟨r, run, ?_⟩
  exact
    { ready := co.ready.effect p (by decide) (by simp only [leave_regs, keysG]; decide) (by decide)
        g2 g1 aligned (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
      pc := p.pc
      result := g10
      saved0 := g8
      saved1 := g9
      saved2 := g18
      saved4 := g20
      saved5 := g21
      callee := fun k hk => by
        have mem := hk
        simp only [formatCallee, List.mem_cons, List.not_mem_nil, or_false] at mem
        exact p.gpr_frame (by decide) k (by omega) (by omega) (fun hm => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega)
      memory := by rw [p.memory, wl_nil]
      output := by simp only [Vsa.Machine.output, p.output] }

end OCaml.Vm.Primitives.Uncaught.FormatException
