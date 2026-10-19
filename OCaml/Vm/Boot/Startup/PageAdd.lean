import OCaml.Vm.Boot.Startup.PageAddSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_page_table_add over the `n` pages of an aligned block: one
`page_table_modify_insert` per page, folded by `indexedLoop`. -/

/-- The table after one insertion into slot `s`. -/
theorem table_after_insert {m m' : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} {ent occ v : BitVec 64}
    {s lo hi : Nat} (hs : s < 2048) (fits : ent.toNat + 16384 ≤ heapEnd) (tableHigh : heapStart ≤ ent.toNat)
    (stackLog : LogInW [⟨lo, hi⟩] log) (above : heapEnd ≤ lo)
    (eq : m' = writeLog (writeLog m log)
      [((slotAddr ent (BitVec.ofNat 64 s)).toNat, 8, v), (pageTable + 0x18, 8, occ + 1#64)])
    (F : PageTableFields m occ ent) :
    PageTableFields m' (occ + 1#64) ent ∧
      (∀ i, i < 2048 → slotWord m' ent i = if i = s then v else slotWord m ent i) := by
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  rw [hE] at fits above
  rw [hS] at tableHigh
  have fits64 : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans fits (by decide)
  have slotNat := slotAddr_nat ent s hs fits64
  -- below the arena's end the stack log is invisible
  have low (x : Nat) (hx : x < heapEnd) : ((writeLog m log)[x]?).getD 0 = (m[x]?).getD 0 := by
    rw [hE] at hx
    rw [frameOn_writeLog _ _ _ stackLog x ⟨Or.inl (show x < lo by omega), trivial⟩]
  have record (off w : Nat) (hoff : off + w ≤ 0x18 ∨ 0x20 ≤ off) (hw : off + w ≤ 0x28) (x : Nat)
      (hx : pageTable + off ≤ x ∧ x < pageTable + off + w) : (m'[x]?).getD 0 = (m[x]?).getD 0 := by
    rw [hP] at hx
    rw [eq, writeLog_out _ _ _ (by simp only [OutL, slotNat, hP, and_true]; omega), low x (by rw [hE]; omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [word_observed (m := m) _ fun i hi => record 0 8 (Or.inl (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.size
  · rw [read4_observed (m := m) _ fun k hk => record 8 4 (Or.inl (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.shift
  · rw [word_observed (m := m) _ fun i hi => record 0x10 8 (Or.inl (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.mask
  · rw [eq]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial
  · rw [word_observed (m := m) _ fun i hi => record 0x20 8 (Or.inr (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.entries
  · intro i hi
    have iNat := slotAddr_nat ent i hi fits64
    split
    · rename_i same; subst same
      unfold slotWord
      rw [eq]
      exact word_writeLog_at _ _ 0 _ _ rfl (by
        simp only [List.drop, OutLRange, hP, and_true]; omega)
    · rename_i ne
      unfold slotWord
      rw [word_observed (m := m) _ fun k hk => by
        rw [eq, writeLog_out _ _ _ (by simp only [OutL, slotNat, iNat, hP, and_true]; omega),
          low _ (by rw [iNat, hE]; omega)]]

theorem occ_room (x : BitVec 64) (h : x.toNat < 1024) : guardB bop.BGEU (x <<< 1) 2048#64 = false := by
  unfold guardB Functions.zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  apply decide_eq_false
  intro hc
  have := Int.ofNat_le.mp hc
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem blockPage_succ (base : BitVec 64) (k : Nat) : blockPage base k + 4096#64 = blockPage base (k + 1) := by
  unfold blockPage
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2 <;> omega

theorem blockPage_nat (base : BitVec 64) (k : Nat) (fits : base.toNat + 4096 * k < 2 ^ 64) :
    (blockPage base k).toNat = base.toNat + 4096 * k := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold blockPage
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [p64] at fits ⊢
  rw [Nat.mod_eq_of_lt (a := 4096 * k) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem last_test (base : BitVec 64) (k n : Nat) (hk : k < n) (fits : base.toNat + 4096 * n < 2 ^ 64) :
    guardB bop.BLTU (blockPage base (n - 1)) (blockPage base k + 4096#64) = !decide (k + 1 < n) := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [p64] at fits
  have a := blockPage_nat base (n - 1) (by rw [p64]; omega)
  have b := blockPage_nat base (k + 1) (by rw [p64]; omega)
  rw [blockPage_succ]
  unfold guardB Functions.zopz0zI_u
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.ofNat_lt]
  rw [a, b]
  omega

theorem or_ne_zero {kind p : BitVec 64} (nz : kind ≠ 0#64) : kind ||| p ≠ 0#64 := by
  intro h
  apply nz
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun x => x.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at this
  simp only [this.1, BitVec.getLsbD_zero]

/-- Filling one empty slot, seen through the slot words, adds one to the count. -/
theorem pageCount_raise {m m' : Std.ExtHashMap Nat (BitVec 8)} {blk s : Nat} {v : BitVec 64} (hs : s < 2048)
    (empty : pageSlot m blk s = 0#64) (nonzero : v ≠ 0#64)
    (update : ∀ i, i < 2048 → pageSlot m' blk i = if i = s then v else pageSlot m blk i) :
    pageCount m' blk = pageCount m blk + 1 := by
  rw [pageCount_congr (m := writeLog m [(blk + 8 * s, 8, v)]) (fun i hi => by rw [update i hi, pageSlot_write]),
    pageCount_fill hs empty nonzero]

/-- The link register inside the loop: the caller's before the first call. -/
def addLink (k : Nat) (ra : BitVec 64) : BitVec 64 := if k = 0 then ra else jal_8000b134_call.link

/-- What `caml_page_table_add`'s loop needs of the block and the table. -/
structure PageAddSpan (H : List (Nat × Nat)) (sp kind base ent : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  /-- caml_page_table_add's frame and caml_page_table_modify's below it. -/
  frame : NativeFrame sp 144
  aligned : base.toNat % 4096 = 0
  fits : base.toNat + 4096 * n < 2 ^ 64
  small : kind.toNat < 4096
  kindNonzero : kind ≠ 0#64
  /-- The table stays at most half full. -/
  room : pageCount m0 ent.toNat + n ≤ 1024
  windows : ∀ i, i < 2048 → WriteWindow (slotAddr ent (BitVec.ofNat 64 i)) 8
  tableLow : ent.toNat + 16384 ≤ heapEnd
  tableHigh : heapStart ≤ ent.toNat
  tableOwned : (ent.toNat, 16384) ∈ H
  /-- No page of the block is in the table yet. -/
  disjoint : ∀ i, i < 2048 → slotWord m0 ent i ≠ 0#64 → ∀ j, j < n →
    guardB bop.BGEU (blockPage base j ^^^ slotWord m0 ent i) 4096#64 = true

/-- `caml_page_table_add`'s loop before page `k` of `n`. -/
structure PageAddAt (H : List (Nat × Nat)) (capacity : Nat) (sp ra kind base ent : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (start : Config) (k : Nat) (d : Config) : Prop where
  pc : PCAt (if k < n then 0x8000b128#64 else 0x8000b160#64) d
  regs : GHolds d.σ [(2, nativeStack sp 48), (8, blockPage base k), (9, blockPage base (n - 1)), (18, kind),
    (19, 4096#64)]
  ready : RuntimeReady H capacity (nativeStack sp 48) (addLink k ra) d
  bound : k ≤ n
  fields : PageTableFields d.σ.mem (BitVec.ofNat 64 (pageCount m0 ent.toNat + k)) ent
  count : pageCount d.σ.mem ent.toNat = pageCount m0 ent.toNat + k
  /-- Every entry is the starting table's or one of the first `k` pages. -/
  known : ∀ i, i < 2048 → slotWord d.σ.mem ent i ≠ 0#64 →
    slotWord d.σ.mem ent i = slotWord m0 ent i ∨ ∃ j, j < k ∧ slotWord d.σ.mem ent i = kind ||| blockPage base j
  /-- Below the arena's end only the slots and the occupancy change. -/
  kept : ∀ x, x < heapEnd → OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x →
    (d.σ.mem[x]?).getD 0 = (m0[x]?).getD 0
  /-- The first `k` pages are in the table. -/
  present : ∀ j, j < k → ∃ i, i < 2048 ∧ slotWord d.σ.mem ent i = kind ||| blockPage base j
  caller : ∀ x, (nativeStack sp 48).toNat ≤ x → (d.σ.mem[x]?).getD 0 = (start.σ.mem[x]?).getD 0

theorem PageAddAt.index {H capacity sp ra kind base ent n m0 start k d} (S : PageAddSpan H sp kind base ent n m0)
    (A : PageAddAt H capacity sp ra kind base ent n m0 start k d) :
    (((gprGet d.σ 8).getD 0).toNat - base.toNat) / 4096 = k := by
  have bound := A.bound
  have fits := S.fits
  rw [gholds_lookup (n := 8) _ A.regs rfl, Option.getD_some,
    blockPage_nat base k (Nat.lt_of_le_of_lt (by omega) fits)]
  omega

/-- One page: caml_page_table_modify inserts it, then the bound test. -/
theorem page_add_step {H capacity sp ra kind base ent n m0 start} (S : PageAddSpan H sp kind base ent n m0)
    (k : Nat) (d : Config) (A : PageAddAt H capacity sp ra kind base ent n m0 start k d) (lt : k < n) :
    ∃ e, Steps d e ∧ PageAddAt H capacity sp ra kind base ent n m0 start (k + 1) e := by
  have frame48 : NativeFrame sp 48 := S.frame.resize (by decide) (by decide)
  have frameM : NativeFrame (nativeStack sp 48) 96 := S.frame.nested (front := 48) (size := 96) (by decide)
  have fits64 : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans S.tableLow (by decide)
  have pc0 : PCAt 0x8000b128#64 d := by have := A.pc; simp only [lt, ite_true] at this; exact this
  obtain ⟨d1, run1, p1⟩ := (page_add_call d (addLink k ra) (blockPage base k) kind A.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ A.regs rfl, gholds_lookup (n := 18) _ A.regs rfl, trivial⟩).run d ⟨pc0, rfl⟩
  have keep1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [10, 12, 11] ++ [1]) : gprGet d1.σ r = gprGet d.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have mem1 : d1.σ.mem = d.σ.mem := p1.memory
  obtain ⟨s4, hs4⟩ := Option.isSome_iff_exists.mp (A.ready.gpr_some 20 (by decide) (by decide))
  have ready1 : RuntimeReady H capacity (nativeStack sp 48) jal_8000b134_call.link d1 :=
    A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep1 2 (by decide) (by decide) (by decide)).trans A.ready.stack) (gholds_lookup (n := 1) _ p1.regs rfl)
      (by decide) frame48 (by simp only [LogInW])
  have target : jal_8000b134_call.target = 0x8000ada4#64 := by decide
  have count1 : pageCount d1.σ.mem ent.toNat = pageCount m0 ent.toNat + k := by rw [mem1]; exact A.count
  have room := S.room
  obtain ⟨hole, holeLt, holeEmpty⟩ := pageCount_empty (m := d1.σ.mem) (blk := ent.toNat) (by omega)
  obtain ⟨slot, steps, d2, run2, M⟩ := page_table_modify_insert d1 H capacity (nativeStack sp 48)
    jal_8000b134_call.link (blockPage base k) kind (blockPage base k) (blockPage base (n - 1)) kind 4096#64 s4
    (BitVec.ofNat 64 (pageCount m0 ent.toNat + k)) ent {
      pc := by rw [← target]; exact p1.pc
      regs := ⟨(keep1 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ A.regs rfl),
        gholds_lookup (n := 1) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl,
        gholds_lookup (n := 11) _ p1.regs rfl, gholds_lookup (n := 12) _ p1.regs rfl,
        gholds_lookup (n := 8) _ p1.regs rfl,
        (keep1 9 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ A.regs rfl),
        gholds_lookup (n := 18) _ p1.regs rfl,
        (keep1 19 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 19) _ A.regs rfl),
        (keep1 20 (by decide) (by decide) (by decide)).trans hs4, trivial⟩
      ready := ready1
      frame := frameM
      fields := by rw [mem1]; exact A.fields
      room := occ_room _ (by rw [BitVec.toNat_ofNat]; omega)
      hole := ⟨hole, holeLt, by rw [slotWord_pageSlot _ _ _ holeLt fits64]; exact holeEmpty⟩
      windows := S.windows
      tableLow := S.tableLow
      tableHigh := S.tableHigh
      tableOwned := S.tableOwned
      absent := fun i hi occupied => by
        rw [mem1] at occupied ⊢
        rcases A.known i hi occupied with old | ⟨j, hj, eq⟩
        · rw [old]; exact S.disjoint i hi (by rw [← old]; exact occupied) k lt
        · rw [eq]
          have fitsN := S.fits
          exact blockPage_other base kind j k (by omega) S.aligned (by omega) (by omega) S.small }
  have slotLt : slot < 2048 := by rw [M.at_slot]; unfold probe; omega
  have stackAbove : heapEnd ≤ nativeFrameBase (nativeStack sp 48) 96 := by
    have := frameM.lower; unfold nativeFrameBase; omega
  have T := table_after_insert slotLt S.tableLow S.tableHigh (pageModifyLog_inside frameM) stackAbove M.memory
    (by rw [mem1]; exact A.fields)
  obtain ⟨d3, run3, p3⟩ := (page_add_next d2 jal_8000b134_call.link (blockPage base k) (blockPage base (n - 1))
    (decide (k + 1 < n)) M.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ M.regs rfl, gholds_lookup (n := 19) _ M.regs rfl, gholds_lookup (n := 10) _ M.regs rfl,
      gholds_lookup (n := 9) _ M.regs rfl, trivial⟩ (last_test base k n lt S.fits)).run d2 ⟨M.pc, rfl⟩
  have keep3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [8]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  have mem3 : d3.σ.mem = d2.σ.mem := p3.memory
  have update (i : Nat) (hi : i < 2048) :
      slotWord d3.σ.mem ent i = if i = slot then kind ||| blockPage base k else slotWord d.σ.mem ent i := by
    rw [mem3, T.2 i hi, mem1]
  have slotNat := slotAddr_nat ent slot slotLt fits64
  have tableLow := S.tableLow
  have stackNat : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  have spLow := S.frame.lower
  refine ⟨d3, run1.trans (run2.trans run3), {
    pc := by have := p3.pc; simp only [decide_eq_true_eq] at this; exact this
    regs := ⟨(keep3 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ M.regs rfl),
      by rw [gholds_lookup (n := 8) _ p3.regs rfl, blockPage_succ],
      gholds_lookup (n := 9) _ p3.regs rfl,
      (keep3 18 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 18) _ M.regs rfl),
      gholds_lookup (n := 19) _ p3.regs rfl, trivial⟩
    ready := by
      rw [show addLink (k + 1) ra = jal_8000b134_call.link from if_neg (by omega)]
      exact M.ready.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
        ((keep3 2 (by decide) (by decide) (by decide)).trans M.ready.stack)
        ((keep3 1 (by decide) (by decide) (by decide)).trans M.ready.raReg) M.ready.aligned frame48
        (by simp only [LogInW])
    bound := by omega
    fields := by
      rw [mem3, show pageCount m0 ent.toNat + (k + 1) = (pageCount m0 ent.toNat + k) + 1 by omega,
        BitVec.ofNat_add]
      exact T.1
    count := by
      rw [mem3, pageCount_raise (m := d1.σ.mem) slotLt
        (by rw [← slotWord_pageSlot _ _ _ slotLt fits64]; exact M.empty) (or_ne_zero S.kindNonzero)
        (fun i hi => by
          rw [← slotWord_pageSlot _ _ _ hi fits64, T.2 i hi, slotWord_pageSlot _ _ _ hi fits64]), count1]
      omega
    known := fun i hi occupied => by
      rw [update i hi] at occupied ⊢
      by_cases same : i = slot
      · rw [if_pos same]; exact Or.inr ⟨k, by omega, rfl⟩
      · rw [if_neg same] at occupied ⊢
        rcases A.known i hi occupied with old | ⟨j, hj, eq⟩
        · exact Or.inl old
        · exact Or.inr ⟨j, by omega, eq⟩
    kept := fun x hx out => by
      simp only [OutW, and_true] at out
      rw [mem3, M.memory, writeLog_out _ _ _ (by simp only [OutL, slotNat, and_true]; omega),
        frameOn_writeLog _ _ _ (pageModifyLog_inside frameM) x ⟨Or.inl (by dsimp only; omega), trivial⟩, mem1]
      exact A.kept x hx (by simp only [OutW, and_true]; exact out)
    caller := fun x hx => by
      have tableBelow : pageTable + 0x20 ≤ heapEnd := by decide
      rw [mem3, M.memory, writeLog_out _ _ _ (by simp only [OutL, slotNat, and_true]; omega),
        frameOn_writeLog _ _ _ (pageModifyLog_inside frameM) x ⟨Or.inr (by dsimp only; omega), trivial⟩, mem1]
      exact A.caller x hx
    present := fun j hj => by
      by_cases last : j = k
      · subst last
        exact ⟨slot, slotLt, by rw [update slot slotLt, if_pos rfl]⟩
      · obtain ⟨i, hi, eq⟩ := A.present j (by omega)
        have ne : i ≠ slot := by
          rintro rfl
          have empty := M.empty
          rw [mem1, eq] at empty
          exact or_ne_zero S.kindNonzero empty
        exact ⟨i, hi, by rw [update i hi, if_neg ne, eq]⟩ }⟩

/-- caml_page_table_add's loop over all `n` pages of the block. -/
theorem page_add_loop {H capacity sp ra kind base ent n m0 start} (S : PageAddSpan H sp kind base ent n m0)
    (A : PageAddAt H capacity sp ra kind base ent n m0 start 0 start) :
    ∃ d, Steps start d ∧ PageAddAt H capacity sp ra kind base ent n m0 start n d :=
  indexedLoop (I := PageAddAt H capacity sp ra kind base ent n m0 start)
    (index := fun d => (((gprGet d.σ 8).getD 0).toNat - base.toNat) / 4096) (start := 0) (count := n)
    (fun _ _ h => h.index S) (fun _ _ h => h.bound) (fun k d ⟨h, lt⟩ => page_add_step S k d h lt) start A
end OCaml.Vm.Boot.Startup
