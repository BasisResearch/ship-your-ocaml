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

/-- Memory that agrees below the arena's end carries the table record. -/
theorem PageTableFields.agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {occ ent : BitVec 64}
    (agree : ∀ x, x < heapEnd → (m'[x]?).getD 0 = (m[x]?).getD 0) (F : PageTableFields m occ ent) :
    PageTableFields m' occ ent := by
  have hP : pageTable = 0x800684b8 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [word_observed (m := m) _ fun i hi => agree _ (by rw [hP, hE]; omega)]; exact F.size
  · rw [read4_observed (m := m) _ fun i hi => agree _ (by rw [hP, hE]; omega)]; exact F.shift
  · rw [word_observed (m := m) _ fun i hi => agree _ (by rw [hP, hE]; omega)]; exact F.mask
  · rw [word_observed (m := m) _ fun i hi => agree _ (by rw [hP, hE]; omega)]; exact F.occupancy
  · rw [word_observed (m := m) _ fun i hi => agree _ (by rw [hP, hE]; omega)]; exact F.entries

theorem slotWord_agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64} (tableLow : ent.toNat + 16384 ≤ heapEnd)
    (agree : ∀ x, x < heapEnd → (m'[x]?).getD 0 = (m[x]?).getD 0) (i : Nat) (hi : i < 2048) :
    slotWord m' ent i = slotWord m ent i := by
  have fits64 : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans tableLow (by decide)
  unfold slotWord
  rw [slotAddr_nat ent i hi fits64]
  exact word_observed _ fun k hk => agree _ (by omega)

theorem first_le_last (base : BitVec 64) (n : Nat) (pos : 0 < n) (fits : base.toNat + 4096 * n < 2 ^ 64) :
    guardB bop.BLTU (blockPage base (n - 1)) base = false := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [p64] at fits
  have a := blockPage_nat base (n - 1) (by rw [p64]; omega)
  unfold guardB Functions.zopz0zI_u
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.false_eq_true, iff_false]
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.ofNat_lt]
  rw [a]
  omega

theorem pageAddLog_split (sp ra s0 s1 s2 s3 : BitVec 64) :
    pageAddLogA sp ra s0 s1 ++ pageAddLogB sp s2 s3 = pageAddLog sp ra s0 s1 s2 s3 := rfl

/-- caml_page_table_add(kind, start, stop) is called on the pages of a block. -/
structure PageAddCall (H : List (Nat × Nat)) (capacity : Nat) (sp ra kind start stop s0 s1 s2 s3 base ent : BitVec 64)
    (n : Nat) (c : Config) : Prop where
  pc : PCAt 0x8000b0ec#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, kind), (11, start), (12, stop), (8, s0), (9, s1), (18, s2), (19, s3)]
  ready : RuntimeReady H capacity sp ra c
  first : start &&& 0xfffffffffffff000#64 = base
  last : (stop + Functions.sign_extend (m := 64) 4095#12) &&& 0xfffffffffffff000#64 = blockPage base (n - 1)
  nonempty : 0 < n
  /-- The record's occupancy counts the nonzero slots. -/
  fields : PageTableFields c.σ.mem (BitVec.ofNat 64 (pageCount c.σ.mem ent.toNat)) ent
  span : PageAddSpan H sp kind base ent n c.σ.mem

/-- The `n` pages are in the table, after whatever it held before. -/
structure PageAdded (H : List (Nat × Nat)) (capacity : Nat) (sp ra kind s0 s1 s2 s3 base ent : BitVec 64) (n : Nat)
    (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (10, 0#64), (9, s1), (8, s0), (1, ra), (19, s3), (18, s2)]
  ready : RuntimeReady H capacity sp ra after
  fields : PageTableFields after.σ.mem (BitVec.ofNat 64 (pageCount before.σ.mem ent.toNat + n)) ent
  count : pageCount after.σ.mem ent.toNat = pageCount before.σ.mem ent.toNat + n
  known : ∀ i, i < 2048 → slotWord after.σ.mem ent i ≠ 0#64 →
    slotWord after.σ.mem ent i = slotWord before.σ.mem ent i ∨
      ∃ j, j < n ∧ slotWord after.σ.mem ent i = kind ||| blockPage base j
  present : ∀ j, j < n → ∃ i, i < 2048 ∧ slotWord after.σ.mem ent i = kind ||| blockPage base j
  kept : ∀ x, x < heapEnd → OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  caller : ∀ x, sp.toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem page_table_add (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra kind start stop s0 s1 s2 s3 base ent : BitVec 64) (n : Nat)
    (A : PageAddCall H capacity sp ra kind start stop s0 s1 s2 s3 base ent n c) :
    ∃ after, Steps c after ∧ PageAdded H capacity sp ra kind s0 s1 s2 s3 base ent n c after := by
  have S := A.span
  have frame48 : NativeFrame sp 48 := S.frame.resize (by decide) (by decide)
  have regs := A.regs
  have stackNat : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  have spLow := S.frame.lower
  -- addi sp, sp, -48
  obtain ⟨d1, run1, p1⟩ := (page_add_frame c sp ra kind A.ready.toLeafInput
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 10) _ regs rfl, trivial⟩).run c ⟨A.pc, rfl⟩
  have keep1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [2]) : gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready1 : RuntimeReady H capacity (nativeStack sp 48) ra d1 :=
    A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p1.regs rfl)
      ((keep1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg) A.ready.aligned frame48
      (by simp only [LogInW])
  -- save ra, s0, s1; page-align the bounds
  obtain ⟨d2, run2, p2⟩ := (page_add_align d1 sp ra s0 s1 start stop base (blockPage base (n - 1)) kind
    ready1.toLeafInput frame48
    ⟨gholds_lookup (n := 2) _ p1.regs rfl, (keep1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg,
      (keep1 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ regs rfl),
      (keep1 9 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ regs rfl),
      (keep1 11 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 11) _ regs rfl),
      (keep1 12 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 12) _ regs rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩
    A.first A.last (first_le_last base n A.nonempty S.fits)).run d1 ⟨p1.pc, rfl⟩
  have keep2 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15, 9, 8]) : gprGet d2.σ r = gprGet d1.σ r :=
    p2.toEffectPost.gpr_frame (by decide) r lo hi out
  have insideA : LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (pageAddLogA sp ra s0 s1) :=
    frame48.word_log_inside fun off value member => by simp at member; omega
  have insideB : LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (pageAddLogB sp s2 s3) :=
    frame48.word_log_inside fun off value member => by simp at member; omega
  have ready2 : RuntimeReady H capacity (nativeStack sp 48) ra d2 :=
    ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p2.regs rfl)
      ((keep2 1 (by decide) (by decide) (by decide)).trans ready1.raReg) ready1.aligned frame48 insideA
  -- save s2, s3; s3 = 4096, s2 = kind
  obtain ⟨d3, run3, p3⟩ := (page_add_setup d2 sp ra s2 s3 kind ready2.toLeafInput frame48
    ⟨gholds_lookup (n := 2) _ p2.regs rfl,
      ((keep2 18 (by decide) (by decide) (by decide)).trans (keep1 18 (by decide) (by decide) (by decide))).trans
        (gholds_lookup (n := 18) _ regs rfl),
      ((keep2 19 (by decide) (by decide) (by decide)).trans (keep1 19 (by decide) (by decide) (by decide))).trans
        (gholds_lookup (n := 19) _ regs rfl),
      gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩).run d2 ⟨p2.pc, rfl⟩
  have keep3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [18, 19]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready3 : RuntimeReady H capacity (nativeStack sp 48) ra d3 :=
    ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p3.regs rfl)
      ((keep3 1 (by decide) (by decide) (by decide)).trans ready2.raReg) ready2.aligned frame48 insideB
  have mem3 : d3.σ.mem = writeLog c.σ.mem (pageAddLog sp ra s0 s1 s2 s3) := by
    rw [p3.memory, p2.memory, p1.memory, ← pageAddLog_split, writeLog_append]; rfl
  have agree3 (x : Nat) (hx : x < heapEnd) : (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem3, frameOn_writeLog _ _ _ (pageAddLog_inside frame48) x
      ⟨Or.inl (show x < nativeFrameBase sp 48 by unfold nativeFrameBase; omega), trivial⟩]
  have above3 (x : Nat) (hx : sp.toNat ≤ x) : (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem3, frameOn_writeLog _ _ _ (pageAddLog_inside frame48) x ⟨Or.inr hx, trivial⟩]
  -- the page loop
  obtain ⟨d4, run4, L⟩ := page_add_loop (capacity := capacity) (ra := ra) (start := d3) S {
    pc := by simp only [A.nonempty, ite_true]; exact p3.pc
    regs := ⟨gholds_lookup (n := 2) _ p3.regs rfl,
      by rw [(keep3 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ p2.regs rfl)]
         simp only [blockPage, Nat.mul_zero, BitVec.add_zero],
      (keep3 9 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ p2.regs rfl),
      gholds_lookup (n := 18) _ p3.regs rfl, gholds_lookup (n := 19) _ p3.regs rfl, trivial⟩
    ready := ready3
    bound := Nat.zero_le _
    fields := PageTableFields.agree agree3 (by simpa using A.fields)
    count := by
      have fits64 : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans S.tableLow (by decide)
      rw [Nat.add_zero]
      exact pageCount_congr fun i hi => by
        rw [← slotWord_pageSlot _ _ _ hi fits64, ← slotWord_pageSlot _ _ _ hi fits64]
        exact slotWord_agree S.tableLow agree3 i hi
    known := fun i hi _ => Or.inl (slotWord_agree S.tableLow agree3 i hi)
    kept := fun x hx _ => agree3 x hx
    present := fun j hj => absurd hj (Nat.not_lt_zero j)
    caller := fun _ _ => rfl }
  have pc4 : PCAt 0x8000b160#64 d4 := by have := L.pc; simp only [Nat.lt_irrefl, ite_false] at this; exact this
  have link : addLink n ra = jal_8000b134_call.link := if_neg (by have := A.nonempty; omega)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (L.ready.gpr_some 10 (by decide) (by decide))
  have saved (off : Nat) (value : BitVec 64) (member : (off, value) ∈ pageAddSlots ra s0 s1 s2 s3) :
      bytesT d4.σ.mem (nativeFrameBase sp 48 + off) 8 = value := by
    have bound : off + 8 ≤ 48 := by simp [pageAddSlots] at member; omega
    rw [word_observed (m := d3.σ.mem) _ fun i hi => L.caller _ (by rw [stackNat]; unfold nativeFrameBase; omega), mem3]
    exact frame48.word_log_read (by intro o w h; simp [pageAddSlots] at h; omega) (by simp [pageAddSlots]) _ member
  -- restore and return
  obtain ⟨d5, run5, p5⟩ := (page_add_return d4 sp ra s0 s1 s2 s3 v (addLink n ra) L.ready.toLeafInput frame48
    ⟨gholds_lookup (n := 2) _ L.regs rfl, hv, trivial⟩ saved A.ready.aligned).run d4 ⟨pc4, rfl⟩
  have mem5 : d5.σ.mem = d4.σ.mem := p5.memory
  refine ⟨d5, run1.trans (run2.trans (run3.trans (run4.trans run5))), {
    pc := p5.pc
    regs := p5.regs
    ready := L.ready.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p5.regs rfl) (gholds_lookup (n := 1) _ p5.regs rfl) A.ready.aligned frame48
      (by simp only [LogInW])
    fields := by rw [mem5]; exact L.fields
    count := by rw [mem5]; exact L.count
    known := fun i hi occupied => by rw [mem5] at occupied ⊢; exact L.known i hi occupied
    present := fun j hj => by rw [mem5]; exact L.present j hj
    kept := fun x hx out => by rw [mem5]; exact L.kept x hx out
    caller := fun x hx => by
      rw [mem5, L.caller x (by rw [stackNat]; omega)]
      exact above3 x hx }⟩
end OCaml.Vm.Boot.Startup
