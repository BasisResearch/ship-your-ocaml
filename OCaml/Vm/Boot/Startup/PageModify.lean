import OCaml.Vm.Boot.Startup.PageModifySteps
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.PageTable
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `caml_page_table_modify(page, 0, kind)` for a page not yet in the table:
the hash, the probe to the first empty slot, the insertion, the return. -/

/-- The page table record and its slots before the insertion. -/
structure PageTableFields (m : Std.ExtHashMap Nat (BitVec 8)) (occ ent : BitVec 64) : Prop where
  size : bytesT m (pageTable + 0) 8 = 2048#64
  shift : read4 m (pageTable + 8) = [53#8, 0#8, 0#8, 0#8]
  mask : bytesT m (pageTable + 0x10) 8 = 2047#64
  occupancy : bytesT m (pageTable + 0x18) 8 = occ
  entries : bytesT m (pageTable + 0x20) 8 = ent

theorem slotAddr_nat (ent : BitVec 64) (i : Nat) (hi : i < 2048) (fits : ent.toNat + 16384 ≤ 2 ^ 64) :
    (slotAddr ent (BitVec.ofNat 64 i)).toNat = ent.toNat + 8 * i := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  simp only [slotAddr, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, p64] at *
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := i * 2 ^ 3) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The allocator's footprint misses a live block of the arena. -/
theorem block_foot_out {H : List (Nat × Nat)} {p n a : Nat} (high : heapStart ≤ p) (owned : (p, n) ∈ H)
    (foot : vsaFoot H a) : a < p ∨ p + n ≤ a := by
  rcases foot with global | ⟨_, _, out⟩
  · left; unfold heapStart at high; unfold allocGlobal InRange at global; omega
  · have := out _ owned; unfold InExt at this; omega

/-- caml_page_table_modify is called to add `page` with `kind`. -/
structure PageModifyCall (H : List (Nat × Nat)) (capacity : Nat) (sp ra page kind s0 s1 s2 s3 s4 occ ent : BitVec 64)
    (c : Config) : Prop where
  pc : PCAt 0x8000ada4#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, page), (11, 0#64), (12, kind), (8, s0), (9, s1), (18, s2), (19, s3),
    (20, s4)]
  ready : RuntimeReady H capacity sp ra c
  frame : NativeFrame sp 96
  fields : PageTableFields c.σ.mem occ ent
  room : guardB bop.BGEU (occ <<< 1) 2048#64 = false
  /-- An empty slot. -/
  hole : ∃ e, e < 2048 ∧ slotWord c.σ.mem ent e = 0#64
  windows : ∀ i, i < 2048 → WriteWindow (slotAddr ent (BitVec.ofNat 64 i)) 8
  /-- The slots lie in the arena. -/
  tableLow : ent.toNat + 16384 ≤ heapEnd
  tableHigh : heapStart ≤ ent.toNat
  /-- The slots are a live block. -/
  tableOwned : (ent.toNat, 16384) ∈ H
  /-- The page is not in the table yet. -/
  absent : ∀ i, i < 2048 → slotWord c.σ.mem ent i ≠ 0#64 →
    guardB bop.BGEU (page ^^^ slotWord c.σ.mem ent i) 4096#64 = true

/-- The page went into slot `slot`, `steps` probes from its home slot. -/
structure PageModified (H : List (Nat × Nat)) (capacity : Nat) (sp ra page kind s0 s1 s2 s3 s4 occ ent : BitVec 64)
    (slot steps : Nat) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (10, 0#64), (20, s4), (19, s3), (18, s2), (9, s1), (8, s0), (1, ra)]
  ready : RuntimeReady H capacity sp ra after
  at_slot : slot = probe (pageHash page).toNat steps
  empty : slotWord before.σ.mem ent slot = 0#64
  occupied : ∀ i, i < steps → slotWord before.σ.mem ent (probe (pageHash page).toNat i) ≠ 0#64
  /-- s4–s11 are the caller's. -/
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  memory : after.σ.mem = writeLog (writeLog before.σ.mem (pageModifyLog sp ra s0 s1 s2 s3 s4))
    [((slotAddr ent (BitVec.ofNat 64 slot)).toNat, 8, kind ||| page), (pageTable + 0x18, 8, occ + 1#64)]

theorem page_table_modify_insert (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra page kind s0 s1 s2 s3 s4 occ ent : BitVec 64)
    (A : PageModifyCall H capacity sp ra page kind s0 s1 s2 s3 s4 occ ent c) :
    ∃ slot steps after, Steps c after ∧ PageModified H capacity sp ra page kind s0 s1 s2 s3 s4 occ ent slot steps c after := by
  have regs := A.regs
  obtain ⟨d1, run1, p1⟩ := (page_modify_save c sp ra s0 s1 s2 s3 s4 A.ready.toLeafInput A.frame page
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 8) _ regs rfl, gholds_lookup (n := 9) _ regs rfl,
      gholds_lookup (n := 18) _ regs rfl, gholds_lookup (n := 19) _ regs rfl, gholds_lookup (n := 20) _ regs rfl,
      gholds_lookup (n := 1) _ regs rfl, gholds_lookup (n := 10) _ regs rfl, trivial⟩).run c ⟨A.pc, rfl⟩
  have keep1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [2]) : gprGet d1.σ n = gprGet c.σ n :=
    p1.toEffectPost.gpr_frame (by decide) n lo hi out
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) A.ready.aligned A.frame
    (pageModifyLog_inside A.frame)
  -- the record is a global: the saves miss it
  have lower := A.frame.lower
  have global (x : Nat) (hx : x < heapEnd) : (d1.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ (pageModifyLog_inside A.frame) x ⟨Or.inl (by simp only [nativeFrameBase]; omega), trivial⟩]
  have ptLow : pageTable + 0x28 ≤ heapEnd := by decide
  have word1 (off : Nat) (hoff : off + 8 ≤ 0x28) : bytesT d1.σ.mem (pageTable + off) 8 = bytesT c.σ.mem (pageTable + off) 8 :=
    word_observed _ fun i hi => global _ (by omega)
  obtain ⟨d2, run2, p2⟩ := (page_record_load d1 ra page occ 2048#64 ent ready1.toLeafInput
    ⟨gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩
    (by rw [word1 0x18 (by decide)]; exact A.fields.occupancy) (by rw [word1 0 (by decide)]; exact A.fields.size)
    (by rw [word1 0x20 (by decide)]; exact A.fields.entries)).run d1 ⟨p1.pc, rfl⟩
  have mem2 : d2.σ.mem = d1.σ.mem := p2.memory
  obtain ⟨d3, run3, p3⟩ := (page_shift_check d2 ra 0#64 kind (occ <<< 1) 2048#64 p2.toLeafInput
    ⟨p2.keep 11 (by decide) (by decide) (by decide) (by decide) ((keep1 11 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 11) _ regs rfl)),
      p2.keep 12 (by decide) (by decide) (by decide) (by decide) ((keep1 12 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 12) _ regs rfl)),
      gholds_lookup (n := 10) _ p2.regs rfl, gholds_lookup (n := 15) _ p2.regs rfl, trivial⟩
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => by rw [mem2]; exact global _ (by omega)]
        exact A.fields.shift) A.room).run d2 ⟨p2.pc, rfl⟩
  obtain ⟨d4, run4, p4⟩ := (page_hash_chain d3 ra page p3.toLeafInput
    ⟨p3.keep 8 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p2.regs rfl), trivial⟩).run d3
    ⟨p3.pc, rfl⟩
  have mem4 : d4.σ.mem = d1.σ.mem := p4.memory.trans (p3.memory.trans mem2)
  have fits : ent.toNat + 16384 ≤ 2 ^ 64 := by have := A.tableLow; unfold heapEnd at this; omega
  have slot1 (i : Nat) (hi : i < 2048) : slotWord d1.σ.mem ent i = slotWord c.σ.mem ent i :=
    word_observed _ fun k hk => global _ (by rw [slotAddr_nat ent i hi fits]; have := A.tableLow; omega)
  have h0 := (pageHash page).toNat
  have hh0 : BitVec.ofNat 64 (pageHash page).toNat = pageHash page := by simp
  have h0lt := pageHash_lt page
  let empty := slotWord c.σ.mem ent (pageHash page).toNat == 0#64
  obtain ⟨d5, run5, p5⟩ := (page_slot d4 ra page ent empty p4.toLeafInput
    ⟨gholds_lookup (n := 15) _ p4.regs rfl,
      p4.keep 18 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p3.regs rfl),
      p4.keep 13 (by decide) (by decide) (by decide) (by decide)
        (p3.keep 13 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 13) _ p2.regs rfl)), trivial⟩
    (by rw [← hh0]; exact (A.windows _ h0lt).read)
    (by rw [mem4]; have := slot1 _ h0lt; unfold slotWord at this; rw [hh0] at this; rw [this]
        show _ = (slotWord c.σ.mem ent (pageHash page).toNat == 0#64); unfold slotWord; rw [hh0])).run d4 ⟨p4.pc, rfl⟩
  have mem5 : d5.σ.mem = d1.σ.mem := p5.memory.trans mem4
  have slot5 (i : Nat) (hi : i < 2048) : slotWord d5.σ.mem ent i = slotWord c.σ.mem ent i := by
    rw [mem5]; exact slot1 i hi
  have probe0 : probe (pageHash page).toNat 0 = (pageHash page).toNat := by unfold probe; omega
  -- to the insertion: the first empty slot on the probe path
  have found : ∃ g slot steps, Steps d5 g ∧ slot = probe (pageHash page).toNat steps ∧
      slotWord c.σ.mem ent slot = 0#64 ∧
      (∀ i, i < steps → slotWord c.σ.mem ent (probe (pageHash page).toNat i) ≠ 0#64) ∧
      BoundaryPost [15, 11, 10, 12, 14, 17, 16] d5 ra 0x8000aee4#64
        [(12, slotAddr ent (BitVec.ofNat 64 slot)), (8, page), (13, ent)] g := by
    by_cases isEmpty : slotWord c.σ.mem ent (pageHash page).toNat = 0#64
    · have et : empty = true := by simp [empty, isEmpty]
      refine ⟨d5, (pageHash page).toNat, 0, .refl _, probe0.symm, isEmpty, fun i hi => absurd hi (by omega), ?_⟩
      have pc5 := p5.pc
      rw [et] at pc5
      exact { p5.toLeafInput with
        pc := pc5
        regs := ⟨by rw [hh0]; exact gholds_lookup (n := 12) _ p5.regs rfl,
          p5.keep 8 (by decide) (by decide) (by decide) (by decide)
            (p4.keep 8 (by decide) (by decide) (by decide) (by decide)
              (p3.keep 8 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p2.regs rfl))),
          gholds_lookup (n := 13) _ p5.regs rfl, trivial⟩
        memory := rfl
        output := rfl
        frame := fun _ _ _ => rfl
        kept := GprsKept.refl _ }
    · have ef : empty = false := by simp [empty, isEmpty]
      have pc5 := p5.pc
      rw [ef] at pc5
      have reg9 : gprGet d5.σ 9 = some (BitVec.ofNat 64 pageTable) :=
        p5.keep 9 (by decide) (by decide) (by decide) (by decide)
          (p4.keep 9 (by decide) (by decide) (by decide) (by decide)
            (p3.keep 9 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p2.regs rfl)))
      obtain ⟨d6, run6, p6⟩ := (page_probe_init d5 ra 2047#64 p5.toLeafInput ⟨reg9, trivial⟩ (by
        rw [word_observed (m := c.σ.mem) _ fun i hi => by rw [mem5]; exact global _ (by omega)]
        exact A.fields.mask)).run d5 ⟨pc5, rfl⟩
      have start : ProbeAt d5 ra page ent (pageHash page).toNat 0 d6 := {
        post := { BoundaryPost.widen p6 (by decide) with
          regs := ⟨by
              rw [probe0, hh0]
              exact p6.keep 15 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 15) _ p5.regs rfl),
            by
              rw [probe0, slot5 _ h0lt]
              refine p6.keep 14 (by decide) (by decide) (by decide) (by decide) ?_
              rw [gholds_lookup (n := 14) _ p5.regs rfl]
              unfold slotWord; rw [hh0, mem4]
              have := slot1 _ h0lt; unfold slotWord at this; rw [hh0] at this; rw [this],
            gholds_lookup (n := 17) _ p6.regs rfl, gholds_lookup (n := 16) _ p6.regs rfl,
            p6.keep 8 (by decide) (by decide) (by decide) (by decide)
              (p5.keep 8 (by decide) (by decide) (by decide) (by decide)
                (p4.keep 8 (by decide) (by decide) (by decide) (by decide)
                  (p3.keep 8 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p2.regs rfl)))),
            p6.keep 13 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 13) _ p5.regs rfl),
            trivial⟩ }
        occupied := fun i hi => by
          rw [show i = 0 by omega, probe0, slot5 _ h0lt]; exact isEmpty }
      obtain ⟨e, he, hole⟩ := A.hole
      obtain ⟨f, slot, steps, run, F⟩ := page_probe_loop d5 ra page ent (pageHash page).toNat e h0lt he
        (by rw [slot5 _ he]; exact hole) (fun i hi => (A.windows i hi).read)
        (fun i hi occ => by rw [slot5 _ hi] at occ ⊢; exact A.absent i hi occ) d6 start
      have slotLt : slot < 2048 := by rw [F.at_slot]; exact probe_lt _ _
      exact ⟨f, slot, steps, run6.trans run, F.at_slot, by rw [← slot5 _ slotLt]; exact F.empty,
        fun i hi => by rw [← slot5 _ (probe_lt _ _)]; exact F.occupied i hi, F.post⟩
  obtain ⟨g, slot, steps, runG, atSlot, emptySlot, occupiedPath, PG⟩ := found
  have slotLt : slot < 2048 := by rw [atSlot]; exact probe_lt _ _
  have memG : g.σ.mem = d1.σ.mem := PG.memory.trans mem5
  have reg10 : (gprGet d5.σ 10).isSome := by
    rw [p5.keep 10 (by decide) (by decide) (by decide) (by decide)
      (p4.keep 10 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 10) _ p3.regs rfl))]
    rfl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (PG.kept.present 10 (by decide) (by decide) reg10)
  have keepG (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [15, 11, 10, 12, 14, 17, 16]) (w : BitVec 64)
      (h : gprGet d5.σ k = some w) : gprGet g.σ k = some w := PG.keep k lo hi (by decide) out h
  have slotAddrNat := slotAddr_nat ent slot slotLt fits
  have text : Image.textBase + Image.textSize ≤ pageTable := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ pageTable := by decide
  have ptStart : pageTable + 0x28 ≤ heapStart := by decide
  have readyG : RuntimeReady H capacity (nativeStack sp 96) ra g :=
    ((((ready1.boundary p2 (by decide) (by decide) (by decide)).boundary p3 (by decide) (by decide) (by decide)).boundary
      p4 (by decide) (by decide) (by decide)).boundary p5 (by decide) (by decide) (by decide)).boundary PG (by decide)
      (by decide) (by decide)
  obtain ⟨d7, run7, p7⟩ := (page_insert g ra page kind (slotAddr ent (BitVec.ofNat 64 slot)) occ v PG.toLeafInput
    ⟨keepG 9 (by decide) (by decide) (by decide) _
        (p5.keep 9 (by decide) (by decide) (by decide) (by decide)
          (p4.keep 9 (by decide) (by decide) (by decide) (by decide)
            (p3.keep 9 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p2.regs rfl)))),
      keepG 19 (by decide) (by decide) (by decide) _
        (p5.keep 19 (by decide) (by decide) (by decide) (by decide)
          (p4.keep 19 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ p3.regs rfl))),
      gholds_lookup (n := 8) _ PG.regs rfl, gholds_lookup (n := 12) _ PG.regs rfl, hv, trivial⟩
    (A.windows slot slotLt)
    (by rw [word_observed (m := c.σ.mem) _ fun i hi => by rw [memG]; exact global _ (by omega)]
        exact A.fields.occupancy)
    (by
      have := A.tableHigh
      constructor <;> simp only [OutLRange, and_true, slotAddrNat] <;> refine ⟨?_, ?_⟩ <;> omega)).run g ⟨PG.pc, rfl⟩
  -- registers the body never wrote
  have through (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (w : BitVec 64)
      (out : k ∉ [2, 9, 14, 15, 8, 10, 13, 18, 20, 19, 12, 11, 17, 16]) (h : gprGet c.σ k = some w) :
      gprGet d7.σ k = some w := by
    have o (l : List Nat) (sub : ∀ n ∈ l, n ∈ [2, 9, 14, 15, 8, 10, 13, 18, 20, 19, 12, 11, 17, 16]) : k ∉ l :=
      fun m => out (sub k m)
    refine (p7.toEffectPost.gpr_frame (by decide) k lo hi (o _ (by decide))).trans ?_
    refine PG.keep k lo hi (by decide) (o _ (by decide)) ?_
    refine p5.keep k lo hi (by decide) (o _ (by decide)) ?_
    refine p4.keep k lo hi (by decide) (o _ (by decide)) ?_
    refine p3.keep k lo hi (by decide) (o _ (by decide)) ?_
    refine p2.keep k lo hi (by decide) (o _ (by decide)) ?_
    exact (keep1 k lo hi (o _ (by decide))).trans h
  have stack7 : gprGet d7.σ 2 = some (nativeStack sp 96) := by
    refine (p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ?_
    refine PG.keep 2 (by decide) (by decide) (by decide) (by decide) ?_
    refine p5.keep 2 (by decide) (by decide) (by decide) (by decide) ?_
    refine p4.keep 2 (by decide) (by decide) (by decide) (by decide) ?_
    refine p3.keep 2 (by decide) (by decide) (by decide) (by decide) ?_
    refine p2.keep 2 (by decide) (by decide) (by decide) (by decide) ?_
    exact gholds_lookup (n := 2) _ p1.regs rfl
  have mem7 : d7.σ.mem = writeLog d1.σ.mem
      [((slotAddr ent (BitVec.ofNat 64 slot)).toNat, 8, kind ||| page), (pageTable + 0x18, 8, occ + 1#64)] := by
    rw [p7.memory, memG]
  have windowsIn : LogInW [⟨pageTable, pageTable + 0x28⟩, ⟨ent.toNat, ent.toNat + 16384⟩]
      [((slotAddr ent (BitVec.ofNat 64 slot)).toNat, 8, kind ||| page), (pageTable + 0x18, 8, occ + 1#64)] := by
    simp only [LogInW, InsideW, slotAddrNat]
    refine ⟨Or.inr (Or.inl ⟨by omega, by omega⟩), Or.inl ⟨by omega, by omega⟩, trivial⟩
  have ready7 : RuntimeReady H capacity (nativeStack sp 96) ra d7 :=
    readyG.window_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
      ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans readyG.stack)
      ((p7.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans readyG.raReg)
      readyG.aligned windowsIn
      (fun pin member => ⟨(pageTableWindows_out_pins pin member).1,
        (arenaWindow_out_pins (n := 16384) A.tableHigh pin member).1, trivial⟩)
      (by have := A.tableHigh; unfold heapStart at this
          simp only [OutWRange, and_true, pageTable, Layout.sym_caml_page_table, Layout.sym_Caml_state]; omega)
      (by have := A.tableHigh; unfold heapStart at this
          simp only [OutWRange, and_true, pageTable, Layout.sym_caml_page_table, Layout.sym_pool]; omega)
      (fun a foot => ⟨(pageTableWindows_out_foot foot).1, block_foot_out A.tableHigh A.tableOwned foot, trivial⟩)
  obtain ⟨d8, run8, p8⟩ := (page_modify_return d7 sp ra s0 s1 s2 s3 s4 v ra
    ⟨p7.good, p7.image, p7.minstret, through 1 (by decide) (by decide) ra (by decide)
      (gholds_lookup (n := 1) _ regs rfl), A.ready.aligned, p7.tick⟩ A.frame
    ⟨stack7, gholds_lookup (n := 10) _ p7.regs rfl, trivial⟩
    (fun off value member => by
      have range : off + 8 ≤ 96 := by
        simp only [pageModifySlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      rw [mem7, bytesT_writeLog_out _ (by
          have := A.tableLow
          simp only [OutLRange, and_true, slotAddrNat, nativeFrameBase]
          refine ⟨?_, ?_⟩ <;> omega), p1.memory]
      exact A.frame.word_log_read (fun off value member => by
          simp only [pageModifySlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega)
        (by simp [pageModifySlots]) _ member)
    A.ready.aligned).run d7 ⟨p7.pc, rfl⟩
  exact ⟨slot, steps, d8, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (runG.trans (run7.trans run8)))))),
    { pc := p8.pc
      regs := p8.regs
      ready := ready7.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
        (gholds_lookup (n := 2) _ p8.regs rfl) (gholds_lookup (n := 1) _ p8.regs rfl) A.ready.aligned A.frame
        (by simp only [LogInW])
      at_slot := atSlot
      empty := emptySlot
      occupied := occupiedPath
      saved := fun k lo hi27 => by
        have hi : k ≤ 31 := by omega
        by_cases h20 : k = 20
        · subst h20; rw [gholds_lookup (n := 20) _ p8.regs rfl, gholds_lookup (n := 20) _ A.regs rfl]
        · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (A.ready.gpr_some k (by omega) hi)
          have out (L : List Nat) (low : ∀ m ∈ L, m ≤ 20) : k ∉ L := fun mem => by have := low k mem; omega
          rw [hw]
          refine (p8.toEffectPost.gpr_frame (by decide) k (by omega) hi (out _ (by decide))).trans
            ((p7.toEffectPost.gpr_frame (by decide) k (by omega) hi (out _ (by decide))).trans ?_)
          exact PG.keep k (by omega) hi (by decide) (out _ (by decide))
            (p5.keep k (by omega) hi (by decide) (out _ (by decide))
              (p4.keep k (by omega) hi (by decide) (out _ (by decide))
                (p3.keep k (by omega) hi (by decide) (out _ (by decide))
                  (p2.keep k (by omega) hi (by decide) (out _ (by decide))
                    ((p1.toEffectPost.gpr_frame (by decide) k (by omega) hi (out _ (by decide))).trans hw)))))
      memory := by rw [p8.memory, show writeLog d7.σ.mem [] = d7.σ.mem from rfl, mem7, p1.memory] }⟩
end OCaml.Vm.Boot.Startup
