import OCaml.Vm.Boot.Startup.PageTableSteps
import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Boot.Startup.MemsetWords
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.ReadyPerm
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `caml_page_table_initialize(0x2f8000)` from caml_init_gc: 2048 entries,
shift 53, mask 2047, no occupancy, and a fresh cleared 16 KB table. -/

/-- The `caml_page_table` record. -/
def pageTableWindows : List W := [⟨pageTable, pageTable + 0x28⟩]

theorem pageTableWindows_out_pins (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) :
    OutW pageTableWindows pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  simp only [OutW, pageTableWindows, and_true]
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, pageTable,
    Layout.sym_caml_page_table] at * <;> omega

theorem pageTableWindows_out_foot {H : List (Nat × Nat)} {a : Nat} (foot : vsaFoot H a) :
    OutW pageTableWindows a := by
  simp only [OutW, pageTableWindows, and_true, pageTable, Layout.sym_caml_page_table]
  rcases foot with global | ⟨lo, _, _⟩
  · unfold allocGlobal InRange at global; omega
  · unfold heapStart at lo; omega

theorem RuntimeReadyL.pageTable_log {live : Nat → Prop} {H capacity oldsp oldra before after writes log pc value regs sp ra}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (inside : LogInW pageTableWindows log) : RuntimeReadyL live H capacity sp ra after :=
  ready.window_log post keys cover gpFrame stack link aligned inside pageTableWindows_out_pins
    ⟨Or.inl (by decide), trivial⟩ ⟨Or.inl (by decide), trivial⟩ (fun _ foot => pageTableWindows_out_foot foot)

theorem below_alloc_frame {x s : Nat} (h : x < s - (32 + allocHeadroom)) : x < s - 32 - allocHeadroom := by
  omega

/-- caml_init_gc calls `caml_page_table_initialize(0x2f8000)`. -/
structure PageTableCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x8000acdc#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, 0x2f8000#64)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (32 + allocHeadroom)
  charged : vsaChg 16384 charge

/-- `caml_page_table` after initialization: 2048 entries over the cleared
table `blk`. -/
structure PageTableAt (m : Std.ExtHashMap Nat (BitVec 8)) (blk : BitVec 64) : Prop where
  size : bytesT m pageTable 8 = 2048#64
  shift : read4 m (pageTable + 8) = [53#8, 0#8, 0#8, 0#8]
  mask : bytesT m (pageTable + 0x10) 8 = 2047#64
  occupancy : bytesT m (pageTable + 0x18) 8 = 0#64
  entries : bytesT m (pageTable + 0x20) 8 = blk
  cleared : ∀ k, k < 16384 → (m[blk.toNat + k]?).getD 0 = 0

/-- caml_page_table_initialize returned 0. -/
structure PageTableDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra blk : BitVec 64) (before after : Config) :
    Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (1, ra), (10, 0#64)]
  ready : RuntimeReady ((blk.toNat, 16384) :: H) capacity sp ra after
  fresh : FreshBlock vsaLayoutP H blk.toNat 16384
  table : PageTableAt after.σ.mem blk
  /-- Memory below the frame outside the allocator and the record. -/
  kept : ∀ x, x < sp.toNat - (32 + allocHeadroom) → ¬ vsaFoot H x → OutW pageTableWindows x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  caller : ∀ x, sp.toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem page_table_initialize (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra : BitVec 64)
    (A : PageTableCall H capacity charge sp ra c) :
    ∃ blk after, Steps c after ∧ PageTableDone H capacity sp ra blk c after := by
  have frame32 : NativeFrame sp 32 := A.frame.resize (by decide) (by decide)
  have regs := A.regs
  have frameA : NativeFrame (nativeStack sp 32) allocHeadroom := A.frame.nested (front := 32) (by decide)
  have frameIn : NativeFrame (nativeStack sp 32) 32 := frameA.resize (by decide) (by decide)
  obtain ⟨d1, run1, p1⟩ := (page_table_save c sp ra A.ready.toLeafInput frame32 0x2f8000#64 1520#64
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 1) _ regs rfl, gholds_lookup (n := 10) _ regs rfl,
      trivial⟩ page_table_pages).run c ⟨A.pc, rfl⟩
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) A.ready.aligned frame32
    (frame32.word_log_inside fun off value member => by simp at member; omega)
  obtain ⟨d2, run2, p2⟩ := (page_table_top d1 ra 1520#64 ready1.toLeafInput
    ⟨gholds_lookup (n := 12) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have ready2 := ready1.pageTable_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready1.stack)
    ((p2.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready1.raReg)
    A.ready.aligned (by simp only [LogInW, InsideW, pageTableWindows]; decide)
  obtain ⟨d3, run3, p3⟩ := (page_table_shift d2 ra 1520#64 ready2.toLeafInput
    ⟨(p2.toEffectPost.gpr_frame (by decide) 15 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 15) _ p1.regs rfl), gholds_lookup (n := 12) _ p2.regs rfl,
      gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩ (by decide)).run d2 ⟨p2.pc, rfl⟩
  have ready3 := ready2.pageTable_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready2.stack)
    ((p3.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready2.raReg)
    A.ready.aligned (by simp only [LogInW, InsideW, pageTableWindows]; decide)
  obtain ⟨d4, run4, D⟩ := page_table_doubling_loop frameIn (start := d3) {
    pc := p3.pc
    regs := ⟨gholds_lookup (n := 12) _ p3.regs rfl, gholds_lookup (n := 15) _ p3.regs rfl,
      gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩
    shift := fun h => absurd h (by decide)
    ready := ready3
    bound := by decide
    mem := rfl }
  have pc4 : PCAt 0x8000ad1c#64 d4 := by have := D.pc; simp only [Nat.lt_irrefl, ite_false] at this; exact this
  obtain ⟨d5, run5, p5⟩ := (page_table_fields d4 ra D.ready.toLeafInput
    ⟨gholds_lookup (n := 12) _ D.regs rfl, D.shift (by decide), gholds_lookup (n := 10) _ D.regs rfl, trivial⟩).run d4
    ⟨pc4, rfl⟩
  have ready5 := D.ready.pageTable_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans D.ready.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans D.ready.raReg)
    A.ready.aligned (by simp only [pageTableFieldsLog, LogInW, InsideW, pageTableWindows]; decide)
  -- caml_stat_alloc_noexc(16384)
  obtain ⟨d6, run6, p6⟩ := (page_table_alloc_call d5 sp ra ready5.toLeafInput frame32
    ⟨gholds_lookup (n := 12) _ p5.regs rfl, ready5.stack, trivial⟩).run d5 ⟨p5.pc, rfl⟩
  have ready6 := ready5.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p6.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready5.stack)
    (gholds_lookup (n := 1) _ p6.regs rfl) (by decide) frame32
    (frame32.word_log_inside fun off value member => by simp at member; omega)
  obtain ⟨d7, run7, ⟨B⟩⟩ := (stat_alloc_ready d6 H capacity charge 16384#64 _ _ ready6 frameA
    (gholds_lookup (n := 10) _ p6.regs rfl) A.charged).run d6 ⟨p6.pc, rfl⟩
  have fresh : FreshBlock vsaLayoutP H (vsaReg d7 10).toNat 16384 := B.allocation.result.fresh
  have align : (vsaReg d7 10).toNat % 16 = 0 := B.allocation.result.align
  have pReg : gprGet d7.σ 10 = some (vsaReg d7 10) := library_gpr B.ready.platform (by decide) (by decide) rfl
  have ready7 : RuntimeReady (((vsaReg d7 10).toNat, 16384) :: H) capacity (nativeStack sp 32) jal_8000ad4c_call.link
    d7 := B.ready
  generalize hblk : vsaReg d7 10 = blk at fresh align pReg ready7
  have blkLo : heapStart ≤ blk.toNat := fresh.2.1
  have blkHi : blk.toNat + 16384 ≤ heapEnd := fresh.2.2.1
  have base0 : nativeFrameBase sp 32 = sp.toNat - 32 := rfl
  have spLow : heapEnd + 32 + allocHeadroom ≤ sp.toNat := A.frame.lower
  -- the size slot survives the allocation
  have size7 : bytesT d7.σ.mem (nativeFrameBase sp 32 + 0) 8 = 16384#64 := by
    rw [word_observed (m := d6.σ.mem) _ (fun i _ => B.caller_byte frameA (by
      rw [show (nativeStack sp 32).toNat = sp.toNat - 32 from frame32.stack_nat]; unfold nativeFrameBase; omega)),
      p6.memory]
    exact frame32.word_log_read (slots := [(0, 16384#64)]) (by simp) (by simp) _ (by simp)
  -- memset(blk, 0, 16384)
  obtain ⟨d8, run8, p8⟩ := (page_table_clear_call d7 sp jal_8000ad4c_call.link blk ready7.toLeafInput frame32
    ⟨pReg, ready7.stack, trivial⟩ (fun h => fresh.1 (by rw [h]; rfl)) size7).run d7
    ⟨by rw [← hblk] at *; exact library_pc B.allocation.good B.allocation.result.frame.pc, rfl⟩
  have ready8 := ready7.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p8.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack)
    (gholds_lookup (n := 1) _ p8.regs rfl) (by decide) frame32
    (frame32.word_log_inside fun off value member => by simp at member; omega)
  have region : ZeroPairRegion blk.toNat 1024 := ⟨blkLo, by omega, align⟩
  have ofNatBlk : BitVec.ofNat 64 blk.toNat = blk := by simp
  obtain ⟨d9, run9, M⟩ := (memset_words d8 blk.toNat 1024 16384#64 jal_8000ad68_call.link region (by decide)
    { toLeafInput := ready8.toLeafInput
      pointer := by rw [ofNatBlk]; exact gholds_lookup (n := 10) _ p8.regs rfl
      zero := gholds_lookup (n := 11) _ p8.regs rfl
      size := gholds_lookup (n := 12) _ p8.regs rfl
      alignedPointer := by rw [ofNatBlk]; exact align
      big := by decide } (by decide) (by decide)).run d8 ⟨p8.pc, rfl⟩
  have keepM (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [6, 14, 15, 13, 12]) : gprGet d9.σ n = gprGet d8.σ n :=
    M.toEffectPost.gpr_frame (by decide) n lo hi out
  have ready9 := ready8.clear M (by decide) (by simp only [memsetWordsRegs, keysG]; decide) (by decide)
    ((keepM 2 (by decide) (by decide) (by decide)).trans ready8.stack)
    ((keepM 1 (by decide) (by decide) (by decide)).trans ready8.raReg) ready8.aligned (List.mem_cons_self ..)
    blkLo (by decide)
  -- one-slot logs leave the rest of memory alone
  have slot (m : Std.ExtHashMap Nat (BitVec 8)) (off : Nat) (v : BitVec 64) (bound : off + 8 ≤ 32) (x : Nat)
      (out : x < nativeFrameBase sp 32 + off ∨ nativeFrameBase sp 32 + off + 8 ≤ x) :
      ((writeLog m (nativeWordLog sp 32 [(off, v)]))[x]?).getD 0 = (m[x]?).getD 0 := by
    rw [frame32.word_log_slots (fun o w h => by simp at h; omega), writeLog_out _ _ _ (by
      simp only [List.map, OutL, and_true]; omega)]
  have ptOut (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (inside : LogInW pageTableWindows log) (x : Nat)
      (out : OutW pageTableWindows x) : ((writeLog m log)[x]?).getD 0 = (m[x]?).getD 0 := by
    rw [frameOn_writeLog _ _ _ inside x out]
  have ptIn2 : LogInW pageTableWindows [(pageTable + 0, 8, 1#64)] := by
    simp only [LogInW, InsideW, pageTableWindows]; decide
  have ptIn3 : LogInW pageTableWindows [(pageTable + 8, 4, 64#64)] := by
    simp only [LogInW, InsideW, pageTableWindows]; decide
  have ptIn5 : LogInW pageTableWindows pageTableFieldsLog := by
    simp only [pageTableFieldsLog, LogInW, InsideW, pageTableWindows]; decide
  -- through the geometry stores: only the record changes
  have geo (x : Nat) (out : OutW pageTableWindows x) : (d5.σ.mem[x]?).getD 0 = (d1.σ.mem[x]?).getD 0 := by
    rw [p5.memory, ptOut _ _ ptIn5 x out, D.mem, p3.memory, ptOut _ _ ptIn3 x out, p2.memory, ptOut _ _ ptIn2 x out]
  have ptLow : pageTable + 0x28 ≤ heapStart := by decide
  have blkOut (x : Nat) (out : x < blk.toNat ∨ blk.toNat + 16384 ≤ x) (m : Std.ExtHashMap Nat (BitVec 8)) :
      ((clearWords m blk.toNat (2 * 1024))[x]?).getD 0 = (m[x]?).getD 0 := by
    rcases out with lo | hi
    · rw [clearWords_below _ _ _ _ lo]
    · rw [clearWords_above _ _ _ _ (by omega)]
  have spNat : (nativeStack sp 32).toNat = sp.toNat - 32 := frame32.stack_nat
  have backTo1 (x : Nat) (blkO : x < blk.toNat ∨ blk.toNat + 16384 ≤ x)
      (s8 : x < nativeFrameBase sp 32 + 8 ∨ nativeFrameBase sp 32 + 8 + 8 ≤ x)
      (s0 : x < nativeFrameBase sp 32 + 0 ∨ nativeFrameBase sp 32 + 0 + 8 ≤ x)
      (alloc : (x < sp.toNat - 32 - allocHeadroom ∧ ¬ vsaFoot H x) ∨ sp.toNat - 32 ≤ x)
      (pt : OutW pageTableWindows x) : (d9.σ.mem[x]?).getD 0 = (d1.σ.mem[x]?).getD 0 := by
    rw [M.memory, blkOut x blkO, p8.memory, slot _ 8 blk (by decide) x s8]
    rw [show (d7.σ.mem[x]?).getD 0 = (d6.σ.mem[x]?).getD 0 by
      rcases alloc with ⟨low, foot⟩ | high
      · exact B.kept_byte (by rw [spNat]; exact low) foot
      · exact B.caller_byte frameA (by rw [spNat]; exact high)]
    rw [p6.memory, slot _ 0 _ (by decide) x s0, geo x pt]
  have stackPt (x : Nat) (hx : sp.toNat - 32 ≤ x) : OutW pageTableWindows x := by
    simp only [OutW, pageTableWindows, and_true]; unfold heapStart at ptLow; unfold heapEnd at spLow; omega
  have stackBlk (x : Nat) (hx : sp.toNat - 32 ≤ x) : x < blk.toNat ∨ blk.toNat + 16384 ≤ x := by
    unfold heapEnd at spLow blkHi; omega
  -- return
  obtain ⟨d10, run10, p10⟩ := (page_table_return d9 sp ra blk (BitVec.ofNat 64 blk.toNat) jal_8000ad68_call.link
    ready9.toLeafInput frame32 ⟨ready9.stack, M.result, trivial⟩
    (by
      rw [word_observed (m := d8.σ.mem) _ fun i hi => by
        rw [M.memory, blkOut _ (stackBlk _ (by unfold nativeFrameBase; omega))], p8.memory]
      exact frame32.word_log_read (slots := [(8, blk)]) (by simp) (by simp) _ (by simp))
    (by
      rw [word_observed (m := d1.σ.mem) _ fun i hi => backTo1 _ (stackBlk _ (by unfold nativeFrameBase; omega))
        (Or.inr (by unfold nativeFrameBase; omega)) (Or.inr (by unfold nativeFrameBase; omega))
        (Or.inr (by unfold nativeFrameBase; omega)) (stackPt _ (by unfold nativeFrameBase; omega)), p1.memory]
      exact frame32.word_log_read (slots := [(24, ra)]) (by simp) (by simp) _ (by simp))
    A.ready.aligned).run d9 ⟨M.pc, rfl⟩
  have ptIn10 : LogInW pageTableWindows [(pageTable + 0x20, 8, blk)] := by
    simp only [LogInW, InsideW, pageTableWindows]; decide
  have mem10 (x : Nat) (out : x < pageTable + 0x20 ∨ pageTable + 0x28 ≤ x) :
      (d10.σ.mem[x]?).getD 0 = (d9.σ.mem[x]?).getD 0 := by
    rw [p10.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; omega)]
  have ptFoot (x : Nat) (lo : pageTable ≤ x) (hi : x < pageTable + 0x28) : ¬ vsaFoot H x := fun foot => by
    have := pageTableWindows_out_foot foot
    simp only [OutW, pageTableWindows, and_true] at this; omega
  -- the record's bytes after the geometry stores
  have backTo5 (x : Nat) (lo : pageTable ≤ x) (hi : x < pageTable + 0x28) :
      (d9.σ.mem[x]?).getD 0 = (d5.σ.mem[x]?).getD 0 := by
    unfold heapStart at ptLow blkLo; unfold heapEnd at spLow
    rw [M.memory, blkOut x (Or.inl (by omega)), p8.memory, slot _ 8 blk (by decide) x (Or.inl (by
      unfold nativeFrameBase; omega)), B.kept_byte (by rw [spNat]; omega) (ptFoot x lo hi), p6.memory,
      slot _ 0 _ (by decide) x (Or.inl (by unfold nativeFrameBase; omega))]
  have word10 (off : Nat) (hoff : off + 8 ≤ 0x20) :
      bytesT d10.σ.mem (pageTable + off) 8 = bytesT d5.σ.mem (pageTable + off) 8 :=
    word_observed _ fun i hi => by rw [mem10 _ (Or.inl (by omega)), backTo5 _ (by omega) (by omega)]
  have fieldsSplit : pageTableFieldsLog = [] ++ (pageTable + 8, 4, 53#64) ::
      [(pageTable + 0, 8, 2048#64), (pageTable + 0x18, 8, 0#64), (pageTable + 0x10, 8, 2047#64)] := rfl
  refine ⟨blk, d10, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans run10)))))))), {
    pc := p10.pc
    regs := ⟨gholds_lookup (n := 2) _ p10.regs rfl, gholds_lookup (n := 1) _ p10.regs rfl,
      gholds_lookup (n := 10) _ p10.regs rfl, trivial⟩
    ready := ready9.pageTable_log p10 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p10.regs rfl) (gholds_lookup (n := 1) _ p10.regs rfl) A.ready.aligned ptIn10
    fresh := fresh
    table := {
      size := by
        rw [show pageTable = pageTable + 0 from rfl, word10 0 (by decide), p5.memory]
        exact word_writeLog_at d4.σ.mem pageTableFieldsLog 1 (pageTable + 0) _ rfl (by
          simp only [pageTableFieldsLog, List.drop, OutLRange, and_true]; omega)
      shift := by
        rw [read4_observed (m := d5.σ.mem) _ fun k hk => by rw [mem10 _ (Or.inl (by omega)),
          backTo5 _ (by omega) (by omega)], p5.memory, fieldsSplit]
        obtain ⟨b0, b1, b2, b3⟩ := pin4_of_writeLog d4.σ.mem []
          [(pageTable + 0, 8, 2048#64), (pageTable + 0x18, 8, 0#64), (pageTable + 0x10, 8, 2047#64)]
          (pageTable + 8) 53#64 (by simp only [OutLRange, and_true]; omega)
        unfold read4
        simp only [b0, b1, b2, b3, Option.getD_some]
        decide
      mask := by
        rw [word10 0x10 (by decide), p5.memory]
        exact word_writeLog_at d4.σ.mem pageTableFieldsLog 3 (pageTable + 0x10) _ rfl
          (by simp only [pageTableFieldsLog, List.drop, OutLRange])
      occupancy := by
        rw [word10 0x18 (by decide), p5.memory]
        exact word_writeLog_at d4.σ.mem pageTableFieldsLog 2 (pageTable + 0x18) _ rfl (by
          simp only [pageTableFieldsLog, List.drop, OutLRange, and_true]; omega)
      entries := by rw [p10.memory]; exact word_writeLog _ _ _
      cleared := fun k hk => by
        rw [mem10 _ (Or.inr (by unfold heapStart at ptLow blkLo; omega)), M.memory,
          clearWords_inside _ _ _ _ (by omega) (by omega)]
        rfl }
    kept := fun x low foot out => by
      have l2 := spLow
      have lowA : x < sp.toNat - 32 - allocHeadroom := below_alloc_frame low
      unfold allocHeadroom heapEnd at l2; unfold allocHeadroom at low
      rw [mem10 x (by simp only [OutW, pageTableWindows, and_true] at out; omega)]
      rw [backTo1 x (by
          by_cases hx : x < heapEnd
          · exact FreshBlock.out_kept fresh hx foot
          · right; unfold heapEnd at blkHi hx; omega)
        (Or.inl (by unfold nativeFrameBase; omega)) (Or.inl (by unfold nativeFrameBase; omega))
        (Or.inl ⟨lowA, foot⟩) out, p1.memory, pageTableSaveLog]
      rw [frameOn_writeLog _ _ _ (frame32.word_log_inside fun o w h => by simp at h; omega) x
        ⟨Or.inl (by simp only [nativeFrameBase]; omega), trivial⟩]
    caller := fun x hx => by
      rw [mem10 x (Or.inr (by unfold heapEnd at spLow; unfold heapStart at ptLow; omega)),
        backTo1 x (stackBlk x (by omega)) (Or.inr (by unfold nativeFrameBase; omega))
          (Or.inr (by unfold nativeFrameBase; omega)) (Or.inr (by omega)) (stackPt x (by omega)), p1.memory,
        pageTableSaveLog]
      rw [frameOn_writeLog _ _ _ (frame32.word_log_inside fun o w h => by simp at h; omega) x
        ⟨Or.inr hx, trivial⟩] }⟩
end OCaml.Vm.Boot.Startup
