import OCaml.Vm.Boot.Startup.MajorTailSteps
import OCaml.Vm.Boot.Startup.ReadyDiv
import OCaml.Vm.Boot.Startup.HeapAlloc
import OCaml.Vm.Boot.Startup.MakeFree
import OCaml.Vm.Boot.Startup.PageApart
import OCaml.Vm.Boot.Startup.PageAdd
import OCaml.Vm.Boot.Startup.MemSame
import Vsa.Sim.FrameComposition
import OCaml.Vm.Boot.Startup.ReadyIndirect
import OCaml.Vm.Boot.Startup.StatAllocDone
import OCaml.Vm.Boot.Startup.MemsetShifted

/-! caml_init_major_heap, composed. Stage A runs from the entry through
`caml_clip_heap_chunk_wsz` (the `__divdi3`/`__muldi3` pair) and the heap
statistics to the `caml_alloc_for_heap` call. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  OCaml.Vm.Sim OCaml.Vm.Gc LeanRV64DExecutable

/-- A frame's save log misses everything below the arena's end. -/
theorem NativeFrame.word_log_below {sp : BitVec 64} {size : Nat} {slots : List (Nat × BitVec 64)}
    (frame : NativeFrame sp size) (bounds : ∀ off value, (off, value) ∈ slots → off + 8 ≤ size)
    (m : Std.ExtHashMap Nat (BitVec 8)) {a w : Nat} (low : a + w ≤ heapEnd) :
    bytesT (writeLog m (nativeWordLog sp size slots)) a w = bytesT m a w :=
  bytesT_writeLog_out m (OCaml.Vm.Sim.outLRange_of_windows (frame.word_log_inside bounds) (by
    simp only [OutWRange, and_true]
    exact Or.inl (by have := frame.lower; unfold nativeFrameBase; omega)))

/-- caml_init_major_heap(heap_size) is called on a fresh runtime: no major
heap yet (`stat_heap_wsz = 0`), huge pages off, the request at least
`Heap_chunk_min`. -/
structure MajorHeapCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra hsize s0 s1 s2 inc : BitVec 64)
    (c : Config) : Prop where
  pc : PCAt 0x80009340#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, hsize), (8, s0), (9, s1), (18, s2)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (48 + (32 + allocHeadroom))
  domainOwned : (firstDomainPtr.toNat, 928) ∈ H
  increment : bytesT c.σ.mem majorIncrementAddr 8 = inc
  percent : inc.toNat ≤ 1000
  noHeap : bytesT c.σ.mem (domainField 336) 8 = 0#64
  chunkMin : 0xf000 ≤ (hsize >>> 3).toNat
  huge : bytesT c.σ.mem 0x80064b08 8 = 0#64
  charged : vsaChg (heapChunkSize ((hsize >>> 3) <<< 3) + 4152#64).toNat charge
  small : (heapChunkSize ((hsize >>> 3) <<< 3)).toNat + 4152 < 2 ^ 32
  /-- The requested heap is below 4 GiB, so rounding it to pages does not wrap. -/
  request : hsize.toNat < 2 ^ 32

/-- The memory when caml_alloc_for_heap is entered: the saved registers, the
size slot, `stat_heap_wsz` and `stat_top_heap_wsz`. -/
def majorAllocMemory (m : Std.ExtHashMap Nat (BitVec 8)) (sp ra hsize s0 s1 s2 : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeLog (writeLog (writeLog m (nativeWordLog sp 48 (majorSlots ra s0 s1 s2))) (nativeWordLog sp 48 [(8, hsize)]))
    (majorSizeLog (hsize >>> 3))

/-- caml_alloc_for_heap is entered with the requested size. -/
structure MajorAllocEntered (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra hsize s0 s1 s2 : BitVec 64)
    (before after : Config) : Prop where
  call : HeapAllocCall H capacity charge (nativeStack sp 48) jal_800093bc_call.link ((hsize >>> 3) <<< 3) after
  memory : after.σ.mem = majorAllocMemory before.σ.mem sp ra hsize s0 s1 s2
  same : GprsSame before after [1, 2, 5, 8, 9, 10, 11, 12, 13, 15, 18]
  stateReg : gprGet after.σ 8 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  domainReg : gprGet after.σ 9 = some firstDomainPtr

theorem major_to_alloc (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra hsize s0 s1 s2 inc : BitVec 64) (A : MajorHeapCall H capacity charge sp ra hsize s0 s1 s2 inc c) :
    ∃ after, Steps c after ∧ MajorAllocEntered H capacity charge sp ra hsize s0 s1 s2 c after := by
  have regs := A.regs
  have frame48 : NativeFrame sp 48 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 48) (32 + allocHeadroom) := A.frame.nested (front := 48) (by decide)
  -- open the frame
  obtain ⟨d1, run1, p1⟩ := (major_frame c sp ra hsize A.ready.toLeafInput
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 10) _ regs rfl, trivial⟩).run c ⟨A.pc, rfl⟩
  have g1 := GprsSame.of_post p1 (by decide)
  have mem1 : d1.σ.mem = c.σ.mem := p1.memory
  have ready1 : RuntimeReady H (capacity + charge) (nativeStack sp 48) ra d1 :=
    A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p1.regs rfl)
      (g1.get (by decide) (by decide) (by decide) A.ready.raReg) A.ready.aligned frame48 (by simp only [LogInW])
  -- save s2, s0, ra, s1
  obtain ⟨d2, run2, p2⟩ := (major_entry d1 sp ra s0 s1 s2 hsize inc ready1.toLeafInput frame48
    ⟨g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ regs rfl), gholds_lookup (n := 2) _ p1.regs rfl,
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs rfl), ready1.raReg,
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ regs rfl), gholds_lookup (n := 10) _ p1.regs rfl,
      trivial⟩
    (by rw [mem1]; exact A.increment) A.percent (by rw [mem1]; exact A.ready.domainWord)).run d1 ⟨p1.pc, rfl⟩
  have g2 := GprsSame.of_post p2 (by decide)
  have slots2 : ∀ off value, (off, value) ∈ majorSlots ra s0 s1 s2 → off + 8 ≤ 48 := fun off value member => by
    simp [majorSlots] at member; omega
  have ready2 : RuntimeReady H (capacity + charge) (nativeStack sp 48) ra d2 :=
    ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p2.regs rfl)
      (g2.get (by decide) (by decide) (by decide) ready1.raReg) A.ready.aligned frame48 (frame48.word_log_inside slots2)
  have low2 (a w : Nat) (low : a + w ≤ heapEnd) : bytesT d2.σ.mem a w = bytesT c.σ.mem a w := by
    rw [p2.memory, frame48.word_log_below slots2 _ low, mem1]
  -- __divdi3(stat_heap_wsz, 100), keeping heap_size at 8(sp)
  obtain ⟨d3, run3, p3⟩ := (major_div_front d2 sp ra hsize 0#64 ready2.toLeafInput frame48
    ⟨gholds_lookup (n := 10) _ p2.regs rfl, gholds_lookup (n := 2) _ p2.regs rfl, gholds_lookup (n := 9) _ p2.regs rfl,
      trivial⟩ (by rw [low2 _ _ (by decide)]; exact A.noHeap)).run d2 ⟨p2.pc, rfl⟩
  have g3 := GprsSame.of_post p3 (by decide)
  have slots3 : ∀ off value, (off, value) ∈ [(8, hsize)] → off + 8 ≤ 48 := fun off value member => by
    simp at member; omega
  have ready3 : RuntimeReady H (capacity + charge) (nativeStack sp 48) ra d3 :=
    ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p3.regs rfl)
      (g3.get (by decide) (by decide) (by decide) ready2.raReg) A.ready.aligned frame48 (frame48.word_log_inside slots3)
  obtain ⟨d4, run4, D⟩ := (ready_divdi3 jal_80009380_call_shape jal_80009380_call_decode jal_80009380_call_target
    (jal_80009380_call_pins p3.image) ready3 (gholds_lookup (n := 10) _ p3.regs rfl) (gholds_lookup (n := 11) _ p3.regs rfl)
    (by decide) (by decide) (by decide) (by decide)).run d3 ⟨p3.pc, rfl⟩
  have q0 : (0#64).sdiv 100#64 = 0#64 := by decide
  -- __muldi3(q, caml_major_heap_increment)
  have g23 := g3.trans D.same
  obtain ⟨d5, run5, p5⟩ := (major_mul_front d4 jal_80009380_call.link ((0#64).sdiv 100#64) inc D.ready.toLeafInput
    ⟨D.result, g23.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p2.regs rfl), trivial⟩).run d4
    ⟨D.pc, rfl⟩
  have g5 := GprsSame.of_post p5 (by decide)
  have ready5 : RuntimeReady H (capacity + charge) (nativeStack sp 48) jal_80009380_call.link d5 :=
    D.ready.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
      (g5.get (by decide) (by decide) (by decide) D.ready.stack) (g5.get (by decide) (by decide) (by decide) D.ready.raReg)
      (by decide) frame48 (by simp only [LogInW])
  obtain ⟨d6, run6, M⟩ := (ready_muldi3 jal_8000938c_call_shape jal_8000938c_call_decode jal_8000938c_call_target
    (jal_8000938c_call_pins p5.image) ready5 (gholds_lookup (n := 10) _ p5.regs rfl) (gholds_lookup (n := 11) _ p5.regs rfl)
    (by decide)).run d5 ⟨p5.pc, rfl⟩
  have gM : GprsSame d5 d6 [1, 10, 11, 12, 13] := ⟨M.frame⟩
  have mem6 : d6.σ.mem = writeLog d2.σ.mem (nativeWordLog sp 48 [(8, hsize)]) := by
    rw [M.memory, p5.memory]
    show d4.σ.mem = _
    rw [D.memory, p3.memory]
  -- the clipped size: stat_heap_wsz = stat_top_heap_wsz = heap_size / 8
  have g26 := (g23.trans g5).trans gM
  obtain ⟨d7, run7, p7⟩ := (major_size d6 sp jal_8000938c_call.link hsize (inc * (0#64).sdiv 100#64)
    M.ready.toLeafInput frame48
    ⟨M.ready.stack, M.result, g26.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p2.regs rfl), trivial⟩
    (by
      rw [mem6, show nativeFrameBase sp 48 + 8 = (nativeStack sp 48 + BitVec.ofNat 64 8).toNat by
        rw [nativeStack, frame48.address _ (by decide)]; exact (frame48.slot_nat (by decide)).symm]
      exact word_writeLog_at _ _ 0 _ _ rfl trivial)
    A.chunkMin (by rw [q0, BitVec.mul_zero]; simp)).run d6 ⟨M.pc, rfl⟩
  have g7 := GprsSame.of_post p7 (by decide)
  have domainW : WindowsOk H [⟨domainField 336, domainField 352⟩] :=
    ownedWindow_ok (by decide) A.domainOwned (by decide) (by decide)
  have ready7 : RuntimeReady H (capacity + charge) (nativeStack sp 48) jal_8000938c_call.link d7 :=
    M.ready.window_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
      (g7.get (by decide) (by decide) (by decide) M.ready.stack) (g7.get (by decide) (by decide) (by decide) M.ready.raReg)
      (by decide) (by simp only [majorSizeLog, LogInW, InsideW, domainField, and_true]; decide)
      domainW.pins domainW.domain domainW.pool domainW.heap
  -- caml_alloc_for_heap(Bsize_wsize(stat_heap_wsz))
  obtain ⟨d8, run8, p8⟩ := (major_alloc_call d7 jal_8000938c_call.link (hsize >>> 3) ready7.toLeafInput
    ⟨gholds_lookup (n := 15) _ p7.regs rfl, trivial⟩).run d7 ⟨p7.pc, rfl⟩
  have g8 := GprsSame.of_post p8 (by decide)
  have ready8 : RuntimeReady H (capacity + charge) (nativeStack sp 48) jal_800093bc_call.link d8 :=
    ready7.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
      (g8.get (by decide) (by decide) (by decide) ready7.stack) (gholds_lookup (n := 1) _ p8.regs rfl) (by decide)
      frame48 (by simp only [LogInW])
  have mem8 : d8.σ.mem = majorAllocMemory c.σ.mem sp ra hsize s0 s1 s2 := by
    rw [p8.memory]
    show d7.σ.mem = _
    rw [p7.memory, mem6, p2.memory, mem1]
    rfl
  have g18 := ((((g1.trans g2).trans g26).trans g7).trans g8).mono (vs := [1, 2, 5, 8, 9, 10, 11, 12, 13, 15, 18]) (by decide)
  refine ⟨d8, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))), {
    call := {
      pc := by rw [← jal_800093bc_call_target]; exact p8.pc
      regs := ⟨ready8.stack, ready8.raReg, gholds_lookup (n := 10) _ p8.regs rfl, trivial⟩
      ready := ready8
      frame := frameIn
      huge := by
        rw [mem8, majorAllocMemory, bytesT_writeLog_out _ (by simp only [majorSizeLog, OutLRange, domainField, and_true]; decide),
          frame48.word_log_below slots3 _ (by decide), frame48.word_log_below slots2 _ (by decide)]
        exact A.huge
      charged := A.charged
      small := A.small }
    memory := mem8
    same := g18
    stateReg := g8.get (by decide) (by decide) (by decide) ((g7.get (by decide) (by decide) (by decide)
      ((g26.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p2.regs rfl)))))
    domainReg := g8.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p7.regs rfl) }⟩

/-- The page table before the chunk is added: its record, its slot array
inside a live block apart from the domain record, and every occupied slot a
page of a live block. -/
structure MajorTableAt (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (ent : BitVec 64) : Prop where
  fields : PageTableFields m (BitVec.ofNat 64 (pageCount m ent.toNat)) ent
  low : ent.toNat + 16384 ≤ heapEnd
  high : heapStart ≤ ent.toNat
  owned : (ent.toNat, 16384) ∈ H
  windows : ∀ i, i < 2048 → WriteWindow (slotAddr ent (BitVec.ofNat 64 i)) 8
  apartDomain : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat
  occupied : ∀ i, i < 2048 → slotWord m ent i ≠ 0#64 → SlotInBlock H (slotWord m ent i)

theorem MajorTableAt.agree {H : List (Nat × Nat)} {m m' : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64}
    (T : MajorTableAt H m ent) (same : ∀ x, InTable ent x → (m'[x]?).getD 0 = (m[x]?).getD 0) :
    MajorTableAt H m' ent := by
  have fits : ent.toNat + 16384 ≤ 2 ^ 64 := by have := T.low; unfold heapEnd at this; omega
  have slots := slotWord_window_agree fits same
  have count : pageCount m' ent.toNat = pageCount m ent.toNat :=
    pageCount_congr fun i hi => by
      rw [← slotWord_pageSlot _ _ i hi fits, ← slotWord_pageSlot _ _ i hi fits, slots i hi]
  refine ⟨?_, T.low, T.high, T.owned, T.windows, T.apartDomain, fun i hi occ => ?_⟩
  · rw [count]; exact T.fields.window_agree same
  · rw [slots i hi] at occ ⊢; exact T.occupied i hi occ

theorem MajorTableAt.cons {H : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64}
    (T : MajorTableAt H m ent) (e : Nat × Nat) : MajorTableAt (e :: H) m ent :=
  ⟨T.fields, T.low, T.high, List.mem_cons_of_mem _ T.owned, T.windows, T.apartDomain, fun i hi occ => by
    obtain ⟨k, p, b, E⟩ := T.occupied i hi occ
    exact ⟨k, p, b, { E with owned := List.mem_cons_of_mem _ E.owned }⟩⟩

/-- The request rounded down to words: below 4 GiB and at least `Heap_chunk_min` words. -/
theorem major_request_nat (hsize : BitVec 64) (small : hsize.toNat < 2 ^ 32) (chunkMin : 0xf000 ≤ (hsize >>> 3).toNat) :
    ((hsize >>> 3) <<< 3).toNat = hsize.toNat / 8 * 8 ∧ 0x78000 ≤ ((hsize >>> 3) <<< 3).toNat ∧
      ((hsize >>> 3) <<< 3).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at chunkMin
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [Nat.reducePow] at *
  omega

/-- The chunk size: whole pages, at least the request, below 8 GiB. -/
theorem major_chunk_size (req : BitVec 64) (small : req.toNat < 2 ^ 32) :
    (heapChunkSize req).toNat % 4096 = 0 ∧ req.toNat ≤ (heapChunkSize req).toNat ∧
      (heapChunkSize req).toNat < 2 ^ 33 := by
  unfold heapChunkSize
  rw [page_mask_nat, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at *
  omega

/-- A word-multiple survives the `>> 3`, `<< 3` round trip as whole pages. -/
theorem major_words_pages (a : BitVec 64) (pages : a.toNat % 4096 = 0) :
    (a >>> 3) <<< 3 = BitVec.ofNat 64 (4096 * (a.toNat / 4096)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have := a.isLt
  simp only [Nat.reducePow] at *
  omega

/-- The chunk's addresses relative to its head. -/
theorem ChunkSpot.chunk_nat {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) :
    (chunkStart mem).toNat = (chunkHead mem).toNat + 56 := S.field_nat 56 (by decide)

theorem ChunkSpot.chunk_aligned {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) :
    (chunkStart mem).toNat % 4096 = 0 := by
  rw [S.chunk_nat]
  exact (chunk_inside mem asize (by have := S.high; unfold heapEnd at this; omega)).2.2

theorem ChunkSpot.below_chunk {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (k : Nat) (h : k ≤ 56) :
    chunkStart mem - BitVec.ofNat 64 k = chunkHead mem + BitVec.ofNat 64 (56 - k) := by
  apply BitVec.eq_of_toNat_eq
  have hb := S.bounds
  have f := S.field_nat (56 - k) (by omega)
  rw [f, BitVec.toNat_sub, S.chunk_nat, BitVec.toNat_ofNat]
  have hi := S.high
  unfold heapEnd at hi
  simp only [Nat.reducePow]
  omega

/-- The head's fields survive writes that miss the head except its `next` word. -/
theorem ChunkHeadAt.agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {mem a : BitVec 64} {asize : Nat}
    (S : ChunkSpot mem asize) (H : ChunkHeadAt m mem a)
    (same : ∀ x, (chunkHead mem).toNat ≤ x → x < (chunkHead mem).toNat + 56 →
      (x < (chunkHead mem).toNat + 24 ∨ (chunkHead mem).toNat + 32 ≤ x) → (m'[x]?).getD 0 = (m[x]?).getD 0) :
    ChunkHeadAt m' mem a := by
  have field (off : Nat) (h : off + 8 ≤ 56) (apart : off + 8 ≤ 24 ∨ 32 ≤ off) :
      bytesT m' (chunkHead mem + BitVec.ofNat 64 off).toNat 8 = bytesT m (chunkHead mem + BitVec.ofNat 64 off).toNat 8 :=
    word_observed _ fun i hi => by rw [S.field_nat off (by omega)] at *; exact same _ (by omega) (by omega) (by omega)
  have zero : bytesT m' (chunkHead mem).toNat 8 = bytesT m (chunkHead mem).toNat 8 := by
    have := field 0 (by decide) (by decide)
    rwa [show chunkHead mem + BitVec.ofNat 64 0 = chunkHead mem from BitVec.add_zero _] at this
  exact ⟨by rw [zero]; exact H.block, by rw [field 16 (by decide) (by decide)]; exact H.size,
    by rw [field 32 (by decide) (by decide)]; exact H.stop, by rw [field 40 (by decide) (by decide)]; exact H.redarkenEnd,
    by rw [field 48 (by decide) (by decide)]; exact H.redarkenFirst⟩

/-- Page `j` of the chunk lies in its raw block and below `2 ^ 64`. -/
theorem major_page_in_block {mem chunk asize j n : Nat} (hj : j < n) (fit : chunk + 4096 * n ≤ mem + asize + 4152)
    (above : mem < chunk) (high : mem + (asize + 4152) ≤ 0x86800000) :
    mem ≤ chunk + 4096 * j ∧ chunk + 4096 * j < mem + (asize + 4152) ∧ chunk + 4096 * j < 2 ^ 64 := by
  refine ⟨by omega, by omega, ?_⟩
  have : chunk + 4096 * j < 0x86800000 := by omega
  exact Nat.lt_trans this (by decide)

/-- The chunk caml_init_major_heap asks for: the request rounded to pages. -/
abbrev majorChunkSize (hsize : BitVec 64) : BitVec 64 := heapChunkSize ((hsize >>> 3) <<< 3)

/-- Its pages. -/
abbrev majorPages (hsize : BitVec 64) : Nat := (majorChunkSize hsize).toNat / 4096

/-- What stage B writes below the arena's end: `caml_heap_start`, the domain's
heap statistics, and the new block. -/
def majorChunkWindows (mem size : Nat) : List W :=
  [⟨heapStartAddr, heapStartAddr + 8⟩, ⟨domainField 336, domainField 376⟩, ⟨mem, mem + size⟩]

/-- caml_page_table_add is entered for the new chunk. -/
structure MajorPageAddEntered (H : List (Nat × Nat)) (capacity : Nat) (sp ra hsize s0 s1 s2 s3 mem ent : BitVec 64)
    (before after : Config) : Prop where
  call : PageAddCall ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) capacity (nativeStack sp 48)
    jal_80009400_call.link 1#64 (chunkStart mem) (chunkStart mem + BitVec.ofNat 64 (4096 * majorPages hsize))
    (BitVec.ofNat 64 Layout.sym_Caml_state) 1#64 0x80064ad0#64 s3 (chunkStart mem) ent (majorPages hsize) after
  fresh : FreshBlock vsaLayoutP H mem.toNat (majorChunkSize hsize + 4152#64).toNat
  spot : ChunkSpot mem (majorChunkSize hsize).toNat
  head : ChunkHeadAt after.σ.mem mem (majorChunkSize hsize)
  next : bytesT after.σ.mem (chunkHead mem + 24#64).toNat 8 = 0#64
  heapStart : bytesT after.σ.mem heapStartAddr 8 = chunkStart mem
  wsz : bytesT after.σ.mem (domainField 336) 8 = majorChunkSize hsize >>> 3
  topWsz : bytesT after.σ.mem (domainField 344) 8 = majorChunkSize hsize >>> 3
  chunks : bytesT after.σ.mem (domainField 368) 8 = 1#64
  slots : ∀ off value, (off, value) ∈ majorSlots ra s0 s1 s2 →
    bytesT after.σ.mem (nativeFrameBase sp 48 + off) 8 = value
  kept : ∀ x, x < heapEnd → ¬ vsaFoot H x →
    OutW (majorChunkWindows mem.toNat (majorChunkSize hsize + 4152#64).toNat) x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  count : pageCount after.σ.mem ent.toNat = pageCount before.σ.mem ent.toNat
  tableApart : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat
  tableOwned : (ent.toNat, 16384) ∈ H

theorem major_to_page_add (c d8 : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra hsize s0 s1 s2 s3 inc ent : BitVec 64) (A : MajorHeapCall H capacity charge sp ra hsize s0 s1 s2 inc c)
    (E : MajorAllocEntered H capacity charge sp ra hsize s0 s1 s2 c d8) (T : MajorTableAt H c.σ.mem ent)
    (s3reg : gprGet c.σ 19 = some s3) (room : pageCount c.σ.mem ent.toNat + majorPages hsize ≤ 1024) :
    ∃ mem after, Steps d8 after ∧ MajorPageAddEntered H capacity sp ra hsize s0 s1 s2 s3 mem ent c after := by
  have frame48 : NativeFrame sp 48 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 48) (32 + allocHeadroom) := A.frame.nested (front := 48) (by decide)
  have stack48 : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  obtain ⟨_, reqLow, reqHigh⟩ := major_request_nat hsize A.request A.chunkMin
  obtain ⟨pagesMod, reqLe, sizeHigh⟩ := major_chunk_size ((hsize >>> 3) <<< 3) reqHigh
  change (majorChunkSize hsize).toNat % 4096 = 0 at pagesMod
  change ((hsize >>> 3) <<< 3).toNat ≤ (majorChunkSize hsize).toNat at reqLe
  change (majorChunkSize hsize).toNat < 2 ^ 33 at sizeHigh
  -- caml_alloc_for_heap
  obtain ⟨mem, d9, run9, D⟩ := alloc_for_heap d8 H capacity charge (nativeStack sp 48) jal_800093bc_call.link
    ((hsize >>> 3) <<< 3) E.call
  have sizeNat : (majorChunkSize hsize + 4152#64).toNat = (majorChunkSize hsize).toNat + 4152 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow] at sizeHigh ⊢; omega
  have spot : ChunkSpot mem (majorChunkSize hsize).toNat :=
    ⟨D.fresh.2.1, by have := D.fresh.2.2.1; rw [sizeNat] at this; exact this⟩
  obtain ⟨headLow, headHigh, _⟩ := spot.bounds
  have chunkNat := spot.chunk_nat
  have chunkAligned := spot.chunk_aligned
  have memLow := spot.low
  have memHigh := spot.high
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  rw [hS] at memLow
  rw [hE] at memHigh
  have nonzero : chunkStart mem ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [chunkNat] at this; simp at this
  -- caml_heap_start = chunk
  obtain ⟨d10, run10, p10⟩ := (major_heap_start d9 jal_800093bc_call.link (chunkStart mem) D.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ D.regs rfl, trivial⟩ nonzero).run d9 ⟨D.pc, rfl⟩
  have g10 := GprsSame.of_post p10 (by decide)
  have startW := globalWindow_ok (H := (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H)
    (lo := heapStartAddr) (hi := heapStartAddr + 8) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold heapStartAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready10 := D.ready.window_log p10 (by decide) (by simp only [keysG]; decide) (by decide)
    (g10.get (by decide) (by decide) (by decide) D.ready.stack) (g10.get (by decide) (by decide) (by decide) D.ready.raReg)
    (by decide) (by simp only [LogInW, InsideW, heapStartAddr]; decide) startW.pins startW.domain startW.pool startW.heap
  have mem10 : d10.σ.mem = writeLog d9.σ.mem [(heapStartAddr, 8, chunkStart mem)] := p10.memory
  -- Chunk_next (chunk) = NULL
  have nextAddr : chunkStart mem - 32#64 = chunkHead mem + BitVec.ofNat 64 24 := spot.below_chunk 32 (by decide)
  have sizeAddr : chunkStart mem - 40#64 = chunkHead mem + BitVec.ofNat 64 16 := spot.below_chunk 40 (by decide)
  have f24 := spot.field_nat 24 (by decide)
  have f16 := spot.field_nat 16 (by decide)
  have stateReg9 : gprGet d9.σ 8 = some (BitVec.ofNat 64 Layout.sym_Caml_state) := (D.saved 8 (by decide)).trans E.stateReg
  obtain ⟨d11, run11, p11⟩ := (major_chunk_next d10 jal_800093bc_call.link (chunkStart mem) ready10.toLeafInput
    ⟨gholds_lookup (n := 10) _ p10.regs rfl, gholds_lookup (n := 18) _ p10.regs rfl,
      g10.get (by decide) (by decide) (by decide) stateReg9, trivial⟩
    (by rw [nextAddr]; exact spot.window 24 (by decide) (by decide))
    (by rw [nextAddr, f24]; exact Nat.le_trans memLow (Nat.le_trans (Nat.le_of_lt headLow) (Nat.le_add_right _ _)))
    (by rw [mem10]; exact word_writeLog_at _ _ 0 _ _ rfl trivial) ready10.domainWord).run d10 ⟨p10.pc, rfl⟩
  have g11 := GprsSame.of_post p11 (by decide)
  have freshW : WindowsOk ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H)
      [⟨(chunkHead mem).toNat + 24, (chunkHead mem).toNat + 32⟩] :=
    ownedWindow_ok (q := mem.toNat) (n := (majorChunkSize hsize + 4152#64).toNat) (by rw [hS]; exact memLow) (by simp)
      (by omega) (by rw [sizeNat]; omega)
  have ready11 := ready10.window_log p11 (by decide) (by simp only [keysG]; decide) (by decide)
    (g11.get (by decide) (by decide) (by decide) ready10.stack) (g11.get (by decide) (by decide) (by decide) ready10.raReg)
    (by decide) (by simp only [LogInW, InsideW, nextAddr, f24, and_true]; omega)
    freshW.pins freshW.domain freshW.pool freshW.heap
  have mem11 : d11.σ.mem = writeLog d10.σ.mem [((chunkStart mem - 32#64).toNat, 8, 0#64)] := p11.memory
  -- the size, the statistics, caml_page_table_add(In_heap, chunk, chunk + size)
  have sizeWord : bytesT d11.σ.mem (chunkStart mem - 40#64).toNat 8 = majorChunkSize hsize := by
    rw [mem11, bytesT_writeLog_out _ (by simp only [OutLRange, nextAddr, sizeAddr, f24, f16, and_true]; omega), mem10,
      bytesT_writeLog_out _ (by simp only [OutLRange, sizeAddr, f16, heapStartAddr, and_true]; omega), sizeAddr]
    exact D.head.size
  obtain ⟨d12, run12, p12⟩ := (major_add_call d11 jal_800093bc_call.link (chunkStart mem) (majorChunkSize hsize)
    ready11.toLeafInput ⟨gholds_lookup (n := 11) _ p11.regs rfl, gholds_lookup (n := 9) _ p11.regs rfl,
      gholds_lookup (n := 14) _ p11.regs rfl, trivial⟩
    (by rw [sizeAddr]; exact (spot.window 16 (by decide) (by decide)).read) sizeWord).run d11 ⟨p11.pc, rfl⟩
  have g12 := GprsSame.of_post p12 (by decide)
  have domainW : WindowsOk ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) [⟨domainField 336, domainField 376⟩] :=
    ownedWindow_ok (by decide) (List.mem_cons_of_mem _ A.domainOwned) (by decide) (by decide)
  have ready12 : RuntimeReady ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) capacity (nativeStack sp 48)
      jal_80009400_call.link d12 :=
    ready11.window_log p12 (by decide) (by simp only [keysG]; decide) (by decide)
      (g12.get (by decide) (by decide) (by decide) ready11.stack) (gholds_lookup (n := 1) _ p12.regs rfl) (by decide)
      (by simp only [majorStatLog, LogInW, InsideW, domainField, and_true]; omega)
      domainW.pins domainW.domain domainW.pool domainW.heap
  have mem12 : d12.σ.mem = writeLog d11.σ.mem (majorStatLog (majorChunkSize hsize >>> 3)) := p12.memory
  -- below the arena's end, only the three windows changed
  have slots2 : ∀ off value, (off, value) ∈ majorSlots ra s0 s1 s2 → off + 8 ≤ 48 := fun off value member => by
    simp [majorSlots] at member; omega
  have slots3 : ∀ off value, (off, value) ∈ [(8, hsize)] → off + 8 ≤ 48 := fun off value member => by
    simp at member; omega
  have kept (x : Nat) (low : x < heapEnd) (foot : ¬ vsaFoot H x)
      (out : OutW (majorChunkWindows mem.toNat (majorChunkSize hsize + 4152#64).toNat) x) :
      (d12.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    simp only [majorChunkWindows, OutW, domainField, heapStartAddr, sizeNat, and_true] at out
    obtain ⟨o1, o2, o3⟩ := out
    have fl := frameIn.lower
    have f48 := frame48.lower
    rw [hE] at low fl f48
    have xb : x < nativeFrameBase sp 48 := by unfold nativeFrameBase; omega
    rw [mem12, writeLog_out _ _ _ (by simp only [majorStatLog, OutL, domainField, and_true]; omega),
      mem11, writeLog_out _ _ _ (by simp only [OutL, nextAddr, f24, and_true]; omega),
      mem10, writeLog_out _ _ _ (by simp only [OutL, heapStartAddr, and_true]; omega),
      D.kept x (by rw [stack48]; omega) foot (by omega), E.memory, majorAllocMemory,
      writeLog_out _ _ _ (by simp only [majorSizeLog, OutL, domainField, and_true]; omega),
      frameOn_writeLog _ _ _ (frame48.word_log_inside slots3) x ⟨Or.inl xb, trivial⟩,
      frameOn_writeLog _ _ _ (frame48.word_log_inside slots2) x ⟨Or.inl xb, trivial⟩]
  -- the table is the caller's
  have tableOut (x : Nat) (inT : InTable ent x) :
      x < heapEnd ∧ ¬ vsaFoot H x ∧ OutW (majorChunkWindows mem.toNat (majorChunkSize hsize + 4152#64).toNat) x := by
    have tl := T.low
    have th := T.high
    have hP : pageTable = 0x800684b8 := rfl
    rcases inT with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · refine ⟨by rw [hP] at lo hi; rw [hE]; omega, pageTable_record_not_foot lo hi, ?_⟩
      simp only [majorChunkWindows, OutW, domainField, heapStartAddr, sizeNat, and_true]
      rw [hP] at lo hi
      omega
    · refine ⟨by omega, owned_not_foot' T.high T.owned lo hi, ?_⟩
      have apart : ¬ (mem.toNat ≤ x ∧ x < mem.toNat + ((majorChunkSize hsize).toNat + 4152)) := fun h =>
        D.fresh.2.2.2 _ T.owned x (by unfold InExt; rw [sizeNat]; exact h) (by unfold InExt; exact ⟨lo, hi⟩)
      have ad := T.apartDomain
      simp only [majorChunkWindows, OutW, domainField, heapStartAddr, sizeNat, and_true]
      rw [hS] at th
      rw [dom] at ad ⊢
      omega
  have table12 : MajorTableAt H d12.σ.mem ent := T.agree fun x inT => by
    obtain ⟨low, foot, out⟩ := tableOut x inT
    exact kept x low foot out
  have pagesEq := major_words_pages (majorChunkSize hsize) pagesMod
  have pagesPos : 0 < majorPages hsize := by unfold majorPages; omega
  have pagesFit : (chunkStart mem).toNat + 4096 * majorPages hsize ≤ mem.toNat + (majorChunkSize hsize).toNat + 4152 := by
    unfold majorPages; omega
  have count12 : pageCount d12.σ.mem ent.toNat = pageCount c.σ.mem ent.toNat := by
    have fits : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans T.low (by decide)
    exact pageCount_congr fun i hi => by
      rw [← slotWord_pageSlot _ _ i hi fits, ← slotWord_pageSlot _ _ i hi fits]
      exact slotWord_window_agree fits (fun x inT => by
        obtain ⟨low, foot, out⟩ := tableOut x inT; exact kept x low foot out) i hi
  -- the new block is apart from the domain record
  have freshDomain (x : Nat) (lo : mem.toNat ≤ x) (hi : x < mem.toNat + (majorChunkSize hsize).toNat + 4152) :
      x < 0x8007d150 ∨ 0x8007d150 + 928 ≤ x := by
    have apart := D.fresh.2.2.2 _ A.domainOwned x (by unfold InExt; rw [sizeNat, ← Nat.add_assoc]; exact ⟨lo, hi⟩)
    unfold InExt at apart
    dsimp only at apart
    rw [dom] at apart
    omega
  -- the caller's frame
  have frameByte (y : Nat) (hy : sp.toNat - 48 ≤ y) : (d12.σ.mem[y]?).getD 0 = (d8.σ.mem[y]?).getD 0 := by
    have f48 := frame48.lower
    rw [hE] at f48
    rw [mem12, writeLog_out _ _ _ (by simp only [majorStatLog, OutL, domainField, dom, and_true]; omega),
      mem11, writeLog_out _ _ _ (by simp only [OutL, nextAddr, f24, and_true]; omega),
      mem10, writeLog_out _ _ _ (by simp only [OutL, heapStartAddr, and_true]; omega), D.caller y (by rw [stack48]; omega)]
  -- registers carried to the call
  have g912 := ((g10.trans g11).trans g12).mono (vs := [18, 11, 14, 9, 15, 10, 12, 1]) (by decide)
  have g9 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [18, 11, 14, 9, 15, 10, 12, 1]) {v : BitVec 64}
      (h : gprGet d9.σ k = some v) : gprGet d12.σ k = some v :=
    g912.get lo hi out h
  have s3d9 : gprGet d9.σ 19 = some s3 :=
    (D.saved 19 (by decide)).trans (E.same.get (by decide) (by decide) (by decide) s3reg)
  refine ⟨mem, d12, run9.trans (run10.trans (run11.trans run12)), {
    call := {
      pc := by rw [← jal_80009400_call_target]; exact p12.pc
      regs := ⟨ready12.stack, ready12.raReg, gholds_lookup (n := 10) _ p12.regs rfl,
        gholds_lookup (n := 11) _ p12.regs rfl, by rw [← pagesEq]; exact gholds_lookup (n := 12) _ p12.regs rfl,
        g9 8 (by decide) (by decide) (by decide) stateReg9, gholds_lookup (n := 9) _ p12.regs rfl,
        (g11.trans g12).get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p10.regs rfl),
        g9 19 (by decide) (by decide) (by decide) s3d9, trivial⟩
      ready := ready12
      first := block_first _ chunkAligned
      last := block_last _ _ pagesPos chunkAligned (by omega)
      nonempty := pagesPos
      fields := table12.fields
      span := {
        frame := frameIn.resize (by unfold allocHeadroom; omega) (by decide)
        aligned := chunkAligned
        fits := by omega
        small := by decide
        kindNonzero := by decide
        room := by rw [count12]; exact room
        windows := T.windows
        tableLow := T.low
        tableHigh := T.high
        tableOwned := List.mem_cons_of_mem _ T.owned
        disjoint := fun i hi occ j hj => by
          obtain ⟨lo', hi', fit'⟩ := major_page_in_block hj pagesFit (by rw [chunkNat]; omega) memHigh
          exact fresh_page_apart D.fresh chunkAligned fit' lo' (by rw [sizeNat]; exact hi')
            (table12.occupied i hi occ) } }
    fresh := D.fresh
    spot := spot
    head := D.head.agree spot fun x lo hi apart => by
      have d := freshDomain x (by omega) (by omega)
      rw [mem12, writeLog_out _ _ _ (by simp only [majorStatLog, OutL, domainField, dom, and_true]; omega),
        mem11, writeLog_out _ _ _ (by simp only [OutL, nextAddr, f24, and_true]; omega),
        mem10, writeLog_out _ _ _ (by simp only [OutL, heapStartAddr, and_true]; omega)]
    next := by
      have d0 := freshDomain ((chunkHead mem).toNat + 24) (by omega) (by omega)
      have d7 := freshDomain ((chunkHead mem).toNat + 31) (by omega) (by omega)
      rw [mem12, bytesT_writeLog_out _ (by
          simp only [majorStatLog, OutLRange, domainField, dom, show (chunkHead mem + 24#64).toNat = (chunkHead mem).toNat + 24
            from f24, and_true]; omega), mem11, nextAddr]
      exact word_writeLog_at _ _ 0 _ _ rfl trivial
    heapStart := by
      rw [mem12, bytesT_writeLog_out _ (by simp only [majorStatLog, OutLRange, domainField, dom, heapStartAddr, and_true]; omega),
        mem11, bytesT_writeLog_out _ (by simp only [OutLRange, nextAddr, f24, heapStartAddr, and_true]; omega), mem10]
      exact word_writeLog_at _ _ 0 _ _ rfl trivial
    wsz := by
      rw [mem12]
      exact word_writeLog_at _ _ 1 _ _ rfl (by simp only [majorStatLog, List.drop, OutLRange, domainField, and_true]; omega)
    topWsz := by rw [mem12]; exact word_writeLog_at _ _ 2 _ _ rfl trivial
    chunks := by
      rw [mem12]
      exact word_writeLog_at _ _ 0 _ _ rfl (by simp only [majorStatLog, List.drop, OutLRange, domainField, and_true]; omega)
    slots := fun off value member => by
      have bound := slots2 off value member
      have high : 16 ≤ off := by simp [majorSlots] at member; omega
      have f48 := frame48.lower
      rw [hE] at f48
      have s8 : (nativeStack sp 48 + BitVec.ofNat 64 8).toNat = nativeFrameBase sp 48 + 8 := by
        rw [nativeStack, frame48.address _ (by decide)]; exact frame48.slot_nat (by decide)
      rw [word_observed (m := d8.σ.mem) _ fun i hi => frameByte _ (by unfold nativeFrameBase; omega), E.memory,
        majorAllocMemory, bytesT_writeLog_out _ (by
          simp only [majorSizeLog, OutLRange, domainField, dom, and_true]; unfold nativeFrameBase; omega),
        bytesT_writeLog_out _ (by simp only [nativeWordLog, List.map, OutLRange, s8, and_true]; omega)]
      exact frame48.word_log_read slots2 (by simp [majorSlots]) _ member
    kept := kept
    count := count12
    tableApart := T.apartDomain
    tableOwned := T.owned
    saved := fun k lo hi => by
      have range : k ∉ [18, 11, 14, 9, 15, 10, 12, 1] := by simp; omega
      rw [g912.same k (by omega) (by omega) range,
        D.saved k (by simp [abiSaved]; omega), E.same.same k (by omega) (by omega) (by simp; omega)] }⟩

/-- The runtime globals the rest of caml_init_major_heap reads: the policy's
function pointers (`caml_set_allocation_policy` set best-fit), and the empty
best-fit structures. -/
structure MajorGlobals (m : Std.ExtHashMap Nat (BitVec 8)) (cur : BitVec 64) : Prop where
  initMerge : bytesT m 0x800649e0 8 = 0x800061a0#64
  makeFree : bytesT m 0x800649b8 8 = 0x80006fac#64
  lists : ∀ j, j < 16 → bytesT m (smallList j).toNat 8 = 0#64
  tree : bytesT m largeTreeAddr 8 = 0#64
  least : bytesT m largeLeastAddr 8 = 0#64
  curWsz : bytesT m flCurWszAddr 8 = cur

/-- What stage B writes below the arena: `caml_heap_start`, the table's
occupancy, the best-fit small lists, `caml_fl_merge` and the small-list map. -/
def majorLowWindows : List W :=
  [⟨heapStartAddr, heapStartAddr + 8⟩, ⟨pageTable + 0x18, pageTable + 0x20⟩, smallListsWindow,
    ⟨flMergeAddr, flMergeAddr + 8⟩, ⟨smallMapAddr, smallMapAddr + 4⟩]

/-- bf_init_merge returned into caml_init_major_heap. -/
structure MajorMerged (H : List (Nat × Nat)) (capacity : Nat) (sp ra hsize s0 s1 s2 s3 mem ent : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt jalr_80009410_call.link after
  regs : GHolds after.σ [(2, nativeStack sp 48), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (9, 1#64),
    (18, 0x80064ad0#64), (19, s3)]
  ready : RuntimeReady ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) capacity (nativeStack sp 48)
    jalr_80009410_call.link after
  fresh : FreshBlock vsaLayoutP H mem.toNat (majorChunkSize hsize + 4152#64).toNat
  spot : ChunkSpot mem (majorChunkSize hsize).toNat
  heapStartWord : bytesT after.σ.mem heapStartAddr 8 = chunkStart mem
  wsz : bytesT after.σ.mem (domainField 336) 8 = majorChunkSize hsize >>> 3
  slots : ∀ off value, (off, value) ∈ majorSlots ra s0 s1 s2 →
    bytesT after.σ.mem (nativeFrameBase sp 48 + off) 8 = value
  count : pageCount after.σ.mem ent.toNat = pageCount before.σ.mem ent.toNat + majorPages hsize
  present : ∀ j, j < majorPages hsize → ∃ i, i < 2048 ∧
    slotWord after.σ.mem ent i = 1#64 ||| blockPage (chunkStart mem) j
  lists : ∀ j, j < 16 → ListReset after.σ.mem j
  flMerge : bytesT after.σ.mem flMergeAddr 8 = 0#64
  /-- Below the arena, outside the runtime's own writes, memory is the caller's. -/
  lowSame : ∀ x, x < heapStart → ¬ allocGlobal x → OutW majorLowWindows x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  tableHigh : heapStart ≤ ent.toNat
  tableLow : ent.toNat + 16384 ≤ heapEnd
  tableOwned : (ent.toNat, 16384) ∈ H
  tableApart : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat

theorem major_merged (c d12 : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra hsize s0 s1 s2 s3 inc mem ent cur : BitVec 64)
    (A : MajorHeapCall H capacity charge sp ra hsize s0 s1 s2 inc c)
    (P : MajorPageAddEntered H capacity sp ra hsize s0 s1 s2 s3 mem ent c d12) (G : MajorGlobals c.σ.mem cur) :
    ∃ after, Steps d12 after ∧ MajorMerged H capacity sp ra hsize s0 s1 s2 s3 mem ent c after := by
  have frame48 : NativeFrame sp 48 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have stack48 : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  have entLow := P.call.span.tableHigh
  have memLow := P.spot.low
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  rw [hS] at entLow memLow
  -- caml_page_table_add runs
  obtain ⟨d13, run13, PA⟩ := page_table_add d12 _ capacity _ _ _ _ _ _ _ _ _ _ _ _ P.call
  have k13 : MemSame d12 d13 fun x =>
      (x < heapEnd ∧ OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x) ∨
        (nativeStack sp 48).toNat ≤ x :=
    ⟨fun x h => h.elim (fun h => PA.kept x h.1 h.2) (PA.caller x)⟩
  -- below the arena, the caller's bytes so far
  have low13 (x : Nat) (low : x < 0x8007d140) (alloc : ¬ allocGlobal x)
      (out : OutW [⟨heapStartAddr, heapStartAddr + 8⟩, ⟨pageTable + 0x18, pageTable + 0x20⟩] x) :
      (d13.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    simp only [OutW, heapStartAddr, hP, and_true] at out
    obtain ⟨o1, o2⟩ := out
    rw [k13.same x (Or.inl ⟨by rw [hE]; omega, by simp only [OutW, hP, and_true]; exact ⟨o2, Or.inl (by omega)⟩⟩)]
    exact P.kept x (by rw [hE]; omega) (fun f => f.elim alloc fun h => by rw [hS] at h; omega)
      (by simp only [majorChunkWindows, OutW, domainField, dom, heapStartAddr, and_true]; exact ⟨o1, Or.inl (by omega),
        Or.inl (by omega)⟩)
  have lowWord13 (a : Nat) (low : a + 8 ≤ 0x8007d140) (alloc : ∀ i, i < 8 → ¬ allocGlobal (a + i))
      (out : ∀ i, i < 8 → OutW [⟨heapStartAddr, heapStartAddr + 8⟩, ⟨pageTable + 0x18, pageTable + 0x20⟩] (a + i)) :
      bytesT d13.σ.mem a 8 = bytesT c.σ.mem a 8 :=
    word_observed _ fun i hi => low13 _ (by omega) (alloc i hi) (out i hi)
  -- caml_fl_p_init_merge
  have pointer : bytesT d13.σ.mem 0x800649e0 8 = 0x800061a0#64 := by
    rw [lowWord13 _ (by decide) (fun i hi => by unfold allocGlobal InRange; omega)
      (fun i hi => by simp only [OutW, heapStartAddr, hP, and_true]; omega)]
    exact G.initMerge
  obtain ⟨d14, run14, p14⟩ := (major_merge_front d13 jal_80009400_call.link 0x800061a0#64 PA.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ PA.regs rfl, trivial⟩ pointer).run d13 ⟨PA.pc, rfl⟩
  have g14 := GprsSame.of_post p14 (by decide)
  have ready14 := PA.ready.stack_log p14 (by decide) (by simp only [keysG]; decide) (by decide)
    (g14.get (by decide) (by decide) (by decide) PA.ready.stack) (g14.get (by decide) (by decide) (by decide) PA.ready.raReg)
    (by decide) frame48 (by simp only [LogInW])
  obtain ⟨d15, run15, I⟩ := (ready_indirect jalr_80009410_call_shape jalr_80009410_call_decode
    (jalr_80009410_call_pins p14.image) ready14 [(15, 0x800061a0#64), (10, 0#64)] p14.regs
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) 0x800061a0#64 rfl (by decide) rfl
    (by decide)).run d14 ⟨p14.pc, rfl⟩
  have tgt : jalr_80009410_call.target 0x800061a0#64 = 0x800061a0#64 := by decide
  have mem15 : d15.σ.mem = d13.σ.mem := I.memory.trans p14.memory
  -- bf_init_merge
  obtain ⟨d16, run16, M⟩ := init_merge d15 _ capacity (nativeStack sp 48) jalr_80009410_call.link
    (bytesVal .lw (read4 d15.σ.mem smallMapAddr)) 0#64 (by rw [← tgt]; exact I.pc) I.ready
    (gholds_lookup (n := 10) _ I.regs rfl) rfl (fun j hj => by
      have n0 := smallList_nat j hj 0 (by decide)
      rw [BitVec.add_zero] at n0
      rw [mem15, n0, lowWord13 _ (by omega) (fun i hi => by unfold allocGlobal InRange; omega)
        (fun i hi => by simp only [OutW, heapStartAddr, hP, and_true]; omega), ← n0]
      exact G.lists j hj)
  -- back to the caller's memory
  have k16 : MemSame d15 d16 (OutW [smallListsWindow, ⟨flMergeAddr, flMergeAddr + 8⟩, ⟨smallMapAddr, smallMapAddr + 4⟩]) :=
    ⟨M.kept⟩
  have back (x : Nat) (h1 : OutW [smallListsWindow, ⟨flMergeAddr, flMergeAddr + 8⟩, ⟨smallMapAddr, smallMapAddr + 4⟩] x)
      (h2 : (x < heapEnd ∧ OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x) ∨
        (nativeStack sp 48).toNat ≤ x) :
      (d16.σ.mem[x]?).getD 0 = (d12.σ.mem[x]?).getD 0 := by
    rw [k16.same x h1, mem15, k13.same x h2]
  have tableInit (x : Nat) (h : InTable ent x) :
      OutW [smallListsWindow, ⟨flMergeAddr, flMergeAddr + 8⟩, ⟨smallMapAddr, smallMapAddr + 4⟩] x := by
    simp only [OutW, smallListsWindow, flMergeAddr, smallMapAddr, and_true]
    rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · rw [hP] at lo; omega
    · omega
  have tableSame (x : Nat) (h : InTable ent x) : (d16.σ.mem[x]?).getD 0 = (d13.σ.mem[x]?).getD 0 := by
    rw [k16.same x (tableInit x h), mem15]
  have fits : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans P.call.span.tableLow (by decide)
  have g16 := (g14.trans I.same).trans (GprsSame.of_saved M.saved)
  have regs13 := PA.regs
  have f48 := frame48.lower
  rw [hE] at f48
  have ta := P.tableApart
  rw [dom] at ta
  refine ⟨d16, run13.trans (run14.trans (run15.trans run16)), {
    pc := M.pc
    regs := ⟨M.ready.stack, g16.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs13 rfl),
      g16.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ regs13 rfl),
      g16.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ regs13 rfl),
      g16.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ regs13 rfl), trivial⟩
    ready := M.ready
    fresh := P.fresh
    spot := P.spot
    heapStartWord := by
      rw [word_observed (m := d12.σ.mem) _ fun i hi => back _
        (by simp only [OutW, smallListsWindow, flMergeAddr, smallMapAddr, heapStartAddr, and_true]; omega)
        (Or.inl ⟨by unfold heapStartAddr; rw [hE]; omega,
          by simp only [OutW, heapStartAddr, hP, and_true]; omega⟩)]
      exact P.heapStart
    wsz := by
      rw [word_observed (m := d12.σ.mem) _ fun i hi => back _
        (by simp only [OutW, smallListsWindow, flMergeAddr, smallMapAddr, domainField, dom, and_true]; omega)
        (Or.inl ⟨by simp only [domainField, dom]; rw [hE]; omega,
          by simp only [OutW, domainField, dom, hP, and_true]; omega⟩)]
      exact P.wsz
    slots := fun off value member => by
      have bound : off + 8 ≤ 48 := by simp [majorSlots] at member; omega
      rw [word_observed (m := d12.σ.mem) _ fun i hi => back _
        (by simp only [OutW, smallListsWindow, flMergeAddr, smallMapAddr, and_true]; unfold nativeFrameBase; omega)
        (Or.inr (by rw [stack48]; unfold nativeFrameBase; omega))]
      exact P.slots off value member
    count := by
      have congr : pageCount d16.σ.mem ent.toNat = pageCount d13.σ.mem ent.toNat := pageCount_congr fun i hi => by
        rw [← slotWord_pageSlot _ _ i hi fits, ← slotWord_pageSlot _ _ i hi fits]
        exact slotWord_window_agree fits tableSame i hi
      rw [congr, PA.count, P.count]
    present := fun j hj => by
      obtain ⟨i, hi, slot⟩ := PA.present j hj
      exact ⟨i, hi, by rw [slotWord_window_agree fits tableSame i hi]; exact slot⟩
    lists := M.lists
    flMerge := M.flMerge
    lowSame := fun x low alloc out => by
      simp only [majorLowWindows, OutW, and_true] at out
      obtain ⟨o1, o2, o3, o4, o5⟩ := out
      rw [k16.same x (by simp only [OutW, and_true]; exact ⟨o3, o4, o5⟩), mem15]
      exact low13 x (by rw [hS] at low; exact low) alloc (by simp only [OutW, and_true]; exact ⟨o1, o2⟩)
    saved := fun k lo hi => by
      rw [g16.same k (by omega) (by omega) (by simp [abiClobbered]; omega), PA.saved k lo hi, P.saved k lo hi]
    tableHigh := P.call.span.tableHigh
    tableLow := P.call.span.tableLow
    tableOwned := P.tableOwned
    tableApart := P.tableApart }⟩

/-- The chunk in words: at least `Heap_chunk_min`, exactly the chunk's bytes. -/
theorem major_words_nat (a : BitVec 64) (pages : a.toNat % 4096 = 0) (big : 0x78000 ≤ a.toNat) (small : a.toNat < 2 ^ 33) :
    8 * (a >>> 3).toNat = a.toNat ∧ 18 ≤ (a >>> 3).toNat ∧ (a >>> 3).toNat ≤ 2 ^ 54 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  omega

theorem above_major_globals {x : Nat} (h : 0x8007d140 ≤ x) :
    (x < largeTreeAddr ∨ largeTreeAddr + 8 ≤ x) ∧ (x < flCurWszAddr ∨ flCurWszAddr + 8 ≤ x) := by
  unfold largeTreeAddr flCurWszAddr; omega

/-- What `bf_make_free_blocks` writes below the arena. -/
def majorFreeWindows : List W :=
  majorLowWindows ++ [⟨largeTreeAddr, largeTreeAddr + 8⟩, ⟨flCurWszAddr, flCurWszAddr + 8⟩]

/-- bf_make_free_blocks returned into caml_init_major_heap: the chunk is one
free block, the best-fit tree's root. -/
structure MajorFreed (H : List (Nat × Nat)) (capacity : Nat) (sp ra hsize s0 s1 s2 s3 mem ent cur : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt jalr_80009430_call.link after
  regs : GHolds after.σ [(2, nativeStack sp 48), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (9, 1#64),
    (18, 0x80064ad0#64), (19, s3), (10, chunkStart mem + 8#64)]
  ready : RuntimeReady ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) capacity (nativeStack sp 48)
    jalr_80009430_call.link after
  fresh : FreshBlock vsaLayoutP H mem.toNat (majorChunkSize hsize + 4152#64).toNat
  spot : ChunkSpot mem (majorChunkSize hsize).toNat
  heapStartWord : bytesT after.σ.mem heapStartAddr 8 = chunkStart mem
  wsz : bytesT after.σ.mem (domainField 336) 8 = majorChunkSize hsize >>> 3
  slots : ∀ off value, (off, value) ∈ majorSlots ra s0 s1 s2 →
    bytesT after.σ.mem (nativeFrameBase sp 48 + off) 8 = value
  count : pageCount after.σ.mem ent.toNat = pageCount before.σ.mem ent.toNat + majorPages hsize
  present : ∀ j, j < majorPages hsize → ∃ i, i < 2048 ∧
    slotWord after.σ.mem ent i = 1#64 ||| blockPage (chunkStart mem) j
  lists : ∀ j, j < 16 → ListReset after.σ.mem j
  flMerge : bytesT after.σ.mem flMergeAddr 8 = 0#64
  header : bytesT after.σ.mem (chunkStart mem).toNat 8 = mfbHeader (majorChunkSize hsize >>> 3)
  tree : TreeRoot after.σ.mem (chunkStart mem + 8#64)
  curWsz : bytesT after.σ.mem flCurWszAddr 8 = cur + 1#64 + ((majorChunkSize hsize >>> 3) - 1#64)
  lowSame : ∀ x, x < heapStart → ¬ allocGlobal x → OutW majorFreeWindows x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k

theorem major_freed (c d16 : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra hsize s0 s1 s2 s3 s4 s5 s6 s7 s8 inc mem ent cur : BitVec 64)
    (A : MajorHeapCall H capacity charge sp ra hsize s0 s1 s2 inc c)
    (M : MajorMerged H capacity sp ra hsize s0 s1 s2 s3 mem ent c d16) (G : MajorGlobals c.σ.mem cur)
    (callee : GHolds c.σ [(20, s4), (21, s5), (22, s6), (23, s7), (24, s8)]) :
    ∃ after, Steps d16 after ∧ MajorFreed H capacity sp ra hsize s0 s1 s2 s3 mem ent cur c after := by
  have frame48 : NativeFrame sp 48 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have stack48 : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  have frame80 : NativeFrame (nativeStack sp 48) 80 :=
    (A.frame.nested (front := 48) (by decide)).resize (by unfold allocHeadroom; omega) (by decide)
  obtain ⟨_, reqLow, reqHigh⟩ := major_request_nat hsize A.request A.chunkMin
  obtain ⟨pagesMod, reqLe, sizeHigh⟩ := major_chunk_size ((hsize >>> 3) <<< 3) reqHigh
  change (majorChunkSize hsize).toNat % 4096 = 0 at pagesMod
  change ((hsize >>> 3) <<< 3).toNat ≤ (majorChunkSize hsize).toNat at reqLe
  change (majorChunkSize hsize).toNat < 2 ^ 33 at sizeHigh
  obtain ⟨words, large, fits⟩ := major_words_nat (majorChunkSize hsize) pagesMod (by omega) sizeHigh
  have sizeNat : (majorChunkSize hsize + 4152#64).toNat = (majorChunkSize hsize).toNat + 4152 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow] at sizeHigh ⊢; omega
  obtain ⟨headLow, headHigh, _⟩ := M.spot.bounds
  have chunkNat := M.spot.chunk_nat
  have chunkAligned := M.spot.chunk_aligned
  have memLow := M.spot.low
  have memHigh := M.spot.high
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  rw [hS] at memLow
  rw [hE] at memHigh
  -- the chunk lies in the fresh block, apart from every live block
  have chunkApart (e : Nat × Nat) (owned : e ∈ H) (x : Nat) (inside : InExt e x) :
      x < (chunkStart mem).toNat ∨ (chunkStart mem).toNat + 8 * (majorChunkSize hsize >>> 3).toNat ≤ x := by
    have apart := M.fresh.2.2.2 e owned x
    unfold InExt at apart
    rw [sizeNat] at apart
    rw [words, chunkNat]
    rcases Nat.lt_or_ge x mem.toNat with h | h
    · left; omega
    · rcases Nat.lt_or_ge x (mem.toNat + ((majorChunkSize hsize).toNat + 4152)) with h' | h'
      · exact absurd inside (apart ⟨h, h'⟩)
      · right; omega
  -- caml_fl_p_make_free_blocks(caml_heap_start, stat_heap_wsz, 1, Caml_white)
  have pointer : bytesT d16.σ.mem 0x800649b8 8 = 0x80006fac#64 := by
    rw [word_observed (m := c.σ.mem) _ fun i hi => M.lowSame _ (by rw [hS]; omega)
      (by unfold allocGlobal InRange; omega)
      (by simp only [majorLowWindows, OutW, heapStartAddr, hP, smallListsWindow, flMergeAddr, smallMapAddr, and_true]
          omega)]
    exact G.makeFree
  obtain ⟨d17, run17, p17⟩ := (major_free_front d16 jalr_80009410_call.link (chunkStart mem)
    (majorChunkSize hsize >>> 3) 0x80006fac#64 M.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ M.regs rfl, gholds_lookup (n := 18) _ M.regs rfl, gholds_lookup (n := 9) _ M.regs rfl,
      trivial⟩ M.ready.domainWord M.heapStartWord pointer M.wsz).run d16 ⟨M.pc, rfl⟩
  have g17 := GprsSame.of_post p17 (by decide)
  have ready17 := M.ready.stack_log p17 (by decide) (by simp only [keysG]; decide) (by decide)
    (g17.get (by decide) (by decide) (by decide) M.ready.stack) (g17.get (by decide) (by decide) (by decide) M.ready.raReg)
    (by decide) frame48 (by simp only [LogInW])
  obtain ⟨d18, run18, I⟩ := (ready_indirect jalr_80009430_call_shape jalr_80009430_call_decode
    (jalr_80009430_call_pins p17.image) ready17 _ p17.regs (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) 0x80006fac#64 rfl (by decide) rfl (by decide)).run d17 ⟨p17.pc, rfl⟩
  have tgt : jalr_80009430_call.target 0x80006fac#64 = 0x80006fac#64 := by decide
  have mem18 : d18.σ.mem = d16.σ.mem := I.memory.trans p17.memory
  have g18 := g17.trans I.same
  have low18 (a : Nat) (low : a + 8 ≤ 0x8007d140) (alloc : ∀ i, i < 8 → ¬ allocGlobal (a + i))
      (out : ∀ i, i < 8 → OutW majorLowWindows (a + i)) : bytesT d18.σ.mem a 8 = bytesT c.σ.mem a 8 := by
    rw [mem18]
    exact word_observed _ fun i hi => M.lowSame _ (by rw [hS]; omega) (alloc i hi) (out i hi)
  have saved18 (k : Nat) (lo : 20 ≤ k) (hi : k ≤ 24) {v : BitVec 64} (h : gprGet c.σ k = some v) :
      gprGet d18.σ k = some v := by
    rw [g18.same k (by omega) (by omega) (by simp; omega), M.saved k lo (by omega)]; exact h
  have regs16 := M.regs
  have lowWin (a : Nat) (i : Nat) (hi : i < 8) (h : a + 8 ≤ 0x80064a00) :
      OutW majorLowWindows (a + i) := by
    simp only [majorLowWindows, OutW, heapStartAddr, hP, smallListsWindow, flMergeAddr, smallMapAddr, and_true]; omega
  -- bf_make_free_blocks
  obtain ⟨d19, run19, F⟩ := make_free_blocks d18 _ capacity (nativeStack sp 48) jalr_80009430_call.link (chunkStart mem)
    (majorChunkSize hsize >>> 3) (BitVec.ofNat 64 Layout.sym_Caml_state) 1#64 0x80064ad0#64 s3 s4 s5 s6 s7 s8 cur
    mem.toNat (majorChunkSize hsize + 4152#64).toNat {
      pc := by rw [← tgt]; exact I.pc
      regs := ⟨I.ready.stack, I.ready.raReg, gholds_lookup (n := 10) _ I.regs rfl, gholds_lookup (n := 11) _ I.regs rfl,
        gholds_lookup (n := 12) _ I.regs rfl, gholds_lookup (n := 13) _ I.regs rfl, gholds_lookup (n := 8) _ I.regs rfl,
        gholds_lookup (n := 9) _ I.regs rfl, gholds_lookup (n := 18) _ I.regs rfl,
        g18.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ regs16 rfl),
        saved18 20 (by decide) (by decide) (gholds_lookup (n := 20) _ callee rfl),
        saved18 21 (by decide) (by decide) (gholds_lookup (n := 21) _ callee rfl),
        saved18 22 (by decide) (by decide) (gholds_lookup (n := 22) _ callee rfl),
        saved18 23 (by decide) (by decide) (gholds_lookup (n := 23) _ callee rfl),
        saved18 24 (by decide) (by decide) (gholds_lookup (n := 24) _ callee rfl), trivial⟩
      ready := I.ready
      frame := frame80
      fits := fits
      large := large
      ownedLow := by rw [hS]; exact memLow
      owned := by simp
      ownedHigh := by rw [sizeNat, hE]; omega
      chunkStart := by rw [chunkNat]; omega
      chunkStop := by rw [chunkNat, words, sizeNat]; omega
      aligned := by omega
      tree := by
        rw [low18 _ (by decide) (fun i hi => by unfold largeTreeAddr allocGlobal InRange; omega)
          (fun i hi => lowWin _ i hi (by decide))]
        exact G.tree
      least := by
        rw [low18 _ (by decide) (fun i hi => by unfold largeLeastAddr allocGlobal InRange; omega)
          (fun i hi => lowWin _ i hi (by decide))]
        exact G.least
      curWsz := by
        rw [low18 _ (by decide) (fun i hi => by unfold flCurWszAddr allocGlobal InRange; omega)
          (fun i hi => by
            simp only [majorLowWindows, OutW, heapStartAddr, hP, smallListsWindow, flMergeAddr, smallMapAddr, and_true]
            unfold flCurWszAddr; omega)]
        exact G.curWsz }
  -- back to the memory before the call
  have back (x : Nat) (h : (x < heapEnd ∧ OutW [⟨(chunkStart mem).toNat,
        (chunkStart mem).toNat + 8 * (majorChunkSize hsize >>> 3).toNat⟩, ⟨largeTreeAddr, largeTreeAddr + 8⟩,
        ⟨flCurWszAddr, flCurWszAddr + 8⟩] x) ∨ (nativeStack sp 48).toNat ≤ x) :
      (d19.σ.mem[x]?).getD 0 = (d16.σ.mem[x]?).getD 0 := by
    rcases h with ⟨low, out⟩ | above
    · rw [F.kept x low out, mem18]
    · rw [F.caller x above, mem18]
  have lowBack (x : Nat) (low : x < 0x8007d140) (tree : x < largeTreeAddr ∨ largeTreeAddr + 8 ≤ x)
      (cur : x < flCurWszAddr ∨ flCurWszAddr + 8 ≤ x) : (d19.σ.mem[x]?).getD 0 = (d16.σ.mem[x]?).getD 0 :=
    back x (Or.inl ⟨by rw [hE]; omega, by simp only [OutW, and_true]; rw [chunkNat]; exact ⟨Or.inl (by omega), tree, cur⟩⟩)
  have tableBack (x : Nat) (inT : InTable ent x) : (d19.σ.mem[x]?).getD 0 = (d16.σ.mem[x]?).getD 0 := by
    have th := M.tableHigh
    have tl := M.tableLow
    rw [hS] at th
    rw [hE] at tl
    rcases inT with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · rw [hP] at lo hi
      exact lowBack x (by omega) (by unfold largeTreeAddr; omega) (by unfold flCurWszAddr; omega)
    · exact back x (Or.inl ⟨by rw [hE]; omega, by
        simp only [OutW, largeTreeAddr, flCurWszAddr, and_true]
        have ag := above_major_globals (Nat.le_trans th lo)
        exact ⟨chunkApart _ M.tableOwned x ⟨lo, hi⟩, ag.1, ag.2⟩⟩)
  have fitsT : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans M.tableLow (by decide)
  have regs19 := F.regs
  refine ⟨d19, run17.trans (run18.trans run19), {
    pc := F.pc
    regs := ⟨gholds_lookup (n := 2) _ regs19 rfl, gholds_lookup (n := 8) _ regs19 rfl,
      gholds_lookup (n := 9) _ regs19 rfl, gholds_lookup (n := 18) _ regs19 rfl, gholds_lookup (n := 19) _ regs19 rfl,
      gholds_lookup (n := 10) _ regs19 rfl, trivial⟩
    ready := F.ready
    fresh := M.fresh
    spot := M.spot
    heapStartWord := by
      rw [word_observed (m := d16.σ.mem) _ fun i hi => lowBack _ (by unfold heapStartAddr; omega)
        (by unfold heapStartAddr largeTreeAddr; omega) (by unfold heapStartAddr flCurWszAddr; omega)]
      exact M.heapStartWord
    wsz := by
      rw [word_observed (m := d16.σ.mem) _ fun i hi => back _ (Or.inl ⟨by simp only [domainField, dom]; rw [hE]; omega, by
        simp only [OutW, largeTreeAddr, flCurWszAddr, and_true]
        have ag := above_major_globals (x := domainField 336 + i)
          (Nat.le_trans (by decide : 0x8007d140 ≤ domainField 336) (Nat.le_add_right _ _))
        exact ⟨chunkApart _ A.domainOwned _ ⟨by simp only [domainField]; omega, by simp only [domainField]; omega⟩,
          ag.1, ag.2⟩⟩)]
      exact M.wsz
    slots := fun off value member => by
      have bound : off + 8 ≤ 48 := by simp [majorSlots] at member; omega
      rw [word_observed (m := d16.σ.mem) _ fun i hi => back _ (Or.inr (by rw [stack48]; unfold nativeFrameBase; omega))]
      exact M.slots off value member
    count := by
      have congr : pageCount d19.σ.mem ent.toNat = pageCount d16.σ.mem ent.toNat := pageCount_congr fun i hi => by
        rw [← slotWord_pageSlot _ _ i hi fitsT, ← slotWord_pageSlot _ _ i hi fitsT]
        exact slotWord_window_agree fitsT tableBack i hi
      rw [congr, M.count]
    present := fun j hj => by
      obtain ⟨i, hi, slot⟩ := M.present j hj
      exact ⟨i, hi, by rw [slotWord_window_agree fitsT tableBack i hi]; exact slot⟩
    lists := fun j hj => by
      have L := M.lists j hj
      have n0 := smallList_nat j hj 0 (by decide)
      have n8 := smallList_nat j hj 8 (by decide)
      rw [BitVec.add_zero] at n0
      have near (off : Nat) (h : off ≤ 8) : ∀ i, i < 8 → (d19.σ.mem[0x800662e8 + 16 * j + off + i]?).getD 0 =
          (d16.σ.mem[0x800662e8 + 16 * j + off + i]?).getD 0 := fun i hi =>
        lowBack _ (by omega) (by unfold largeTreeAddr; omega) (by unfold flCurWszAddr; omega)
      constructor
      · rw [n0, word_observed (m := d16.σ.mem) _ fun i hi => by have := near 0 (by decide) i hi; simpa using this, ← n0]
        exact L.free
      · rw [show smallList j + 8#64 = smallList j + BitVec.ofNat 64 8 from rfl, n8,
          word_observed (m := d16.σ.mem) _ (near 8 (by decide)), ← n8]
        exact L.merge
    flMerge := by
      rw [word_observed (m := d16.σ.mem) _ fun i hi => lowBack _ (by unfold flMergeAddr; omega)
        (by unfold flMergeAddr largeTreeAddr; omega) (by unfold flMergeAddr flCurWszAddr; omega)]
      exact M.flMerge
    header := F.header
    tree := F.tree
    curWsz := F.curWsz
    lowSame := fun x low alloc out => by
      unfold majorFreeWindows at out
      rw [outW_append] at out
      obtain ⟨o1, o2⟩ := out
      simp only [OutW, and_true] at o2
      rw [hS] at low
      rw [lowBack x low o2.1 o2.2]
      exact M.lowSame x (by rw [hS]; exact low) alloc o1
    saved := fun k lo hi => by
      by_cases h : k ≤ 24
      · have cases : k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl
        · rw [gholds_lookup (n := 20) _ regs19 rfl, gholds_lookup (n := 20) _ callee rfl]
        · rw [gholds_lookup (n := 21) _ regs19 rfl, gholds_lookup (n := 21) _ callee rfl]
        · rw [gholds_lookup (n := 22) _ regs19 rfl, gholds_lookup (n := 22) _ callee rfl]
        · rw [gholds_lookup (n := 23) _ regs19 rfl, gholds_lookup (n := 23) _ callee rfl]
        · rw [gholds_lookup (n := 24) _ regs19 rfl, gholds_lookup (n := 24) _ callee rfl]
      · rw [F.saved k (by omega) hi, g18.same k (by omega) (by omega) (by simp; omega), M.saved k lo hi] }⟩

/-- The mark stack's two blocks are allocated: the record `stack` (its
address in `Caml_state->mark_stack`) and the entry array `entries`. -/
structure MajorStackAllocated (H : List (Nat × Nat)) (capacity : Nat) (sp stack entries : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt jal_80009460_call.link after
  regs : GHolds after.σ [(2, nativeStack sp 48), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (9, stack), (10, entries)]
  ready : RuntimeReady ((entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) :: H) capacity
    (nativeStack sp 48) jal_80009460_call.link after
  freshStack : FreshBlock vsaLayoutP H stack.toNat (24#64).toNat
  alignStack : stack.toNat % 16 = 0
  freshEntries : FreshBlock vsaLayoutP ((stack.toNat, (24#64).toNat) :: H) entries.toNat (32768#64).toNat
  alignEntries : entries.toNat % 16 = 0
  record : bytesT after.σ.mem (domainField 128) 8 = stack
  back : ∀ x, ((x < heapEnd ∧ ¬ vsaFoot H x ∧ OutW [⟨gcPhaseAddr, gcPhaseAddr + 4⟩, ⟨domainField 128, domainField 136⟩] x) ∨
      (nativeStack sp 48).toNat ≤ x) → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k

theorem major_stack_allocated (c d19 : Config) (H : List (Nat × Nat)) (cap c1 c2 charge : Nat)
    (sp ra hsize s0 s1 s2 s3 inc mem ent cur : BitVec 64)
    (A : MajorHeapCall H (cap + c2 + c1) charge sp ra hsize s0 s1 s2 inc c)
    (F : MajorFreed H (cap + c2 + c1) sp ra hsize s0 s1 s2 s3 mem ent cur c d19)
    (charged1 : vsaChg (24#64).toNat c1) (charged2 : vsaChg (32768#64).toNat c2) :
    ∃ stack entries after, Steps d19 after ∧
      MajorStackAllocated ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) cap sp stack entries d19 after := by
  have frame48 : NativeFrame sp 48 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have stack48 : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  have frameIn : NativeFrame (nativeStack sp 48) (32 + allocHeadroom) := A.frame.nested (front := 48) (by decide)
  have frameA : NativeFrame (nativeStack sp 48) allocHeadroom := frameIn.resize (by omega) (by decide)
  have fl := frameIn.lower
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  -- caml_gc_phase = Phase_idle; caml_stat_alloc_noexc(sizeof(struct mark_stack))
  obtain ⟨d20, run20, p20⟩ := (major_phase_call d19 jalr_80009430_call.link (chunkStart mem + 8#64) F.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ F.regs rfl, gholds_lookup (n := 10) _ F.regs rfl, trivial⟩ F.ready.domainWord).run d19
    ⟨F.pc, rfl⟩
  have g20 := GprsSame.of_post p20 (by decide)
  have phaseW := globalWindow_ok (H := (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H)
    (lo := gcPhaseAddr) (hi := gcPhaseAddr + 4) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold gcPhaseAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready20 := F.ready.window_log p20 (by decide) (by simp only [keysG]; decide) (by decide)
    (g20.get (by decide) (by decide) (by decide) F.ready.stack) (gholds_lookup (n := 1) _ p20.regs rfl) (by decide)
    (by simp only [LogInW, InsideW, gcPhaseAddr]; decide) phaseW.pins phaseW.domain phaseW.pool phaseW.heap
  obtain ⟨stack, d21, run21, S1⟩ := stat_alloc_done d20 _ (cap + c2) c1 24#64 (nativeStack sp 48) jal_80009448_call.link
    ready20 frameA (gholds_lookup (n := 10) _ p20.regs rfl) charged1
    (by rw [show BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc = jal_80009448_call.target by decide]; exact p20.pc)
  -- Caml_state->mark_stack = stack
  have regs20 := p20.regs
  obtain ⟨d22, run22, p22⟩ := (major_stack_set d21 jal_80009448_call.link stack S1.ready.toLeafInput
    ⟨(S1.saved 8 (by decide)).trans (gholds_lookup (n := 8) _ regs20 rfl), S1.result,
      (S1.saved 9 (by decide)).trans (gholds_lookup (n := 9) _ regs20 rfl), trivial⟩ S1.ready.domainWord).run d21
    ⟨S1.pc, rfl⟩
  have g22 := GprsSame.of_post p22 (by decide)
  have domainW : WindowsOk ((stack.toNat, (24#64).toNat) :: (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H)
      [⟨domainField 128, domainField 136⟩] :=
    ownedWindow_ok (by decide) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ A.domainOwned)) (by decide) (by decide)
  have ready22 := S1.ready.window_log p22 (by decide) (by simp only [keysG]; decide) (by decide)
    (g22.get (by decide) (by decide) (by decide) S1.ready.stack) (g22.get (by decide) (by decide) (by decide) S1.ready.raReg)
    (by decide) (by simp only [LogInW, InsideW, domainField]; decide) domainW.pins domainW.domain domainW.pool domainW.heap
  have stackNonzero : stack ≠ 0#64 := fun h => S1.fresh.1 (by rw [h]; rfl)
  have record22 : bytesT d22.σ.mem (domainField 128) 8 = stack := by
    rw [p22.memory]; exact word_writeLog_at _ _ 0 _ _ rfl trivial
  -- caml_stat_alloc_noexc(MARK_STACK_INIT_SIZE * sizeof(mark_entry))
  obtain ⟨d23, run23, p23⟩ := (major_stack_alloc_call d22 jal_80009448_call.link stack ready22.toLeafInput
    ⟨gholds_lookup (n := 15) _ p22.regs rfl, gholds_lookup (n := 10) _ p22.regs rfl, trivial⟩ record22
    stackNonzero).run d22 ⟨p22.pc, rfl⟩
  have g23 := GprsSame.of_post p23 (by decide)
  have ready23 := ready22.stack_log p23 (by decide) (by simp only [keysG]; decide) (by decide)
    (g23.get (by decide) (by decide) (by decide) ready22.stack) (gholds_lookup (n := 1) _ p23.regs rfl) (by decide)
    frame48 (by simp only [LogInW])
  obtain ⟨entries, d24, run24, S2⟩ := stat_alloc_done d23 _ cap c2 32768#64 (nativeStack sp 48) jal_80009460_call.link
    ready23 frameA (gholds_lookup (n := 10) _ p23.regs rfl) charged2
    (by rw [show BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc = jal_80009460_call.target by decide]; exact p23.pc)
  have mem23 : d23.σ.mem = d22.σ.mem := p23.memory
  have back (x : Nat) (h : (x < heapEnd ∧
        ¬ vsaFoot ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) x ∧
        OutW [⟨gcPhaseAddr, gcPhaseAddr + 4⟩, ⟨domainField 128, domainField 136⟩] x) ∨ (nativeStack sp 48).toNat ≤ x) :
      (d24.σ.mem[x]?).getD 0 = (d19.σ.mem[x]?).getD 0 := by
    rcases h with ⟨low, foot, out⟩ | above
    · simp only [OutW, and_true] at out
      have below : x < (nativeStack sp 48).toNat - allocHeadroom := by omega
      rw [S2.kept x below (fun f => foot (vsaFoot_of_cons f)), mem23, p22.memory,
        writeLog_out _ _ _ (by simp only [OutL, and_true]; exact out.2), S1.kept x below foot, p20.memory,
        writeLog_out _ _ _ (by simp only [OutL, and_true]; exact out.1)]
    · rw [S2.caller x above, mem23, p22.memory,
        writeLog_out _ _ _ (by simp only [OutL, domainField, dom, and_true]; omega), S1.caller x above, p20.memory,
        writeLog_out _ _ _ (by simp only [OutL, gcPhaseAddr, and_true]; omega)]
  have g24 := (((g20.trans (GprsSame.of_saved S1.saved)).trans g22).trans g23).trans (GprsSame.of_saved S2.saved)
  refine ⟨stack, entries, d24, run20.trans (run21.trans (run22.trans (run23.trans run24))), {
    pc := S2.pc
    regs := ⟨S2.ready.stack, (S2.saved 8 (by decide)).trans
        (g23.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p22.regs rfl)),
      (S2.saved 9 (by decide)).trans (gholds_lookup (n := 9) _ p23.regs rfl), S2.result, trivial⟩
    ready := S2.ready
    freshStack := S1.fresh
    alignStack := S1.align
    freshEntries := S2.fresh
    alignEntries := S2.align
    record := by
      have domLow : 0x8007d140 ≤ domainField 128 := by decide
      rw [word_observed (m := d22.σ.mem) _ fun i hi => by
        rw [S2.kept _ (by simp only [domainField, dom] at *; omega)
          (owned_not_foot' (by decide) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ A.domainOwned))
            (by simp only [domainField]; omega) (by simp only [domainField]; omega)), mem23]]
      exact record22
    back := back
    saved := fun k lo hi => g24.same k (by omega) (by omega) (by simp [abiClobbered]; omega) }⟩

/-- What stage C writes below the arena besides the mark stack's blocks. -/
def majorStackWindows (stack : Nat) : List W :=
  [⟨gcPhaseAddr, gcPhaseAddr + 4⟩, ⟨domainField 128, domainField 136⟩, ⟨stack, stack + 24⟩,
    ⟨extraResourcesAddr, extraResourcesAddr + 8⟩, ⟨allocatedWordsAddr, allocatedWordsAddr + 8⟩]

/-- caml_init_major_heap tail-calls `memset(caml_major_ring, 0, 400)` with the
mark stack initialised and the caller's frame restored. -/
structure MajorTailed (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 stack entries : BitVec 64)
    (base after : Config) : Prop where
  pc : PCAt 0x8004276c#64 after
  regs : GHolds after.σ [(2, sp), (10, BitVec.ofNat 64 majorRingAddr), (11, 0#64), (12, 400#64), (18, s2), (9, s1),
    (1, ra), (8, s0), (15, 0x800644a8#64)]
  ready : RuntimeReady ((entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) :: H) capacity sp ra after
  record : bytesT after.σ.mem (domainField 128) 8 = stack
  entriesWord : bytesT after.σ.mem stack.toNat 8 = entries
  count : bytesT after.σ.mem (stack + 8#64).toNat 8 = 0#64
  size : bytesT after.σ.mem (stack + 16#64).toNat 8 = 2048#64
  extra : bytesT after.σ.mem extraResourcesAddr 8 = 0#64
  allocated : bytesT after.σ.mem allocatedWordsAddr 8 = 0#64
  /-- Below the arena, outside stage C's writes, the bytes are those of `base` (bf_make_free_blocks's return). -/
  back : ∀ x, x < heapEnd → ¬ vsaFoot H x → OutW (majorStackWindows stack.toNat) x →
    (after.σ.mem[x]?).getD 0 = (base.σ.mem[x]?).getD 0
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet base.σ k

theorem major_tailed (c d19 d24 : Config) (H : List (Nat × Nat)) (cap c1 c2 charge : Nat)
    (sp ra hsize s0 s1 s2 s3 inc mem ent cur stack entries : BitVec 64)
    (A : MajorHeapCall H (cap + c2 + c1) charge sp ra hsize s0 s1 s2 inc c)
    (F : MajorFreed H (cap + c2 + c1) sp ra hsize s0 s1 s2 s3 mem ent cur c d19)
    (S : MajorStackAllocated ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) cap sp stack entries d19 d24) :
    ∃ after, Steps d24 after ∧
      MajorTailed ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) cap sp ra s0 s1 s2 stack entries d19 after := by
  have frame48 : NativeFrame sp 48 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have stack48 : (nativeStack sp 48).toNat = sp.toNat - 48 := frame48.stack_nat
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have f48 := frame48.lower
  rw [hE] at f48
  have domainOwned : (firstDomainPtr.toNat, 928) ∈ (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H :=
    List.mem_cons_of_mem _ A.domainOwned
  -- the record's block
  have sLow : 0x8007d140 ≤ stack.toNat := S.freshStack.2.1
  have sHigh : stack.toNat + 24 ≤ 0x86800000 := S.freshStack.2.2.1
  have sAlign := S.alignStack
  have sDom (x : Nat) (lo : stack.toNat ≤ x) (hi : x < stack.toNat + 24) :
      x < 0x8007d150 ∨ 0x8007d150 + 928 ≤ x := by
    have apart := S.freshStack.2.2.2 _ domainOwned x (by unfold InExt; exact ⟨lo, hi⟩)
    unfold InExt at apart
    dsimp only at apart
    rw [dom] at apart
    omega
  have s8 : (stack + 8#64).toNat = stack.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have s16 : (stack + 16#64).toNat = stack.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have stackOwned : (stack.toNat, (24#64).toNat) ∈
      (entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) :: (mem.toNat,
        (majorChunkSize hsize + 4152#64).toNat) :: H := by simp
  -- stack->stack = entries
  obtain ⟨d25, run25, p25⟩ := (major_stack_store d24 jal_80009460_call.link stack entries S.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ S.regs rfl, gholds_lookup (n := 9) _ S.regs rfl, trivial⟩
    (window_of_heap (by rw [hS]; exact sLow) (by rw [hE]; omega) (by omega))
    (by constructor <;> simp only [OutLRange, and_true] <;> simp only [Image.textBase, Image.textSize, Image.rodataBase,
      Image.rodataSize] <;> omega)).run d24 ⟨S.pc, rfl⟩
  have g25 := GprsSame.of_post p25 (by decide)
  have stackW : WindowsOk ((entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) ::
      (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) [⟨stack.toNat, stack.toNat + 24⟩] :=
    ownedWindow_ok (by rw [hS]; exact sLow) stackOwned (Nat.le_refl _) (by simp)
  have ready25 := S.ready.window_log p25 (by decide) (by simp only [keysG]; decide) (by decide)
    (g25.get (by decide) (by decide) (by decide) S.ready.stack) (g25.get (by decide) (by decide) (by decide) S.ready.raReg)
    (by decide) (by simp only [LogInW, InsideW, and_true]; omega) stackW.pins stackW.domain stackW.pool stackW.heap
  have domain25 : bytesT d25.σ.mem (domainField 128) 8 = stack := by
    rw [p25.memory, bytesT_writeLog_out _ (by
      simp only [OutLRange, domainField, dom, and_true]
      have a0 := sDom stack.toNat (Nat.le_refl _) (by omega)
      have a7 := sDom (stack.toNat + 7) (by omega) (by omega)
      omega)]
    exact S.record
  have stored25 : bytesT d25.σ.mem stack.toNat 8 = entries := by
    rw [p25.memory]; exact word_writeLog_at _ _ 0 _ _ rfl trivial
  -- reload; nonnull
  obtain ⟨d26, run26, p26⟩ := (major_stack_check d25 jal_80009460_call.link stack entries entries ready25.toLeafInput
    ⟨g25.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ S.regs rfl), gholds_lookup (n := 10) _ p25.regs rfl,
      trivial⟩ ready25.domainWord domain25
    (window_of_heap (w := 8) (by rw [hS]; exact sLow) (by rw [hE]; omega) (by omega)).read stored25
    (fun h => S.freshEntries.1 (by rw [h]; rfl))).run d25 ⟨p25.pc, rfl⟩
  have g26 := GprsSame.of_post p26 (by decide)
  have ready26 := ready25.stack_log p26 (by decide) (by simp only [keysG]; decide) (by decide)
    (g26.get (by decide) (by decide) (by decide) ready25.stack) (g26.get (by decide) (by decide) (by decide) ready25.raReg)
    (by decide) frame48 (by simp only [LogInW])
  have mem26 : d26.σ.mem = d25.σ.mem := p26.memory
  -- count, size, caml_extra_heap_resources
  have extraW := globalWindow_ok (H := (entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) ::
      (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H)
    (lo := extraResourcesAddr) (hi := extraResourcesAddr + 8) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold extraResourcesAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have initW := stackW.cons extraW
  obtain ⟨d27, run27, p27⟩ := (major_stack_init d26 jal_80009460_call.link stack entries ready26.toLeafInput
    ⟨gholds_lookup (n := 14) _ p26.regs rfl, gholds_lookup (n := 15) _ p26.regs rfl, gholds_lookup (n := 10) _ p26.regs rfl,
      trivial⟩ (by rw [mem26]; exact domain25)
    (window_of_heap (by rw [s8, hS]; omega) (by rw [s8, hE]; omega) (by rw [s8]; omega))
    (window_of_heap (by rw [s16, hS]; omega) (by rw [s16, hE]; omega) (by rw [s16]; omega))
    (by
      simp only [OutLRange, s8, domainField, dom, and_true]
      have a8 := sDom (stack.toNat + 8) (by omega) (by omega)
      have a15 := sDom (stack.toNat + 15) (by omega) (by omega)
      omega)
    (by constructor <;> simp only [stackInitLog, OutLRange, s8, s16, extraResourcesAddr, and_true] <;>
      simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega)).run d26 ⟨p26.pc, rfl⟩
  have g27 := GprsSame.of_post p27 (by decide)
  have ready27 := ready26.window_log p27 (by decide) (by simp only [keysG]; decide) (by decide)
    (g27.get (by decide) (by decide) (by decide) ready26.stack) (g27.get (by decide) (by decide) (by decide) ready26.raReg)
    (by decide) (by simp only [stackInitLog, LogInW, InsideW, s8, s16, extraResourcesAddr, and_true]; omega)
    initW.pins initW.domain initW.pool initW.heap
  -- restore; caml_allocated_words = 0; tail call
  have slots27 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ majorSlots ra s0 s1 s2) :
      bytesT d27.σ.mem (nativeFrameBase sp 48 + off) 8 = value := by
    have bound : off + 8 ≤ 48 := by simp [majorSlots] at member; omega
    rw [word_observed (m := d19.σ.mem) _ fun i hi => by
      rw [p27.memory, writeLog_out _ _ _ (by
          simp only [stackInitLog, OutL, s8, s16, extraResourcesAddr, and_true]; unfold nativeFrameBase; omega),
        mem26, p25.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; unfold nativeFrameBase; omega),
        S.back _ (Or.inr (by rw [stack48]; unfold nativeFrameBase; omega))]]
    exact F.slots off value member
  obtain ⟨d28, run28, p28⟩ := (major_tail d27 sp ra s0 s1 s2 entries jal_80009460_call.link ready27.toLeafInput frame48
    ⟨ready27.stack, gholds_lookup (n := 10) _ p27.regs rfl, trivial⟩ slots27).run d27 ⟨p27.pc, rfl⟩
  have g28 := GprsSame.of_post p28 (by decide)
  have wordsW := globalWindow_ok (H := (entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) ::
      (mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H)
    (lo := allocatedWordsAddr) (hi := allocatedWordsAddr + 8) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold allocatedWordsAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready28 := ready27.window_log p28 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p28.regs rfl) (gholds_lookup (n := 1) _ p28.regs rfl) A.ready.aligned
    (by simp only [LogInW, InsideW, allocatedWordsAddr]; decide) wordsW.pins wordsW.domain wordsW.pool wordsW.heap
  -- memory: stage C's writes over d19
  have back28 (x : Nat) (low : x < heapEnd) (foot : ¬ vsaFoot ((mem.toNat, (majorChunkSize hsize + 4152#64).toNat) :: H) x)
      (out : OutW (majorStackWindows stack.toNat) x) : (d28.σ.mem[x]?).getD 0 = (d19.σ.mem[x]?).getD 0 := by
    simp only [majorStackWindows, OutW, and_true] at out
    obtain ⟨o1, o2, o3, o4, o5⟩ := out
    rw [p28.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; exact o5), p27.memory,
      writeLog_out _ _ _ (by simp only [stackInitLog, OutL, s8, s16, and_true]; omega), mem26, p25.memory,
      writeLog_out _ _ _ (by simp only [OutL, and_true]; omega),
      S.back x (Or.inl ⟨low, foot, by simp only [OutW, and_true]; exact ⟨o1, o2⟩⟩)]
  have mem28 : d28.σ.mem = writeLog d27.σ.mem [(allocatedWordsAddr, 8, 0#64)] := p28.memory
  have mem27 : d27.σ.mem = writeLog d26.σ.mem (stackInitLog stack) := p27.memory
  have aw : OutLRange [(allocatedWordsAddr, 8, 0#64)] (domainField 128) 8 := by
    simp only [OutLRange, allocatedWordsAddr, domainField, dom, and_true]; omega
  have g := (((g25.trans g26).trans g27).trans g28)
  refine ⟨d28, run25.trans (run26.trans (run27.trans run28)), {
    pc := p28.pc
    regs := p28.regs
    ready := ready28
    record := by
      rw [mem28, bytesT_writeLog_out _ aw, mem27, bytesT_writeLog_out _ (by
        simp only [stackInitLog, OutLRange, s8, s16, extraResourcesAddr, domainField, dom, and_true]
        have a8 := sDom (stack.toNat + 8) (by omega) (by omega)
        have a23 := sDom (stack.toNat + 23) (by omega) (by omega)
        omega), mem26]
      exact domain25
    entriesWord := by
      rw [mem28, bytesT_writeLog_out _ (by simp only [OutLRange, allocatedWordsAddr, and_true]; omega), mem27,
        bytesT_writeLog_out _ (by simp only [stackInitLog, OutLRange, s8, s16, extraResourcesAddr, and_true]; omega), mem26]
      exact stored25
    count := by
      rw [mem28, bytesT_writeLog_out _ (by simp only [OutLRange, allocatedWordsAddr, s8, and_true]; omega), mem27]
      exact word_writeLog_at _ _ 0 _ _ rfl (by
        simp only [stackInitLog, List.drop, OutLRange, s8, s16, extraResourcesAddr, and_true]; omega)
    size := by
      rw [mem28, bytesT_writeLog_out _ (by simp only [OutLRange, allocatedWordsAddr, s16, and_true]; omega), mem27]
      exact word_writeLog_at _ _ 1 _ _ rfl (by
        simp only [stackInitLog, List.drop, OutLRange, s16, extraResourcesAddr, and_true]; omega)
    extra := by
      rw [mem28, bytesT_writeLog_out _ (by simp only [OutLRange, allocatedWordsAddr, extraResourcesAddr, and_true]; omega),
        mem27]
      exact word_writeLog_at _ _ 2 _ _ rfl trivial
    allocated := by rw [mem28]; exact word_writeLog_at _ _ 0 _ _ rfl trivial
    back := back28
    saved := fun k lo hi => by
      rw [g.same k (by omega) (by omega) (by simp; omega), S.saved k lo hi] }⟩

/-- `caml_major_ring`'s 400 bytes. -/
def majorRingWindow : W := ⟨(BitVec.ofNat 64 majorRingAddr).toNat, (BitVec.ofNat 64 majorRingAddr).toNat + 16 * 24 + 16⟩

/-- memset cleared `caml_major_ring` and returned to caml_init_major_heap's caller. -/
structure MajorRingCleared (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 : BitVec 64) (base after : Config) :
    Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (18, s2), (9, s1), (1, ra), (8, s0)]
  ready : RuntimeReady H capacity sp ra after
  memory : after.σ.mem = writeLog base.σ.mem (memsetShiftLog (BitVec.ofNat 64 majorRingAddr) 24)
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet base.σ k

theorem major_ring_cleared (d19 d28 : Config) (H : List (Nat × Nat)) (cap : Nat)
    (sp ra s0 s1 s2 stack entries : BitVec 64)
    (T : MajorTailed H cap sp ra s0 s1 s2 stack entries d19 d28) :
    ∃ after, Steps d28 after ∧
      MajorRingCleared ((entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) :: H) cap sp ra s0 s1 s2
        d28 after := by
  obtain ⟨d29, run29, M⟩ := (memset_shifted d28 (BitVec.ofNat 64 majorRingAddr) 400#64 ra 24 T.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ T.regs rfl, gholds_lookup (n := 11) _ T.regs rfl, gholds_lookup (n := 12) _ T.regs rfl,
      trivial⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).run d28 ⟨T.pc, rfl⟩
  have g29 := GprsSame.of_post M (by decide)
  have ringW := globalWindow_ok (H := (entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) :: H)
    (lo := majorRingWindow.lo) (hi := majorRingWindow.hi) (by decide) (by decide) (by decide)
    (fun a lo hi => by
      simp only [majorRingWindow, majorRingAddr, BitVec.toNat_ofNat] at lo hi
      unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready29 := T.ready.window_log M (by decide) (by simp only [memsetShiftRegs, keysG]; decide) (by decide)
    (g29.get (by decide) (by decide) (by decide) T.ready.stack) (gholds_lookup (n := 1) _ M.regs rfl) T.ready.aligned
    (memsetShiftLog_in _ 24 (by decide)) ringW.pins ringW.domain ringW.pool ringW.heap
  refine ⟨d29, run29, {
    pc := M.pc
    regs := ⟨ready29.stack, g29.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ T.regs rfl),
      g29.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ T.regs rfl), ready29.raReg,
      g29.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ T.regs rfl), trivial⟩
    ready := ready29
    memory := M.memory
    saved := fun k lo hi => g29.same k (by omega) (by omega) (by simp; omega) }⟩

end OCaml.Vm.Boot.Startup
