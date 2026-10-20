import OCaml.Vm.Boot.Startup.MajorTailSteps
import OCaml.Vm.Boot.Startup.ReadyDiv
import OCaml.Vm.Boot.Startup.HeapAlloc
import OCaml.Vm.Boot.Startup.MakeFree

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

end OCaml.Vm.Boot.Startup
