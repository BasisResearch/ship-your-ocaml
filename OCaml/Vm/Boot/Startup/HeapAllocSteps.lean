import OCaml.Vm.Boot.Startup.HeapAllocTestNormalized
import OCaml.Vm.Boot.Startup.HeapAllocTestImage
import OCaml.Vm.Boot.Startup.HeapAllocSizeNormalized
import OCaml.Vm.Boot.Startup.HeapAllocSizeImage
import OCaml.Vm.Boot.Startup.HeapAllocFrameNormalized
import OCaml.Vm.Boot.Startup.HeapAllocFrameImage
import OCaml.Vm.Boot.Startup.HeapAllocCallNormalized
import OCaml.Vm.Boot.Startup.HeapAllocCallImage
import OCaml.Vm.Boot.Startup.HeapAllocHeadNormalized
import OCaml.Vm.Boot.Startup.HeapAllocHeadImage
import OCaml.Vm.Boot.Startup.HeapAllocReturnNormalized
import OCaml.Vm.Boot.Startup.HeapAllocReturnImage
import OCaml.Vm.Boot.Startup.HeapAllocCallCallInterface
import OCaml.Vm.Boot.Startup.StatAlignedSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_alloc_for_heap(request)'s blocks, without huge pages: allocate a
page-rounded chunk plus a page and its 56-byte head, place the head just
below a page boundary, fill it. -/

local macro "htk" : tactic => `(tactic| simp only [heapalloctest_line_8000ac40, heapalloctest_line_8000ac44, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- No huge pages. -/
theorem heap_alloc_test (c : Config) (ra req : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, req)])
    (huge : bytesT c.σ.mem 0x80064b08 8 = 0#64) :
    FnSummary 0x8000ac40#64 (fun e => e = c) (WriteRegistersPost [15] [] c 0x8000ac4c#64 req
      [(15, 0#64), (10, req)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 0x80064b08).toNat) = 0#64 := by
    rw [read8_value]; exact huge
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_alloc_for_heapXac40FSeg 0x8000ac40#64 [(10, req)]
        [read8 c.σ.mem (BitVec.ofNat 64 0x80064b08).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := heapAllocTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_alloc_for_heap_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 0x80064b08) 8 by constructor <;> decide).ld rfl (by htk; decide)
            (read8_pins _ _)
        · htk; rw [word]; rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_alloc_for_heapXac40FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, imm20Of, heapalloctest_line_8000ac40, heapalloctest_line_8000ac44] at pins
    exact ⟨gholds_lookup_eq pins rfl word, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- The request rounded up to a page. -/
def heapChunkSize (req : BitVec 64) : BitVec 64 := (req + 4095#64) &&& 0xfffffffffffff000#64

theorem heap_alloc_size (c : Config) (ra req : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, req)]) :
    FnSummary 0x8000ac4c#64 (fun e => e = c) (WriteRegistersPost [15, 14, 10] [] c 0x8000ac68#64 4152#64
      [(15, 0xfffffffffffff000#64), (14, heapChunkSize req), (10, 4152#64)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_alloc_for_heapXac4cSeg 0x8000ac4c#64 [(10, req)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := heapAllocSize_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_alloc_for_heap_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_alloc_for_heapXac4cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, heapallocsize_line_8000ac4c, heapallocsize_line_8000ac50, heapallocsize_line_8000ac54, heapallocsize_line_8000ac58, heapallocsize_line_8000ac5c, heapallocsize_line_8000ac60, heapallocsize_line_8000ac64] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by
        unfold heapChunkSize; congr 1 <;> decide), gholds_lookup_eq pins rfl (by decide), trivial⟩
  · rfl
  · decide

/-- Open a 32-byte frame. -/
theorem heap_alloc_frame (c : Config) (sp ra v : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(2, sp), (10, v)]) :
    FnSummary 0x8000ac68#64 (fun e => e = c) (WriteRegistersPost [2] [] c 0x8000ac6c#64 v
      [(2, nativeStack sp 32), (10, v)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_alloc_for_heapXac68Seg 0x8000ac68#64 [(2, sp), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := heapAllocFrame_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_alloc_for_heap_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

def heapAllocSlots (ra asize : BitVec 64) : List (Nat × BitVec 64) := [(24, ra), (8, asize)]

/-- `caml_stat_alloc_noexc(asize + 4152)`, keeping `asize` at `8(sp)`. -/
theorem heap_alloc_call_front (c : Config) (sp ra asize : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(14, asize), (10, 4152#64), (1, ra), (2, nativeStack sp 32)]) :
    FnSummary 0x8000ac6c#64 (fun e => e = c) (WriteRegistersPost [10] (nativeWordLog sp 32 (heapAllocSlots ra asize)) c
      jal_8000ac78_call.pc (asize + 4152#64) [(14, asize), (10, asize + 4152#64), (2, nativeStack sp 32)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 (heapAllocSlots ra asize)) :=
    frame.word_log_inside fun off value member => by simp [heapAllocSlots] at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_alloc_for_heapXac6cSeg 0x8000ac6c#64
        [(14, asize), (10, 4152#64), (1, ra), (2, nativeStack sp 32)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 10, 1, 2]; decide
      shape := by change ChainOK _ [14, 10, 1, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := heapAllocCall_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_alloc_for_heap_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    exact ⟨gholds_lookup (n := 14) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 2) _ pins rfl,
      trivial⟩
  · rfl
  · decide

theorem heap_alloc_call (c : Config) (sp ra asize : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(14, asize), (10, 4152#64), (1, ra), (2, nativeStack sp 32)]) :
    FnSummary 0x8000ac6c#64 (fun e => e = c) (WriteRegistersPost ([10] ++ [1]) (nativeWordLog sp 32 (heapAllocSlots ra asize))
      c jal_8000ac78_call.target (asize + 4152#64)
      ((1, jal_8000ac78_call.link) :: [(14, asize), (10, asize + 4152#64), (2, nativeStack sp 32)])) :=
  block_then_call c jal_8000ac78_call_shape jal_8000ac78_call_decode (fun _ h => jal_8000ac78_call_pins h)
    (heap_alloc_call_front c sp ra asize leaf frame regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- The chunk's head: 56 bytes just below the page boundary above `mem + 56`. -/
def chunkHead (mem : BitVec 64) : BitVec 64 := (pageNumber (mem + 56#64) <<< 12) + 2047#64 + 1993#64

/-- The chunk: the page boundary itself. -/
def chunkStart (mem : BitVec 64) : BitVec 64 := chunkHead mem + 56#64

/-- The head's fields: block, size, end, redarken_end, redarken_first. -/
def chunkHeadLog (mem asize : BitVec 64) : List WEntry :=
  [((chunkHead mem + 32#64).toNat, 8, chunkStart mem + asize), ((chunkHead mem + 40#64).toNat, 8, chunkStart mem + asize),
    ((chunkHead mem + 48#64).toNat, 8, chunkStart mem), ((chunkHead mem + 16#64).toNat, 8, asize),
    ((chunkHead mem).toNat, 8, mem)]

local macro "hhk" : tactic => `(tactic| simp only [heapallochead_line_8000ac7c, heapallochead_line_8000ac84, heapallochead_line_8000ac88, heapallochead_line_8000ac8c, heapallochead_line_8000ac90, heapallochead_line_8000ac94, heapallochead_line_8000ac98, heapallochead_line_8000ac9c, heapallochead_line_8000aca0, heapallochead_line_8000aca4, heapallochead_line_8000aca8, heapallochead_line_8000acac, heapallochead_line_8000acb0, heapallochead_line_8000acb4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- A nonnull block: place and fill the chunk head; return the chunk. -/
theorem heap_alloc_head (c : Config) (sp ra mem asize : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(10, mem), (2, nativeStack sp 32)]) (nonzero : mem ≠ 0#64)
    (sizeSlot : bytesT c.σ.mem (nativeFrameBase sp 32 + 8) 8 = asize)
    (window : ∀ off, off + 8 ≤ 56 → off % 8 = 0 → WriteWindow (chunkHead mem + BitVec.ofNat 64 off) 8)
    (outside : ImageOutside (chunkHeadLog mem asize)) :
    FnSummary 0x8000ac7c#64 (fun e => e = c) (WriteRegistersPost [13, 15, 14, 10, 12] (chunkHeadLog mem asize) c
      0x8000acb8#64 (chunkStart mem) [(13, mem), (15, chunkHead mem), (14, asize), (10, chunkStart mem),
        (12, chunkStart mem + asize), (2, nativeStack sp 32)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 8)) = asize := by rw [read8_value]; exact sizeSlot
  have s56 : Functions.sign_extend (m := 64) 56#12 = 56#64 := by decide
  have s2047 : Functions.sign_extend (m := 64) 2047#12 = 2047#64 := by decide
  have s1993 : Functions.sign_extend (m := 64) 1993#12 = 1993#64 := by decide
  have s16 : Functions.sign_extend (m := 64) 16#12 = 16#64 := by decide
  have s32 : Functions.sign_extend (m := 64) 32#12 = 32#64 := by decide
  have s40 : Functions.sign_extend (m := 64) 40#12 = 40#64 := by decide
  have s48 : Functions.sign_extend (m := 64) 48#12 = 48#64 := by decide
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput (caml_alloc_for_heapXac7cFSeg ++ caml_alloc_for_heapXac84Seg)
        0x8000ac7c#64 [(10, mem), (2, nativeStack sp 32)] [read8 c.σ.mem (nativeFrameBase sp 32 + 8)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := heapAllocHead_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_alloc_for_heap_at_"
        · change guardB bop.BEQ mem 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (window 32 (by decide) (by decide)).sd rfl (by hhk; rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, s32]; rfl)
        · exact (window 40 (by decide) (by decide)).sd rfl (by hhk; rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, s40]; rfl)
        · exact (window 48 (by decide) (by decide)).sd rfl (by hhk; rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, s48]; rfl)
        · exact (window 16 (by decide) (by decide)).sd rfl (by hhk; rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, s16]; rfl)
        · exact (window 0 (by decide) (by decide)).sd rfl (by hhk; rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, sext_zero]; rfl) }))
  · simp only [caml_alloc_for_heapXac7cFSeg, caml_alloc_for_heapXac84Seg, List.cons_append, List.nil_append,
      evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, wlogM, wentryM, widthOfM, eaddrM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, heapallochead_line_8000ac7c, heapallochead_line_8000ac84, heapallochead_line_8000ac88, heapallochead_line_8000ac8c, heapallochead_line_8000ac90, heapallochead_line_8000ac94, heapallochead_line_8000ac98, heapallochead_line_8000ac9c, heapallochead_line_8000aca0, heapallochead_line_8000aca4, heapallochead_line_8000aca8, heapallochead_line_8000acac, heapallochead_line_8000acb0, heapallochead_line_8000acb4]
    rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, word, s32, s40, s48, s16, sext_zero, BitVec.add_zero, BitVec.add_zero]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_alloc_for_heapXac7cFSeg, caml_alloc_for_heapXac84Seg, List.cons_append, List.nil_append,
      evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons, List.tail_cons, heapallochead_line_8000ac7c, heapallochead_line_8000ac84, heapallochead_line_8000ac88, heapallochead_line_8000ac8c, heapallochead_line_8000ac90, heapallochead_line_8000ac94, heapallochead_line_8000ac98, heapallochead_line_8000ac9c, heapallochead_line_8000aca0, heapallochead_line_8000aca4, heapallochead_line_8000aca8, heapallochead_line_8000acac, heapallochead_line_8000acb0, heapallochead_line_8000acb4] at pins
    rw [srli_page _ _ rfl, slli_twelve _ _ rfl, s56, s2047, s1993, word] at pins
    exact ⟨gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]), gholds_lookup (n := 15) _ pins rfl,
      gholds_lookup (n := 14) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 12) _ pins rfl,
      gholds_lookup (n := 2) _ pins rfl, trivial⟩
  · rfl
  · decide
/-- Restore ra and return. -/
theorem heap_alloc_return (c : Config) (sp ra v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(2, nativeStack sp 32), (10, v)])
    (saved : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000acb8#64 (fun e => e = c) (WriteRegistersPost [1, 2] [] c ra v [(2, sp), (1, ra), (10, v)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) = ra := by rw [read8_value]; exact saved
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_alloc_for_heapXacb8Seg 0x8000acb8#64
        [(2, nativeStack sp 32), (10, v)] [read8 c.σ.mem (nativeFrameBase sp 32 + 24)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := heapAllocReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_alloc_for_heap_at_"
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word, ret_tgt ra aligned]
  · simp only [caml_alloc_for_heapXacb8Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, heapallocreturn_line_8000acb8, heapallocreturn_line_8000acbc]
    rw [show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide, nativeStack_restore, word]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
