import OCaml.Vm.Boot.Startup.MajorHeadNormalized
import OCaml.Vm.Boot.Startup.MajorHeadImage
import OCaml.Vm.Boot.Startup.MajorAddCallNormalized
import OCaml.Vm.Boot.Startup.MajorAddCallImage
import OCaml.Vm.Boot.Startup.MajorAddCallCallInterface
import OCaml.Vm.Boot.Startup.MajorSteps
import OCaml.Vm.Boot.Startup.MinorRefSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_init_major_heap after caml_alloc_for_heap: `caml_heap_start`, the
chunk's next link, the heap statistics, and caml_page_table_add(In_heap, ...). -/

/-- `caml_heap_start`. -/
def heapStartAddr : Nat := 0x80064ad0

local macro "mhk" : tactic => `(tactic| simp only [majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `caml_heap_start = chunk`, nonnull. -/
theorem major_heap_start (c : Config) (ra chunk : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, chunk)])
    (nonzero : chunk ≠ 0#64) :
    FnSummary 0x800093c0#64 (fun e => e = c) (WriteRegistersPost [18] [(heapStartAddr, 8, chunk)] c 0x800093d0#64 chunk
      [(18, 0x80064ad0#64), (10, chunk)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, heapStartAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX93c0FSeg 0x800093c0#64 [(10, chunk)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorHead_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 heapStartAddr) 8 by constructor <;> decide).sd rfl (by mhk; decide)
        · change guardB bop.BEQ chunk 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero }))
  · simp only [caml_init_major_heapX93c0FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, wlogM, wentryM,
      widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of,
      majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc]
    rw [show (2147521472#64 + Functions.sign_extend (BitVec.extractLsb' 12 20 0x0005b917#32 +++ 0#12) +
      Functions.sign_extend (m := 64) 1808#12 + Functions.sign_extend (m := 64) 0#12).toNat = heapStartAddr by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX93c0FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `Chunk_next(chunk) = NULL`; reload `caml_heap_start` and the domain; `s1 = 1`. -/
theorem major_chunk_next (c : Config) (ra chunk : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, chunk), (18, 0x80064ad0#64), (8, BitVec.ofNat 64 Layout.sym_Caml_state)])
    (window : WriteWindow (chunk - 32#64) 8) (heap : 0x8007d140 ≤ (chunk - 32#64).toNat)
    (heapWord : bytesT c.σ.mem heapStartAddr 8 = chunk)
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x800093d0#64 (fun e => e = c) (WriteRegistersPost [11, 14, 9] [((chunk - 32#64).toNat, 8, 0#64)] c
      0x800093e0#64 chunk [(11, chunk), (14, firstDomainPtr), (9, 1#64), (10, chunk)]) := by
  have hw : bytesVal .ld (read8 c.σ.mem (0x80064ad0#64).toNat) = chunk := by rw [read8_value]; exact heapWord
  have dw : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have addr : chunk + Functions.sign_extend (m := 64) 4064#12 = chunk - 32#64 := by
    rw [show Functions.sign_extend (m := 64) 4064#12 = -32#64 by decide, ← BitVec.sub_eq_add_neg]
  apply registers_of_blocks' leaf.image (by
      constructor <;> simp only [OutLRange, and_true] <;> simp only [Image.textBase, Image.textSize, Image.rodataBase,
        Image.rodataSize] <;> omega)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX93d0Seg 0x800093d0#64
        [(10, chunk), (18, 0x80064ad0#64), (8, BitVec.ofNat 64 Layout.sym_Caml_state)]
        [read8 c.σ.mem (0x80064ad0#64).toNat, read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 18, 8]; decide
      shape := by change ChainOK _ [10, 18, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := majorHead_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact window.sd rfl (by mhk; exact addr)
        · past_stores
          · exact (show ReadWindow (0x80064ad0#64) 8 by constructor <;> decide).ld rfl
              (by mhk; rw [sext_zero, BitVec.add_zero]) (read8_pins _ _)
          all_goals (intro _; simp only [majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc, OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, List.headD_cons, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, addr, sext_zero, BitVec.add_zero, and_true]; simp only [show (0x80064ad0#64).toNat = 0x80064ad0 from rfl]; omega)
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
              (by mhk; rw [sext_zero, BitVec.add_zero]) (read8_pins _ _)
          all_goals (intro _; simp only [majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc, OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, List.headD_cons, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, addr, sext_zero, BitVec.add_zero, and_true]; simp only [show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = 0x80064d08 from rfl]; omega) }))
  · simp only [caml_init_major_heapX93d0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc]
    rw [addr]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX93d0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, majorhead_line_800093c0, majorhead_line_800093c4, majorhead_line_800093c8, majorhead_line_800093d0, majorhead_line_800093d4, majorhead_line_800093d8, majorhead_line_800093dc] at pins
    try simp only [sext_zero, BitVec.add_zero] at pins
    exact ⟨gholds_lookup_eq pins rfl hw, gholds_lookup_eq pins rfl dw, gholds_lookup_eq pins rfl (by decide),
      gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

local macro "mak" : tactic => `(tactic| simp only [majoraddcall_line_800093e0, majoraddcall_line_800093e4, majoraddcall_line_800093e8, majoraddcall_line_800093ec, majoraddcall_line_800093f0, majoraddcall_line_800093f4, majoraddcall_line_800093f8, majoraddcall_line_800093fc, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `stat_heap_chunks = 1`, `stat_heap_wsz = stat_top_heap_wsz = asize / 8`. -/
def majorStatLog (w : BitVec 64) : List WEntry :=
  [(domainField 368, 8, 1#64), (domainField 336, 8, w), (domainField 344, 8, w)]

/-- The chunk's size; the statistics; `caml_page_table_add(In_heap, chunk, chunk + size)`. -/
theorem major_add_front (c : Config) (ra chunk asize : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, chunk), (9, 1#64), (14, firstDomainPtr)])
    (sizeWindow : ReadWindow (chunk - 40#64) 8) (sizeWord : bytesT c.σ.mem (chunk - 40#64).toNat 8 = asize) :
    FnSummary 0x800093e0#64 (fun e => e = c) (WriteRegistersPost [15, 10, 12] (majorStatLog (asize >>> 3)) c
      jal_80009400_call.pc 1#64 [(15, asize >>> 3), (10, 1#64), (12, chunk + (asize >>> 3) <<< 3), (11, chunk),
        (9, 1#64), (14, firstDomainPtr)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (chunk - 40#64).toNat) = asize := by rw [read8_value]; exact sizeWord
  have addr : chunk + Functions.sign_extend (m := 64) 4056#12 = chunk - 40#64 := by
    rw [show Functions.sign_extend (m := 64) 4056#12 = -40#64 by decide, ← BitVec.sub_eq_add_neg]
  have field (off : Nat) (sx : BitVec 12) (h : Functions.sign_extend (m := 64) sx = BitVec.ofNat 64 off)
      (hoff : off + 8 ≤ 928) (al : off % 8 = 0) :
      WriteWindow (firstDomainPtr + Functions.sign_extend (m := 64) sx) 8 := by
    rw [h]
    have n : (firstDomainPtr + BitVec.ofNat 64 off).toNat = 0x8007d150 + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show firstDomainPtr.toNat = 0x8007d150 from rfl, Nat.reducePow]
      omega
    have hT : Layout.sym_tohost = 0x80061fc0 := rfl
    constructor <;> (try rw [hT]) <;> rw [n] <;> omega
  apply registers_of_blocks' leaf.image (by
      constructor <;> simp only [majorStatLog, OutLRange, domainField, show firstDomainPtr.toNat = 0x8007d150 from rfl,
        and_true] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX93e0Seg 0x800093e0#64
        [(11, chunk), (9, 1#64), (14, firstDomainPtr)] [read8 c.σ.mem (chunk - 40#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 9, 14]; decide
      shape := by change ChainOK _ [11, 9, 14] _; decide
      tick := leaf.tick
      facts := by
        have code := majorAddCall_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact sizeWindow.ld rfl (by mak; exact addr) (read8_pins _ _)
        · exact (field 368 368#12 (by decide) (by decide) (by decide)).sd rfl (by mak)
        · exact (field 336 336#12 (by decide) (by decide) (by decide)).sd rfl (by mak)
        · exact (field 344 344#12 (by decide) (by decide) (by decide)).sd rfl (by mak) }))
  · simp only [caml_init_major_heapX93e0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, majoraddcall_line_800093e0, majoraddcall_line_800093e4, majoraddcall_line_800093e8, majoraddcall_line_800093ec, majoraddcall_line_800093f0, majoraddcall_line_800093f4, majoraddcall_line_800093f8, majoraddcall_line_800093fc]
    rw [word, srli_three _ _ rfl,
      show (firstDomainPtr + Functions.sign_extend (m := 64) 368#12).toNat = domainField 368 by decide,
      show (firstDomainPtr + Functions.sign_extend (m := 64) 336#12).toNat = domainField 336 by decide,
      show (firstDomainPtr + Functions.sign_extend (m := 64) 344#12).toNat = domainField 344 by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX93e0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, majoraddcall_line_800093e0, majoraddcall_line_800093e4, majoraddcall_line_800093e8, majoraddcall_line_800093ec, majoraddcall_line_800093f0, majoraddcall_line_800093f4, majoraddcall_line_800093f8, majoraddcall_line_800093fc] at pins
    rw [word, srli_three _ _ rfl, slli_three _ _ rfl] at pins
    try simp only [sext_zero, BitVec.add_zero] at pins
    exact ⟨gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 12) _ pins rfl,
      gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 9) _ pins rfl, gholds_lookup (n := 14) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem major_add_call (c : Config) (ra chunk asize : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, chunk), (9, 1#64), (14, firstDomainPtr)])
    (sizeWindow : ReadWindow (chunk - 40#64) 8) (sizeWord : bytesT c.σ.mem (chunk - 40#64).toNat 8 = asize) :
    FnSummary 0x800093e0#64 (fun e => e = c) (WriteRegistersPost ([15, 10, 12] ++ [1]) (majorStatLog (asize >>> 3)) c
      jal_80009400_call.target 1#64 ((1, jal_80009400_call.link) ::
        [(15, asize >>> 3), (10, 1#64), (12, chunk + (asize >>> 3) <<< 3), (11, chunk), (9, 1#64),
          (14, firstDomainPtr)])) :=
  block_then_call c jal_80009400_call_shape jal_80009400_call_decode (fun _ h => jal_80009400_call_pins h)
    (major_add_front c ra chunk asize leaf regs sizeWindow sizeWord) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup
