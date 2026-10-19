import OCaml.Vm.Boot.Startup.StatAlignedFrameNormalized
import OCaml.Vm.Boot.Startup.StatAlignedFrameImage
import OCaml.Vm.Boot.Startup.StatAlignedEntryNormalized
import OCaml.Vm.Boot.Startup.StatAlignedEntryImage
import OCaml.Vm.Boot.Startup.StatAlignedEntryCallInterface
import OCaml.Vm.Boot.Startup.StatAlignedRoundNormalized
import OCaml.Vm.Boot.Startup.StatAlignedRoundImage
import OCaml.Vm.Boot.Startup.StatAlignedReturnNormalized
import OCaml.Vm.Boot.Startup.StatAlignedReturnImage
import OCaml.Vm.Boot.Startup.PageAddSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_stat_alloc_aligned_noexc(size, modulo, &raw)'s blocks: allocate
`size + 4096`, round the result up to the next page, store the raw block. -/

theorem lui_a5_one (i : MInstr) (w : i.word = 0x000017b7#32) :
    Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) = 4096#64 := by
  rw [imm20Of, w]; decide

/-- `a5 = 4096`, open a 32-byte frame. -/
theorem stat_aligned_frame (c : Config) (sp ra size : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, sp), (10, size)]) :
    FnSummary 0x8000ab80#64 (fun e => e = c) (WriteRegistersPost [15, 2] [] c 0x8000ab88#64 size
      [(15, 4096#64), (2, nativeStack sp 32), (10, size)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_stat_alloc_aligned_noexcXab80Seg 0x8000ab80#64
        [(2, sp), (10, size)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := statAlignedFrame_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_aligned_noexc_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_stat_alloc_aligned_noexcXab80Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal,
      lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, statalignedframe_line_8000ab80, statalignedframe_line_8000ab84] at pins
    exact ⟨gholds_lookup_eq pins rfl (lui_a5_one _ rfl), gholds_lookup (n := 2) _ pins rfl,
      gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

def statAlignedSlots (ra modulo out : BitVec 64) : List (Nat × BitVec 64) := [(24, ra), (8, modulo), (0, out)]

/-- `a0 = size + 4096`; save ra, the modulo and the out pointer. -/
theorem stat_aligned_entry_front (c : Config) (sp ra size modulo out : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(10, size), (15, 4096#64), (1, ra), (2, nativeStack sp 32), (11, modulo), (12, out)]) :
    FnSummary 0x8000ab88#64 (fun e => e = c) (WriteRegistersPost [10] (nativeWordLog sp 32 (statAlignedSlots ra modulo out))
      c jal_8000ab98_call.pc (size + 4096#64)
      [(10, size + 4096#64), (15, 4096#64), (2, nativeStack sp 32), (11, modulo), (12, out)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 (statAlignedSlots ra modulo out)) :=
    frame.word_log_inside fun off value member => by simp [statAlignedSlots] at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_stat_alloc_aligned_noexcXab88Seg 0x8000ab88#64
        [(10, size), (15, 4096#64), (1, ra), (2, nativeStack sp 32), (11, modulo), (12, out)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 15, 1, 2, 11, 12]; decide
      shape := by change ChainOK _ [10, 15, 1, 2, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := statAlignedEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_aligned_noexc_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    exact ⟨gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 2) _ pins rfl,
      gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem stat_aligned_entry (c : Config) (sp ra size modulo out : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(10, size), (15, 4096#64), (1, ra), (2, nativeStack sp 32), (11, modulo), (12, out)]) :
    FnSummary 0x8000ab88#64 (fun e => e = c) (WriteRegistersPost ([10] ++ [1])
      (nativeWordLog sp 32 (statAlignedSlots ra modulo out)) c jal_8000ab98_call.target (size + 4096#64)
      ((1, jal_8000ab98_call.link) :: [(10, size + 4096#64), (15, 4096#64), (2, nativeStack sp 32),
        (11, modulo), (12, out)])) :=
  block_then_call c jal_8000ab98_call_shape jal_8000ab98_call_decode (fun _ h => jal_8000ab98_call_pins h)
    (stat_aligned_entry_front c sp ra size modulo out leaf frame regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- The next page boundary strictly above `raw`. -/
def pageAbove (raw : BitVec 64) : BitVec 64 := (pageNumber raw + 1#64) <<< 12

theorem slli_twelve (x : BitVec 64) (a : MInstr) (imm : a.imm = 12#12) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (shamtOf a) 5 0) = x <<< 12 := by
  rw [shamtOf, imm]
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq']
  rfl

local macro "sak" : tactic => `(tactic| simp only [statalignedround_line_8000aba0, statalignedround_line_8000aba4, statalignedround_line_8000aba8, statalignedround_line_8000abac, statalignedround_line_8000abb0, statalignedround_line_8000abb4, statalignedround_line_8000abb8, statalignedround_line_8000abbc, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- A nonnull block: round it up and store it through the out pointer. -/
theorem stat_aligned_round (c : Config) (sp ra raw out : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(2, nativeStack sp 32), (10, raw)]) (nonzero : raw ≠ 0#64)
    (moduloSlot : bytesT c.σ.mem (nativeFrameBase sp 32 + 8) 8 = 0#64)
    (outSlot : bytesT c.σ.mem (nativeFrameBase sp 32 + 0) 8 = out)
    (outWindow : WriteWindow out 8) (outside : ImageOutside [(out.toNat, 8, raw)]) :
    FnSummary 0x8000ab9c#64 (fun e => e = c) (WriteRegistersPost [11, 12, 15, 10] [(out.toNat, 8, raw)] c
      0x8000abc0#64 (pageAbove raw) [(10, pageAbove raw), (2, nativeStack sp 32)]) := by
  have word (off : Nat) (value : BitVec 64) (h : bytesT c.σ.mem (nativeFrameBase sp 32 + off) 8 = value) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + off)) = value := by rw [read8_value]; exact h
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput (caml_stat_alloc_aligned_noexcXab9cFSeg ++
        caml_stat_alloc_aligned_noexcXaba0Seg) 0x8000ab9c#64 [(2, nativeStack sp 32), (10, raw)]
        [read8 c.σ.mem (nativeFrameBase sp 32 + 8), read8 c.σ.mem (nativeFrameBase sp 32 + 0)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := statAlignedRound_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_aligned_noexc_at_"
        · change guardB bop.BEQ raw 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact outWindow.sd rfl (by sak; rw [word 0 out outSlot,
            show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) }))
  · simp only [caml_stat_alloc_aligned_noexcXab9cFSeg, caml_stat_alloc_aligned_noexcXaba0Seg, List.cons_append,
      List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, wlogM, wentryM,
      widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, statalignedround_line_8000aba0, statalignedround_line_8000aba4, statalignedround_line_8000aba8, statalignedround_line_8000abac, statalignedround_line_8000abb0, statalignedround_line_8000abb4, statalignedround_line_8000abb8, statalignedround_line_8000abbc]
    rw [word 0 out outSlot, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · intro σ pins
    simp only [caml_stat_alloc_aligned_noexcXab9cFSeg, caml_stat_alloc_aligned_noexcXaba0Seg, List.cons_append,
      List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons, List.tail_cons,
      statalignedround_line_8000aba0, statalignedround_line_8000aba4, statalignedround_line_8000aba8, statalignedround_line_8000abac, statalignedround_line_8000abb0, statalignedround_line_8000abb4, statalignedround_line_8000abb8, statalignedround_line_8000abbc] at pins
    exact ⟨gholds_lookup_eq pins rfl (by
        rw [word 8 _ moduloSlot, BitVec.add_zero, srli_page _ _ rfl, slli_twelve _ _ rfl,
          show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, BitVec.sub_zero]; rfl),
      gholds_lookup (n := 2) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- Restore ra and return. -/
theorem stat_aligned_return (c : Config) (sp ra v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(2, nativeStack sp 32), (10, v)])
    (saved : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000abc0#64 (fun e => e = c) (WriteRegistersPost [1, 2] [] c ra v [(2, sp), (1, ra), (10, v)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) = ra := by rw [read8_value]; exact saved
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_stat_alloc_aligned_noexcXabc0Seg 0x8000abc0#64
        [(2, nativeStack sp 32), (10, v)] [read8 c.σ.mem (nativeFrameBase sp 32 + 24)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := statAlignedReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_aligned_noexc_at_"
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word, ret_tgt ra aligned]
  · simp only [caml_stat_alloc_aligned_noexcXabc0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, statalignedreturn_line_8000abc0, statalignedreturn_line_8000abc4]
    rw [show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide, nativeStack_restore, word]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
