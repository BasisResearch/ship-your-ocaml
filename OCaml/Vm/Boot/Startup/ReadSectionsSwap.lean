import OCaml.Vm.Boot.Startup.ReadSectionsSteps
import OCaml.Vm.Boot.Startup.ReadSectionsSwapNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsSwapImage
import OCaml.Vm.Boot.Startup.ReadSectionsLoopNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsLoopImage
import OCaml.Vm.Boot.Startup.ReadSectionsReturnNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsReturnImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_read_section_descriptors' loop: reverse the length bytes of
descriptor `i`. -/

local macro "wsk" : tactic => `(tactic| simp only [readsectionsswap_line_80004b70, readsectionsswap_line_80004b74, readsectionsswap_line_80004b78, readsectionsswap_line_80004b7c, readsectionsswap_line_80004b80, readsectionsswap_line_80004b84, readsectionsswap_line_80004b88, readsectionsswap_line_80004b8c, readsectionsswap_line_80004b90, readsectionsswap_line_80004b94, readsectionsswap_line_80004b98, readsectionsswap_line_80004b9c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

theorem swap_shift (a : MInstr) (word : a.imm = 3#12) (k : Nat) (hk : k < 7) :
    Sail.shift_bits_left (BitVec.ofNat 64 k) (Sail.BitVec.extractLsb (shamtOf a) 5 0) = BitVec.ofNat 64 (8 * k) := by
  rw [shamtOf, word]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem swap_next (k : Nat) (hk : k < 7) :
    Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 k + Functions.sign_extend (m := 64) 1#12) 31 0) =
      BitVec.ofNat 64 (k + 1) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Descriptor `ent`'s length bytes `T 0 … T 3` (at `ent + 4`) stored reversed. -/
def sectionSwapLog (ent : BitVec 64) (T : Nat → BitVec 8) : List WEntry :=
  [((ent + 4#64).toNat, 1, lbuWord (T 3)), ((ent + 7#64).toNat, 1, lbuWord (T 0)),
    ((ent + 5#64).toNat, 1, lbuWord (T 2)), ((ent + 6#64).toNat, 1, lbuWord (T 1))]

/-- One descriptor's length bytes reversed. -/
theorem read_sections_swap (c : Config) (ra trail blk ent : BitVec 64) (k : Nat) (hk : k < 7) (T : Nat → BitVec 8)
    (leaf : LeafInput ra c) (regs : GHolds c.σ [(8, trail), (14, BitVec.ofNat 64 k)])
    (window : ReadWindow (trail + 16#64) 8) (blkWord : bytesT c.σ.mem (trail + 16#64).toNat 8 = blk)
    (entry : blk + BitVec.ofNat 64 (8 * k) = ent)
    (fields : ∀ j, j < 4 → WriteWindow (ent + BitVec.ofNat 64 (4 + j)) 1)
    (len : ∀ j, j < 4 → (c.σ.mem[(ent + BitVec.ofNat 64 (4 + j)).toNat]?).getD 0 = T j)
    (outside : ImageOutside (sectionSwapLog ent T)) :
    FnSummary 0x80004b70#64 (fun e => e = c) (WriteRegistersPost [12, 13, 10, 11, 15, 14] (sectionSwapLog ent T) c
      0x80004ba0#64 (lbuWord (T 3)) [(12, lbuWord (T 2)), (13, lbuWord (T 1)), (10, lbuWord (T 3)),
        (11, lbuWord (T 0)), (15, ent), (14, BitVec.ofNat 64 (k + 1)), (8, trail)]) := by
  have field (j : Nat) (hj : j < 4) (imm : BitVec 12) (himm : Functions.sign_extend (m := 64) imm =
      BitVec.ofNat 64 (4 + j)) (a : MInstr) (shift : a.imm = 3#12) :
      bytesVal .ld (read8 c.σ.mem (trail + 16#64).toNat) +
        Sail.shift_bits_left (BitVec.ofNat 64 k) (Sail.BitVec.extractLsb (shamtOf a) 5 0) +
        Functions.sign_extend (m := 64) imm = ent + BitVec.ofNat 64 (4 + j) := by
    rw [read8_value, blkWord, swap_shift a shift k hk, entry, himm]
  apply registers_of_blocks leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4b70Seg 0x80004b70#64
        [(8, trail), (14, BitVec.ofNat 64 k)] [read8 c.σ.mem (trail + 16#64).toNat, [T 0], [T 3], [T 1], [T 2]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 14]; decide
      shape := by change ChainOK _ [8, 14] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsSwap_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        · exact window.ld rfl rfl (read8_pins _ _)
        · repeat refine memFacts_stepMem_skip rfl ?_
          exact (fields 0 (by decide)).read.lbu rfl (by wsk; exact field 0 (by decide) _ (by decide) _ rfl) (len 0 (by decide))
        · repeat refine memFacts_stepMem_skip rfl ?_
          exact (fields 3 (by decide)).read.lbu rfl (by wsk; exact field 3 (by decide) _ (by decide) _ rfl) (len 3 (by decide))
        · repeat refine memFacts_stepMem_skip rfl ?_
          exact (fields 1 (by decide)).read.lbu rfl (by wsk; exact field 1 (by decide) _ (by decide) _ rfl) (len 1 (by decide))
        · repeat refine memFacts_stepMem_skip rfl ?_
          exact (fields 2 (by decide)).read.lbu rfl (by wsk; exact field 2 (by decide) _ (by decide) _ rfl) (len 2 (by decide))
        · exact (fields 0 (by decide)).sb rfl (by wsk; exact field 0 (by decide) _ (by decide) _ rfl)
        · exact (fields 3 (by decide)).sb rfl (by wsk; exact field 3 (by decide) _ (by decide) _ rfl)
        · exact (fields 1 (by decide)).sb rfl (by wsk; exact field 1 (by decide) _ (by decide) _ rfl)
        · exact (fields 2 (by decide)).sb rfl (by wsk; exact field 2 (by decide) _ (by decide) _ rfl) }))
  · simp only [caml_read_section_descriptorsX4b70Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsswap_line_80004b70, readsectionsswap_line_80004b74, readsectionsswap_line_80004b78, readsectionsswap_line_80004b7c, readsectionsswap_line_80004b80, readsectionsswap_line_80004b84, readsectionsswap_line_80004b88, readsectionsswap_line_80004b8c, readsectionsswap_line_80004b90, readsectionsswap_line_80004b94, readsectionsswap_line_80004b98, readsectionsswap_line_80004b9c]
    rw [field 0 (by decide) _ (by decide) _ rfl, field 3 (by decide) _ (by decide) _ rfl,
      field 1 (by decide) _ (by decide) _ rfl, field 2 (by decide) _ (by decide) _ rfl]
    rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4b70Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsswap_line_80004b70, readsectionsswap_line_80004b74, readsectionsswap_line_80004b78, readsectionsswap_line_80004b7c, readsectionsswap_line_80004b80, readsectionsswap_line_80004b84, readsectionsswap_line_80004b88, readsectionsswap_line_80004b8c, readsectionsswap_line_80004b90, readsectionsswap_line_80004b94, readsectionsswap_line_80004b98, readsectionsswap_line_80004b9c]
    rw [read8_value, blkWord, swap_shift _ rfl k hk, entry, swap_next k hk]
  · rfl
  · decide
local macro "lpk" : tactic => `(tactic| simp only [readsectionsloop_line_80004ba0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

theorem sections_more (n : Nat) (hn : n < 7) :
    guardB bop.BLTU (BitVec.ofNat 64 n) (bytesVal .lw sectionsWord) = true := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Back to the head while `i < num_sections`. -/
theorem read_sections_again (c : Config) (ra trail v : BitVec 64) (n : Nat) (hn : n < 7) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, trail), (14, BitVec.ofNat 64 n), (10, v)]) (window : ReadWindow trail 4)
    (numWord : read4 c.σ.mem trail.toNat = sectionsWord) :
    FnSummary 0x80004ba0#64 (fun e => e = c) (WriteRegistersPost [15] [] c 0x80004b70#64 v
      [(15, 7#64), (8, trail), (14, BitVec.ofNat 64 n), (10, v)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4ba0TSeg 0x80004ba0#64
        [(8, trail), (14, BitVec.ofNat 64 n), (10, v)] [sectionsWord] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 14, 10]; decide
      shape := by change ChainOK _ [8, 14, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsLoop_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        · exact window.lw rfl (by lpk; rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
            BitVec.add_zero]) (by rw [← numWord]; exact read4_pins _ _)
        · lpk; exact sections_more n hn }))
  · rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4ba0TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsloop_line_80004ba0]
    rw [show bytesVal MKind.lw sectionsWord = 7#64 by decide]
  · rfl
  · decide

/-- Out of the loop after the last descriptor. -/
theorem read_sections_done (c : Config) (ra trail v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, trail), (14, 7#64), (10, v)]) (window : ReadWindow trail 4)
    (numWord : read4 c.σ.mem trail.toNat = sectionsWord) :
    FnSummary 0x80004ba0#64 (fun e => e = c) (WriteRegistersPost [15] [] c 0x80004ba8#64 v
      [(15, 7#64), (8, trail), (14, 7#64), (10, v)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4ba0FSeg 0x80004ba0#64
        [(8, trail), (14, 7#64), (10, v)] [sectionsWord] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 14, 10]; decide
      shape := by change ChainOK _ [8, 14, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsLoop_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        · exact window.lw rfl (by lpk; rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
            BitVec.add_zero]) (by rw [← numWord]; exact read4_pins _ _)
        · lpk; decide }))
  · rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4ba0FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsloop_line_80004ba0]
    rw [show bytesVal MKind.lw sectionsWord = 7#64 by decide]
  · rfl
  · decide

/-- Restore `ra`, `s0`, `s1`, `s2` and return. -/
theorem read_sections_return (c : Config) (sp ra s0 s1 s2 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(2, nativeStack sp 32), (10, v)])
    (saved : ∀ off value, (off, value) ∈ readSectionsSlots ra s0 s1 s2 →
      bytesT c.σ.mem (nativeFrameBase sp 32 + off) 8 = value)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80004ba8#64 (fun e => e = c) (WriteRegistersPost [1, 8, 9, 18, 2] [] c ra v
      [(2, sp), (18, s2), (9, s1), (8, s0), (1, ra), (10, v)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ readSectionsSlots ra s0 s1 s2) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4ba8Seg 0x80004ba8#64
        [(2, nativeStack sp 32), (10, v)]
        [read8 c.σ.mem (nativeFrameBase sp 32 + 24), read8 c.σ.mem (nativeFrameBase sp 32 + 16),
          read8 c.σ.mem (nativeFrameBase sp 32 + 8), read8 c.σ.mem (nativeFrameBase sp 32 + 0)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word 24 ra (by simp [readSectionsSlots]), ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word 24 ra (by simp [readSectionsSlots]), ret_tgt ra aligned]
  · simp only [caml_read_section_descriptorsX4ba8Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsreturn_line_80004ba8, readsectionsreturn_line_80004bac, readsectionsreturn_line_80004bb0, readsectionsreturn_line_80004bb4, readsectionsreturn_line_80004bb8]
    rw [show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide, nativeStack_restore,
      word 0 s2 (by simp [readSectionsSlots]), word 8 s1 (by simp [readSectionsSlots]),
      word 16 s0 (by simp [readSectionsSlots]), word 24 ra (by simp [readSectionsSlots])]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
