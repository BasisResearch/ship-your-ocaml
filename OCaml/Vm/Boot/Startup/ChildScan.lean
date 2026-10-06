import OCaml.Vm.Boot.Startup.ChildCheck
import OCaml.Vm.Boot.Startup.ChildNextNormalized
import OCaml.Vm.Boot.Startup.ChildNextImage
import OCaml.Vm.Boot.Startup.IndexedLoop
import OCaml.Vm.Boot.Startup.ChildPrologueNormalized
import OCaml.Vm.Boot.Startup.ChildPrologueImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def childNextInput (i p v d k a0 : BitVec 64) : GRegs :=
  [(9, i), (8, p), (18, 64#64), (15, v), (19, d), (20, k), (10, a0)]
def childNextOutput (i p v d k a0 : BitVec 64) : GRegs :=
  [(8, p), (9, i), (18, 64#64), (15, v), (19, d), (20, k), (10, a0)]

/-- `addiw s1,s1,1` on a small slot index. -/
theorem addiw_one (i : Nat) (small : i < 64) :
    Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 i + Functions.sign_extend (m := 64) 1#12) 31 0) =
      BitVec.ofNat 64 (i + 1) := by
  have all : ∀ j : Fin 64, Functions.sign_extend (m := 64)
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 j.val + Functions.sign_extend (m := 64) 1#12) 31 0) =
      BitVec.ofNat 64 (j.val + 1) := by decide
  exact all ⟨i, small⟩

/-- Advance to the next slot and test the end of the table. -/
theorem child_next (c : Config) (ra p v d k a0 : BitVec 64) (i : Nat) (small : i < 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (childNextInput (BitVec.ofNat 64 i) p v d k a0)) :
    FnSummary 0x80000080#64 (fun e => e = c)
      (WriteRegistersPost [9, 8] [] c (if i + 1 < 64 then 0x8000008c#64 else 0x800000e8#64) a0
        (childNextOutput (BitVec.ofNat 64 (i + 1)) (p + 56#64) v d k a0)) := by
  by_cases last : i + 1 < 64
  · have step : guardB bop.BEQ (BitVec.ofNat 64 (i + 1)) 64#64 = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput childX0080FSeg 0x80000080#64
          (childNextInput (BitVec.ofNat 64 i) p v d k a0) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [9, 8, 18, 15, 19, 20, 10]; decide
        shape := by change ChainOK _ [9, 8, 18, 15, 19, 20, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := childNext_code leaf.image
          chain_facts code with "Vsa.Sim.Code.child_at_"
          change guardB bop.BEQ (Functions.sign_extend (m := 64)
            (Sail.BitVec.extractLsb (BitVec.ofNat 64 i + Functions.sign_extend (m := 64) 1#12) 31 0)) 64#64 = false
          rw [addiw_one i small]
          exact step }))
    · rfl
    · rw [if_pos last]; rfl
    · simp only [childX0080FSeg, evalBlocks, evalBlock, SegEvalState.init, childnext_line_80000080,
        childnext_line_80000084, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG,
        eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff,
        ite_true, ite_false, childNextInput, childNextOutput]
      rw [addiw_one i small]
      rfl
    · rfl
    · decide
  · have top : i + 1 = 64 := by omega
    have step : guardB bop.BEQ (BitVec.ofNat 64 (i + 1)) 64#64 = true := by rw [top]; rfl
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput childX0080TSeg 0x80000080#64
          (childNextInput (BitVec.ofNat 64 i) p v d k a0) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [9, 8, 18, 15, 19, 20, 10]; decide
        shape := by change ChainOK _ [9, 8, 18, 15, 19, 20, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := childNext_code leaf.image
          chain_facts code with "Vsa.Sim.Code.child_at_"
          change guardB bop.BEQ (Functions.sign_extend (m := 64)
            (Sail.BitVec.extractLsb (BitVec.ofNat 64 i + Functions.sign_extend (m := 64) 1#12) 31 0)) 64#64 = true
          rw [addiw_one i small]
          exact step }))
    · rfl
    · rw [if_neg last]; rfl
    · simp only [childX0080TSeg, evalBlocks, evalBlock, SegEvalState.init, childnext_line_80000080,
        childnext_line_80000084, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG,
        eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff,
        ite_true, ite_false, childNextInput, childNextOutput]
      rw [addiw_one i small]
      rfl
    · rfl
    · decide

/-- The first slot after the root. -/
def childFirst : BitVec 64 := BitVec.ofNat 64 (Layout.sym_files + 56)

def childSlots (ra s0 s1 s2 s3 s4 s5 : BitVec 64) : List (Nat × BitVec 64) :=
  [(48, s0), (40, s1), (32, s2), (24, s3), (16, s4), (8, s5), (56, ra)]
def childLog (sp ra s0 s1 s2 s3 s4 s5 : BitVec 64) : List WEntry := nativeWordLog sp 64 (childSlots ra s0 s1 s2 s3 s4 s5)
def childInput (sp ra s0 s1 s2 s3 s4 s5 d name k a5 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (1, ra), (10, d), (11, name), (12, k), (15, a5)]

theorem childLog_inside {sp ra s0 s1 s2 s3 s4 s5} (frame : NativeFrame sp 64) :
    LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (childLog sp ra s0 s1 s2 s3 s4 s5) := by
  apply frame.word_log_inside
  intro off value member
  simp only [childSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

def childEntered (sp ra d name k a5 : BitVec 64) : GRegs :=
  [(18, 64#64), (9, 1#64), (8, childFirst), (20, k), (21, name), (19, d), (2, nativeStack sp 64), (1, ra),
    (10, d), (11, name), (12, k), (15, a5)]

theorem child_prologue (c : Config) (sp ra s0 s1 s2 s3 s4 s5 d name k a5 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (childInput sp ra s0 s1 s2 s3 s4 s5 d name k a5)) :
    FnSummary 0x80000040#64 (fun e => e = c)
      (WriteRegistersPost [2, 19, 21, 20, 8, 9, 18] (childLog sp ra s0 s1 s2 s3 s4 s5) c 0x8000008c#64 d
        (childEntered sp ra d name k a5)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (childLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput childX0040Seg 0x80000040#64
        (childInput sp ra s0 s1 s2 s3 s4 s5 d name k a5) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8, 9, 18, 19, 20, 21, 1, 10, 11, 12, 15]; decide
      shape := by change ChainOK _ [2, 8, 9, 18, 19, 20, 21, 1, 10, 11, 12, 15] _; decide
      tick := leaf.tick
      facts := by
        have code := childPrologue_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.child_at_"
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · simp only [childX0040Seg, evalBlocks, evalBlock, SegEvalState.init, childprologue_line_80000040, childprologue_line_80000044, childprologue_line_80000048, childprologue_line_8000004c, childprologue_line_80000050, childprologue_line_80000054, childprologue_line_80000058, childprologue_line_8000005c, childprologue_line_80000060, childprologue_line_80000064, childprologue_line_80000068, childprologue_line_8000006c, childprologue_line_80000070, childprologue_line_80000074, childprologue_line_80000078, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, childInput, childEntered]
    have zero : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide
    have down : Functions.sign_extend (m := 64) 4032#12 = -BitVec.ofNat 64 64 := by decide
    rw [zero, down, BitVec.add_zero, BitVec.add_zero, BitVec.add_zero]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and, nativeStack]
    decide
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
