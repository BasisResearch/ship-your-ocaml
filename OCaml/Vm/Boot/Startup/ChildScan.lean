import OCaml.Vm.Boot.Startup.ChildCheck
import OCaml.Vm.Boot.Startup.ChildNextNormalized
import OCaml.Vm.Boot.Startup.ChildNextImage
import OCaml.Vm.Boot.Startup.IndexedLoop
import OCaml.Vm.Boot.Startup.ChildMissNormalized
import OCaml.Vm.Boot.Startup.ChildMissImage
import OCaml.Vm.Boot.Startup.ChildReturnNormalized
import OCaml.Vm.Boot.Startup.ChildReturnImage
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Boot.Startup.ChildPrologueNormalized
import OCaml.Vm.Boot.Startup.ChildPrologueImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

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

/-- Slot `i` of htif.c's `files` table. -/
def fileSlot (i : Nat) : BitVec 64 := BitVec.ofNat 64 (Layout.sym_files + 56 * i)

theorem fileSlot_nat {i : Nat} (small : i ≤ 64) : (fileSlot i).toNat = Layout.sym_files + 56 * i := by
  unfold fileSlot Layout.sym_files
  rw [BitVec.toNat_ofNat]
  omega

theorem fileSlot_window {i : Nat} (small : i < 64) : SlotWindow (fileSlot i) := by
  have nat := fileSlot_nat (Nat.le_of_lt small)
  constructor <;> rw [nat] <;> unfold Layout.sym_files
  · omega
  · omega
  · right; unfold Layout.sym_tohost; omega

theorem fileSlot_next (i : Nat) : fileSlot i + 56#64 = fileSlot (i + 1) := by
  unfold fileSlot
  rw [Nat.mul_succ, ← Nat.add_assoc, BitVec.ofNat_add (Layout.sym_files + 56 * i) 56]

/-- a5 at the head of slot `i`: the caller's value, then the last failed test. -/
def childPrev (a5 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (d : BitVec 64) (i : Nat) : BitVec 64 :=
  if i = 1 then a5 else slotMissValue m (Layout.sym_files + 56 * (i - 1)) d

/-- The scan at the head of slot `i` of a table that does not hold `(d, k)`. -/
structure ChildScanAt (d k a0 a5 ra : BitVec 64) (base : Config) (i : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  low : 1 ≤ i
  high : i ≤ 64
  pc : PCAt (if i < 64 then 0x8000008c#64 else 0x800000e8#64) c
  regs : GHolds c.σ (childNextInput (BitVec.ofNat 64 i) (fileSlot i) (childPrev a5 base.σ.mem d i) d k a0)
  memory : c.σ.mem = base.σ.mem
  output : c.σ.sailOutput = base.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [8, 9, 15], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = base.σ.regs.get? r

def childIndex (c : Config) : Nat := ((gprGet c.σ 9).getD 0).toNat

theorem ChildScanAt.index {d k a0 a5 ra base i c} (h : ChildScanAt d k a0 a5 ra base i c) : childIndex c = i := by
  have r := gholds_lookup (n := 9) _ h.regs (by rfl)
  have := h.high
  simp only [childIndex, r, Option.getD_some, BitVec.toNat_ofNat]
  omega

theorem child_scan_step {d k a0 a5 ra base i c} (miss : ∀ j, 1 ≤ j → j < 64 → SlotMiss base.σ.mem (Layout.sym_files + 56 * j) d k)
    (h : ChildScanAt d k a0 a5 ra base i c) (hi : i < 64) :
    ∃ e, Steps c e ∧ ChildScanAt d k a0 a5 ra base (i + 1) e := by
  have pc : PCAt 0x8000008c#64 c := by simpa only [hi, ite_true] using h.pc
  have slotMiss : SlotMiss c.σ.mem (fileSlot i).toNat d k := by
    rw [h.memory, fileSlot_nat (Nat.le_of_lt hi)]
    exact miss i h.low hi
  obtain ⟨a, run1, checked⟩ := (child_check c ra (fileSlot i) d k a0 h.leaf
    ⟨gholds_lookup (n := 8) _ h.regs (by rfl), gholds_lookup (n := 19) _ h.regs (by rfl),
      gholds_lookup (n := 20) _ h.regs (by rfl), gholds_lookup (n := 10) _ h.regs (by rfl), trivial⟩
    (fileSlot_window hi) slotMiss).run c ⟨pc, rfl⟩
  have keep (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [15])
      (hv : gprGet c.σ n = some v) : gprGet a.σ n = some v :=
    (checked.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  obtain ⟨e, run2, stepped⟩ := (child_next a ra (fileSlot i) (slotMissValue c.σ.mem (fileSlot i).toNat d) d k a0 i hi
    ⟨checked.good, checked.image, checked.minstret,
      (checked.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, checked.tick⟩
    ⟨keep 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ h.regs (by rfl)),
      gholds_lookup (n := 8) _ checked.regs (by rfl),
      keep 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ h.regs (by rfl)),
      gholds_lookup (n := 15) _ checked.regs (by rfl), gholds_lookup (n := 19) _ checked.regs (by rfl),
      gholds_lookup (n := 20) _ checked.regs (by rfl), gholds_lookup (n := 10) _ checked.regs (by rfl),
      trivial⟩).run a ⟨checked.pc, rfl⟩
  have memE : e.σ.mem = base.σ.mem :=
    (show e.σ.mem = a.σ.mem from stepped.memory).trans ((show a.σ.mem = c.σ.mem from checked.memory).trans h.memory)
  refine ⟨e, run1.trans run2, {
    leaf := ⟨stepped.good, stepped.image, stepped.minstret,
      (stepped.frame .x1 (by decide) (by decide)).trans ((checked.frame .x1 (by decide) (by decide)).trans
        h.leaf.raReg), h.leaf.aligned, stepped.tick⟩
    low := by omega
    high := by omega
    pc := stepped.pc
    regs := ?_
    memory := memE
    output := stepped.output.trans (checked.output.trans h.output)
    frame := fun r outside noise => ?_ }⟩
  · have prev : childPrev a5 base.σ.mem d (i + 1) = slotMissValue c.σ.mem (fileSlot i).toNat d := by
      unfold childPrev
      rw [if_neg (show ¬(i + 1 = 1) by have := h.low; omega), h.memory, fileSlot_nat (Nat.le_of_lt hi), Nat.add_sub_cancel]
    rw [prev, ← fileSlot_next]
    have r := stepped.regs
    exact ⟨gholds_lookup (n := 9) _ r (by rfl), gholds_lookup (n := 8) _ r (by rfl),
      gholds_lookup (n := 18) _ r (by rfl), gholds_lookup (n := 15) _ r (by rfl),
      gholds_lookup (n := 19) _ r (by rfl), gholds_lookup (n := 20) _ r (by rfl),
      gholds_lookup (n := 10) _ r (by rfl), trivial⟩
  · have sub1 : ∀ n ∈ [9, 8], n ∈ [8, 9, 15] := by decide
    have sub2 : ∀ n ∈ [15], n ∈ [8, 9, 15] := by decide
    exact (stepped.frame r (fun n hn => outside n (sub1 n hn)) noise).trans
      ((checked.frame r (fun n hn => outside n (sub2 n hn)) noise).trans (h.frame r outside noise))

theorem child_scan_loop {d k a0 a5 ra} (base : Config)
    (miss : ∀ j, 1 ≤ j → j < 64 → SlotMiss base.σ.mem (Layout.sym_files + 56 * j) d k) :
    Triple (ChildScanAt d k a0 a5 ra base 1) (ChildScanAt d k a0 a5 ra base 64) :=
  indexed_loop childIndex 64 1 _ (fun _ _ h => h.high) (fun _ _ h => h.index)
    (fun _ _ h hk => child_scan_step miss h hk)

/-- No slot matched: return -1. -/
theorem child_miss_exit (c : Config) (ra a0 : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, a0)]) :
    FnSummary 0x800000e8#64 (fun e => e = c)
      (WriteRegistersPost [9] [] c 0x800000c0#64 a0 [(9, -1#64), (10, a0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput childX00e8Seg 0x800000e8#64 [(10, a0)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := childMiss_code leaf.image
        chain_facts code with "Vsa.Sim.Code.child_at_" }))
  · rfl
  · rfl
  · simp only [childX00e8Seg, evalBlocks, evalBlock, SegEvalState.init, childmiss_line_800000e8, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.cons.injEq, Prod.mk.injEq]
    decide
  · rfl
  · decide

def childReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 64 + 56), read8 c.σ.mem (nativeFrameBase sp 64 + 48),
   read8 c.σ.mem (nativeFrameBase sp 64 + 32), read8 c.σ.mem (nativeFrameBase sp 64 + 24),
   read8 c.σ.mem (nativeFrameBase sp 64 + 16), read8 c.σ.mem (nativeFrameBase sp 64 + 8),
   read8 c.σ.mem (nativeFrameBase sp 64 + 40)]

theorem child_return (c : Config) (sp ra s0 s1 s2 s3 s4 s5 result oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ [(2, nativeStack sp 64), (9, result)])
    (saved : ∀ off value, (off, value) ∈ childSlots ra s0 s1 s2 s3 s4 s5 →
      bytesT c.σ.mem (nativeFrameBase sp 64 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800000c0#64 (fun e => e = c)
      (WriteRegistersPost [1, 8, 18, 19, 20, 21, 10, 9, 2] [] c ra result
        [(2, sp), (9, s1), (10, result), (21, s5), (20, s4), (19, s3), (18, s2), (8, s0), (1, ra)]) := by
  have savedRa := saved 56 ra (by simp [childSlots])
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput childX00c0Seg 0x800000c0#64
        [(2, nativeStack sp 64), (9, result)] (childReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 9]; decide
      shape := by change ChainOK _ [2, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := childReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.child_at_"
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [childX00c0Seg, evalBlocks, evalBlock, SegEvalState.init, childreturn_line_800000c0, childreturn_line_800000c4, childreturn_line_800000c8, childreturn_line_800000cc, childreturn_line_800000d0, childreturn_line_800000d4, childreturn_line_800000d8, childreturn_line_800000dc, childreturn_line_800000e0, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, childReturnLoads]
    have zero : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide
    have up : Functions.sign_extend (m := 64) 64#12 = 64#64 := by decide
    rw [read8_value, read8_value, read8_value, read8_value, read8_value, read8_value, read8_value, zero, up,
      BitVec.add_zero, nativeStack_restore, saved 40 s1 (by simp [childSlots]), saved 8 s5 (by simp [childSlots]),
      saved 16 s4 (by simp [childSlots]), saved 24 s3 (by simp [childSlots]), saved 32 s2 (by simp [childSlots]),
      saved 48 s0 (by simp [childSlots]), savedRa]
  · rfl
  · decide
/-- A slot's test depends only on its 24 bytes. -/
structure SlotSame (m m' : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) : Prop where
  byte : ∀ x, p ≤ x → x < p + 24 → (m'[x]?).getD 0 = (m[x]?).getD 0

theorem SlotSame.used {m m' p} (h : SlotSame m m' p) : slotUsed m' p = slotUsed m p :=
  h.byte p (Nat.le_refl _) (by omega)

theorem SlotSame.linked {m m' p} (h : SlotSame m m' p) : slotLinked m' p = slotLinked m p :=
  h.byte (p + 2) (by omega) (by omega)

theorem SlotSame.parent {m m' p} (h : SlotSame m m' p) : slotParent m' p = slotParent m p := by
  unfold slotParent read4
  rw [h.byte (p + 4) (by omega) (by omega), h.byte (p + 4 + 1) (by omega) (by omega),
    h.byte (p + 4 + 2) (by omega) (by omega), h.byte (p + 4 + 3) (by omega) (by omega)]

theorem SlotSame.length {m m' p} (h : SlotSame m m' p) : slotLength m' p = slotLength m p :=
  word_observed _ (fun i hi => h.byte _ (by omega) (by omega))

theorem SlotSame.value {m m' p d} (h : SlotSame m m' p) : slotMissValue m' p d = slotMissValue m p d := by
  unfold slotMissValue
  rw [h.used, h.linked, h.parent, h.length]

theorem SlotSame.miss {m m' p d k} (h : SlotSame m m' p) (miss : SlotMiss m p d k) : SlotMiss m' p d k := by
  rcases miss with a | ⟨a, b⟩ | ⟨a, b, e⟩ | ⟨a, b, e, f⟩
  · exact .unused (h.used.trans a)
  · exact .unlinked (h.used ▸ a) (h.linked.trans b)
  · exact .parent (h.used ▸ a) (h.linked ▸ b) (h.parent ▸ e)
  · exact .length (h.used ▸ a) (h.linked ▸ b) (h.parent ▸ e) (h.length ▸ f)

def childResult (sp ra s0 s1 s2 s3 s4 s5 v : BitVec 64) : GRegs :=
  [(2, sp), (9, s1), (10, -1#64), (21, s5), (20, s4), (19, s3), (18, s2), (8, s0), (1, ra), (15, v)]

/-- **`child(d, name, k)` over a table with no matching slot** returns -1,
restoring its caller's registers. -/
theorem child_miss (c : Config) (sp ra s0 s1 s2 s3 s4 s5 d name k a5 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (childInput sp ra s0 s1 s2 s3 s4 s5 d name k a5))
    (miss : ∀ j, 1 ≤ j → j < 64 → SlotMiss c.σ.mem (Layout.sym_files + 56 * j) d k) :
    FnSummary 0x80000040#64 (fun e => e = c)
      (WriteRegistersPost [2, 19, 21, 20, 8, 9, 18, 15, 1, 10] (childLog sp ra s0 s1 s2 s3 s4 s5) c ra (-1#64)
        (childResult sp ra s0 s1 s2 s3 s4 s5 (slotMissValue c.σ.mem (Layout.sym_files + 56 * 63) d))) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, opened⟩ := (child_prologue c sp ra s0 s1 s2 s3 s4 s5 d name k a5 leaf frame regs).run c ⟨pc, rfl⟩
  have lower := frame.lower
  have same (j : Nat) (hj : j < 64) : SlotSame c.σ.mem a.σ.mem (Layout.sym_files + 56 * j) := ⟨fun x lo hi => by
    rw [opened.memory, frameOn_writeLog _ _ _ (childLog_inside frame) x ⟨Or.inl (by
      show x < nativeFrameBase sp 64
      unfold nativeFrameBase Layout.sym_files Vsa.Sim.DlHeap.heapEnd at *
      omega), trivial⟩]⟩
  have leafA : LeafInput ra a := ⟨opened.good, opened.image, opened.minstret,
    gholds_lookup (n := 1) _ opened.regs (by rfl), leaf.aligned, opened.tick⟩
  have start : ChildScanAt d k d a5 ra a 1 a :=
    { leaf := leafA
      low := Nat.le_refl _
      high := by decide
      pc := opened.pc
      regs := ⟨gholds_lookup (n := 9) _ opened.regs (by rfl), gholds_lookup (n := 8) _ opened.regs (by rfl),
        gholds_lookup (n := 18) _ opened.regs (by rfl), gholds_lookup (n := 15) _ opened.regs (by rfl),
        gholds_lookup (n := 19) _ opened.regs (by rfl), gholds_lookup (n := 20) _ opened.regs (by rfl),
        gholds_lookup (n := 10) _ opened.regs (by rfl), trivial⟩
      memory := rfl
      output := rfl
      frame := fun _ _ _ => rfl }
  obtain ⟨b, run2, scanned⟩ := child_scan_loop a (fun j lo hi => (same j hi).miss (miss j lo hi)) a start
  have pcB : PCAt 0x800000e8#64 b := by simpa using scanned.pc
  obtain ⟨e, run3, exited⟩ := (child_miss_exit b ra d scanned.leaf
    ⟨gholds_lookup (n := 10) _ scanned.regs (by rfl), trivial⟩).run b ⟨pcB, rfl⟩
  have memE : e.σ.mem = a.σ.mem := (show e.σ.mem = b.σ.mem from exited.memory).trans scanned.memory
  have frameE (r : Register) (outside : ∀ n ∈ [8, 9, 15], gprReg n ≠ r)
      (noise : ∀ q ∈ noiseRegs, (q == r) = false) : e.σ.regs.get? r = a.σ.regs.get? r :=
    (exited.frame r (fun n hn => outside n (by simp at hn; simp [hn])) noise).trans (scanned.frame r outside noise)
  have stackE : gprGet e.σ 2 = some (nativeStack sp 64) :=
    (frameE .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ opened.regs (by rfl))
  obtain ⟨f, run4, returned⟩ := (child_return e sp ra s0 s1 s2 s3 s4 s5 (-1#64) ra
    ⟨exited.good, exited.image, exited.minstret, (frameE .x1 (by decide) (by decide)).trans leafA.raReg,
      leaf.aligned, exited.tick⟩ frame ⟨stackE, gholds_lookup (n := 9) _ exited.regs (by rfl), trivial⟩
    (fun off value member => by
      rw [memE, opened.memory]
      apply frame.word_log_read
      · intro k v hk
        simp only [childSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
        omega
      · simp [childSlots]
      · exact member) leaf.aligned).run e ⟨exited.pc, rfl⟩
  have a5F : gprGet f.σ 15 = some (slotMissValue c.σ.mem (Layout.sym_files + 56 * 63) d) := by
    have atB := gholds_lookup (n := 15) _ scanned.regs (by rfl)
    have prev : childPrev a5 a.σ.mem d 64 = slotMissValue c.σ.mem (Layout.sym_files + 56 * 63) d := by
      unfold childPrev
      rw [if_neg (by decide)]
      exact (same 63 (by decide)).value
    rw [prev] at atB
    exact (returned.frame .x15 (by decide) (by decide)).trans ((exited.frame .x15 (by decide) (by decide)).trans atB)
  refine ⟨f, run1.trans (run2.trans (run3.trans run4)), ⟨{
    good := returned.good
    image := returned.image
    minstret := returned.minstret
    tick := returned.tick
    pc := returned.pc
    result := returned.result
    memory := (show f.σ.mem = e.σ.mem from returned.memory).trans (memE.trans opened.memory)
    output := returned.output.trans (exited.output.trans (scanned.output.trans opened.output))
    frame := fun r outside noise => ?_ }, ?_⟩⟩
  · have mem (l : List Nat) (sub : ∀ n ∈ l, n ∈ [2, 19, 21, 20, 8, 9, 18, 15, 1, 10]) : ∀ n ∈ l, gprReg n ≠ r :=
      fun n hn => outside n (sub n hn)
    exact (returned.frame r (mem _ (by decide)) noise).trans ((exited.frame r (mem _ (by decide)) noise).trans
      ((scanned.frame r (mem _ (by decide)) noise).trans (opened.frame r (mem _ (by decide)) noise)))
  · have r := returned.regs
    exact ⟨gholds_lookup (n := 2) _ r (by rfl), gholds_lookup (n := 9) _ r (by rfl),
      gholds_lookup (n := 10) _ r (by rfl), gholds_lookup (n := 21) _ r (by rfl),
      gholds_lookup (n := 20) _ r (by rfl), gholds_lookup (n := 19) _ r (by rfl),
      gholds_lookup (n := 18) _ r (by rfl), gholds_lookup (n := 8) _ r (by rfl),
      gholds_lookup (n := 1) _ r (by rfl), a5F, trivial⟩
end OCaml.Vm.Boot.Startup
