import OCaml.Vm.Boot.Startup.ChildScan
import OCaml.Vm.Boot.Startup.ChildCompareNormalized
import OCaml.Vm.Boot.Startup.ChildCompareCallInterface
import OCaml.Vm.Boot.Startup.ChildCompareImage
import OCaml.Vm.Boot.Startup.ChildCompareTestNormalized
import OCaml.Vm.Boot.Startup.ChildCompareTestImage
import OCaml.Vm.Boot.Startup.MemcmpRun
import OCaml.Vm.Boot.Startup.BlockCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The slot at `p` is directory `d`'s entry of length `k`: compare its name
with `memcmp(name_p, name, k)`. -/
theorem child_hit_compare (c : Config) (ra p d k a0 name node : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (childCheckInput p d k a0 ++ [(21, name)])) (window : SlotWindow p)
    (used : slotUsed c.σ.mem p.toNat ≠ 0#8) (linked : slotLinked c.σ.mem p.toNat ≠ 0#8)
    (parent : slotParent c.σ.mem p.toNat = d) (length : slotLength c.σ.mem p.toNat = k)
    (namePtr : bytesT c.σ.mem (p.toNat + 8) 8 = node) :
    FnSummary 0x8000008c#64 (fun e => e = c)
      (WriteRegistersPost ([15, 10, 12, 11] ++ [1]) [] c jal_800000b8_call.target node
        ((1, jal_800000b8_call.link) :: [(11, name), (12, k), (10, node), (15, k), (8, p), (19, d), (20, k),
          (21, name)])) := by
  apply block_then_call c jal_800000b8_call_shape jal_800000b8_call_decode (fun _ h => jal_800000b8_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (childX008cFSeg ++ childX0094FSeg ++ childX009cFSeg ++ childX00a4FSeg ++
        childCompareSave) 0x8000008c#64 (childCheckInput p d k a0 ++ [(21, name)])
        [[slotUsed c.σ.mem p.toNat], [slotLinked c.σ.mem p.toNat], read4 c.σ.mem (p.toNat + 4),
          read8 c.σ.mem (p.toNat + 16), read8 c.σ.mem (p.toNat + 8)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 19, 20, 10, 21]; decide
      shape := by change ChainOK _ [8, 19, 20, 10, 21] _; decide
      tick := leaf.tick
      facts := by
        have code := childUsed_code leaf.image
        have code2 := childCompare_code leaf.image
        chain_facts code with "Vsa.Sim.Code.child_at_"
        · exact (window.read 0 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
        · change guardB bop.BEQ (bytesVal .lbu [slotUsed c.σ.mem p.toNat]) 0#64 = false
          rw [name_lbu_value]
          exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of used (by decide))
        · exact (window.read 2 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
        · change guardB bop.BEQ (bytesVal .lbu [slotLinked c.σ.mem p.toNat]) 0#64 = false
          rw [name_lbu_value]
          exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of linked (by decide))
        · exact (window.read 4 4 (by decide)).lw rfl rfl (by rw [window.nat (by decide)]; exact read4_pins _ _)
        · change guardB bop.BNE (slotParent c.σ.mem p.toNat) d = false
          rw [parent]; exact bne_self_eq_false d
        · exact (window.read 16 8 (by decide)).ld rfl rfl (by rw [window.nat (by decide)]; exact read8_pins _ _)
        · change guardB bop.BNE (bytesVal .ld (read8 c.σ.mem (p.toNat + 16))) k = false
          rw [read8_value]
          change guardB bop.BNE (slotLength c.σ.mem p.toNat) k = false
          rw [length]; exact bne_self_eq_false k
        · exact (window.read 8 8 (by decide)).ld rfl rfl (by rw [window.nat (by decide)]; exact read8_pins _ _) }))
  · rfl
  · rfl
  · simp only [childX008cFSeg, childX0094FSeg, childX009cFSeg, childX00a4FSeg, childCompareSave, evalBlocks,
      evalBlock, SegEvalState.init, childlinked_line_80000094, childused_line_8000008c, childlength_line_800000a4,
      childparent_line_8000009c, childcompare_line_800000ac, childcompare_line_800000b0, childcompare_line_800000b4,
      runGM, ldsRunM, wlogM, stepGM, stepLdsM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.cons_append, List.nil_append,
      childCheckInput]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero, read8_value,
      read8_value, namePtr]
    change [(11, name), (12, k), (10, node), (15, slotLength c.σ.mem p.toNat), (8, p), (19, d), (20, k), (21, name)] = _
    rw [length]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- `memcmp` returned 0: the slot names the component. -/
theorem child_hit_test (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, 0#64)]) :
    FnSummary 0x800000bc#64 (fun e => e = c) (WriteRegistersPost [] [] c 0x800000c0#64 0#64 [(10, 0#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput childX00bcFSeg 0x800000bc#64 [(10, 0#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := childCompareTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.child_at_"
        change guardB bop.BNE 0#64 0#64 = false
        decide }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

def childHitResult (sp ra s0 s1 s2 s3 s4 s5 : BitVec 64) : GRegs :=
  [(2, sp), (9, s1), (10, 1#64), (21, s5), (20, s4), (19, s3), (18, s2), (8, s0), (1, ra)]

/-- **`child(d, name, k)` when slot 1 is the entry**: it returns 1. -/
theorem child_hit (c : Config) (sp ra s0 s1 s2 s3 s4 s5 d name a5 node : BitVec 64) (k : Nat)
    (leaf : LeafInput ra c) (present : GprPresent c.σ) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (childInput sp ra s0 s1 s2 s3 s4 s5 d name (BitVec.ofNat 64 k) a5))
    (used : slotUsed c.σ.mem (Layout.sym_files + 56) ≠ 0#8)
    (linked : slotLinked c.σ.mem (Layout.sym_files + 56) ≠ 0#8)
    (parent : slotParent c.σ.mem (Layout.sym_files + 56) = d)
    (length : slotLength c.σ.mem (Layout.sym_files + 56) = BitVec.ofNat 64 k)
    (namePtr : bytesT c.σ.mem (Layout.sym_files + 56 + 8) 8 = node)
    (lo : 1 ≤ k) (hi : k ≤ 7) (nodeWin : ReadWindow node (k + 1)) (nameWin : ReadWindow name (k + 1))
    (nodeLow : node.toNat + k < nativeFrameBase sp 64) (nameLow : name.toNat + k < nativeFrameBase sp 64)
    (same : ∀ j, j < k → (c.σ.mem[node.toNat + j]?).getD 0 = (c.σ.mem[name.toNat + j]?).getD 0) :
    FnSummary 0x80000040#64 (fun e => e = c)
      (WriteRegistersPost [2, 19, 21, 20, 8, 9, 18, 15, 10, 12, 11, 1, 13, 14] (childLog sp ra s0 s1 s2 s3 s4 s5) c ra
        1#64 (childHitResult sp ra s0 s1 s2 s3 s4 s5)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, opened⟩ := (child_prologue c sp ra s0 s1 s2 s3 s4 s5 d name (BitVec.ofNat 64 k) a5 leaf frame
    regs).run c ⟨pc, rfl⟩
  have lower := frame.lower
  have keep (x : Nat) (low : x < nativeFrameBase sp 64) : (a.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [opened.memory, frameOn_writeLog _ _ _ (childLog_inside frame) x ⟨Or.inl low, trivial⟩]
  have slotLow (off : Nat) (hoff : off < 56) : Layout.sym_files + 56 + off < nativeFrameBase sp 64 := by
    unfold nativeFrameBase Layout.sym_files Vsa.Sim.DlHeap.heapEnd at *; omega
  have sameSlot : SlotSame c.σ.mem a.σ.mem (Layout.sym_files + 56 * 1) := ⟨fun x lo hi => by
    rw [keep x (by unfold nativeFrameBase Layout.sym_files Vsa.Sim.DlHeap.heapEnd at *; omega)]⟩
  have leafA : LeafInput ra a := ⟨opened.good, opened.image, opened.minstret,
    gholds_lookup (n := 1) _ opened.regs (by rfl), leaf.aligned, opened.tick⟩
  have slotNat : (childFirst).toNat = Layout.sym_files + 56 := by decide
  have namePtrA : bytesT a.σ.mem (childFirst.toNat + 8) 8 = node := by
    rw [slotNat, word_observed (m := c.σ.mem) _ (fun i hi => keep _ (by
      have := slotLow (8 + i) (by omega); omega))]
    exact namePtr
  obtain ⟨b, run2, cmp⟩ := (child_hit_compare a ra childFirst d (BitVec.ofNat 64 k) d name node leafA
    ⟨gholds_lookup (n := 8) _ opened.regs (by rfl), gholds_lookup (n := 19) _ opened.regs (by rfl),
      gholds_lookup (n := 20) _ opened.regs (by rfl), gholds_lookup (n := 10) _ opened.regs (by rfl),
      gholds_lookup (n := 21) _ opened.regs (by rfl), trivial⟩ (fileSlot_window (i := 1) (by decide))
    (by rw [slotNat, show Layout.sym_files + 56 = Layout.sym_files + 56 * 1 from rfl, sameSlot.used]; exact used)
    (by rw [slotNat, show Layout.sym_files + 56 = Layout.sym_files + 56 * 1 from rfl, sameSlot.linked]; exact linked)
    (by rw [slotNat, show Layout.sym_files + 56 = Layout.sym_files + 56 * 1 from rfl, sameSlot.parent]; exact parent)
    (by rw [slotNat, show Layout.sym_files + 56 = Layout.sym_files + 56 * 1 from rfl, sameSlot.length]; exact length)
    namePtrA).run a ⟨opened.pc, rfl⟩
  have memB : b.σ.mem = a.σ.mem := cmp.memory
  have presentA := opened.present present (by decide) (by simp only [childEntered, keysG]; decide)
  have presentB := cmp.present presentA (by decide) (by simp only [keysG]; decide)
  obtain ⟨e, run3, D⟩ := (memcmp_equal b jal_800000b8_call.link node name k
    ⟨cmp.good, cmp.image, cmp.minstret, gholds_lookup (n := 1) _ cmp.regs (by rfl), by decide, cmp.tick⟩
    ⟨gholds_lookup (n := 10) _ cmp.regs (by rfl), gholds_lookup (n := 11) _ cmp.regs (by rfl),
      gholds_lookup (n := 12) _ cmp.regs (by rfl), gholds_lookup (n := 1) _ cmp.regs (by rfl), trivial⟩
    presentB lo hi nodeWin nameWin (fun j hj => by
      rw [memB, keep _ (by omega), keep _ (by omega)]; exact same j hj)).run b
    ⟨cmp.pc, rfl⟩
  obtain ⟨f, run4, T⟩ := (child_hit_test e _ D.toLeafInput ⟨D.result, trivial⟩).run e ⟨D.pc, rfl⟩
  have frameF (r : Register) (outside : ∀ n ∈ [10, 13, 12, 15, 14, 11, 1], gprReg n ≠ r)
      (noise : ∀ q ∈ noiseRegs, (q == r) = false) : f.σ.regs.get? r = a.σ.regs.get? r := by
    have mem (l : List Nat) (sub : ∀ n ∈ l, n ∈ [10, 13, 12, 15, 14, 11, 1]) : ∀ n ∈ l, gprReg n ≠ r :=
      fun n hn => outside n (sub n hn)
    exact (T.frame r (mem _ (by decide)) noise).trans ((D.frame r (mem _ (by decide)) noise).trans
      (cmp.frame r (mem _ (by decide)) noise))
  have memF : f.σ.mem = a.σ.mem := (show f.σ.mem = e.σ.mem from T.memory).trans (D.memory.trans memB)
  obtain ⟨g, run5, returned⟩ := (child_return f sp ra s0 s1 s2 s3 s4 s5 1#64 jal_800000b8_call.link
    ⟨T.good, T.image, T.minstret, (T.frame .x1 (by decide) (by decide)).trans D.raReg, by decide, T.tick⟩ frame
    ⟨(frameF .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ opened.regs (by rfl)),
      (frameF .x9 (by decide) (by decide)).trans (gholds_lookup (n := 9) _ opened.regs (by rfl)), trivial⟩
    (fun off value member => by
      rw [memF, opened.memory]
      apply frame.word_log_read
      · intro k v hk
        simp only [childSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
        omega
      · simp [childSlots]
      · exact member) leaf.aligned).run f ⟨T.pc, rfl⟩
  refine ⟨g, run1.trans (run2.trans (run3.trans (run4.trans run5))), {
    good := returned.good
    image := returned.image
    minstret := returned.minstret
    tick := returned.tick
    pc := returned.pc
    result := returned.result
    memory := (show g.σ.mem = f.σ.mem from returned.memory).trans (memF.trans opened.memory)
    output := returned.output.trans (T.output.trans (D.output.trans (cmp.output.trans opened.output)))
    frame := fun r outside noise => ?_
    kept := opened.kept.trans (cmp.kept.trans ((GprsKept.of_regFrame (W := memcmpWrites) (by decide) (by decide)
      (fun n hn => have b := (show KeysOK memcmpWrites by decide) n hn; D.present.get n b.1 (by omega))
      D.frame).trans (T.kept.trans returned.kept)))
    regs := returned.regs }⟩
  have mem (l : List Nat) (sub : ∀ n ∈ l, n ∈ [2, 19, 21, 20, 8, 9, 18, 15, 10, 12, 11, 1, 13, 14]) :
      ∀ n ∈ l, gprReg n ≠ r := fun n hn => outside n (sub n hn)
  exact (returned.frame r (mem _ (by decide)) noise).trans ((T.frame r (mem _ (by decide)) noise).trans
    ((D.frame r (mem _ (by decide)) noise).trans ((cmp.frame r (mem _ (by decide)) noise).trans
      (opened.frame r (mem _ (by decide)) noise))))
end OCaml.Vm.Boot.Startup
