import OCaml.Vm.Boot.Startup.StrncmpLoop
import OCaml.Vm.Boot.Startup.StrncmpDispatch
import OCaml.Vm.Boot.Startup.StrncmpReturn
import Vsa.Sim.GRegsFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

theorem strncmpEnd_cursor (p : BitVec 64) (last : Nat) :
    strncmpEnd p (BitVec.ofNat 64 (last + 1)) = nameCursor p last := by
  unfold strncmpEnd nameCursor
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp only [show BitVec.ofNat 64 1 + (-1#64) = 0#64 from rfl, BitVec.add_zero]

def strncmpEqualRegs (p q ra : BitVec 64) (last : Nat) (byte : Nat → BitVec 8) : GRegs :=
  [(10, 0#64), (1, ra), (11, nameCursor q (last + 1)), (12, nameCursor p last),
   (15, nameByteWord (byte last)), (14, nameByteWord (byte last))]

/-- Complete native strncmp for equal nonzero prefixes on its unaligned byte
path. The length is arbitrary; the comparison loop is folded, not evaluated. -/
theorem strncmp_equal (c : Config) (p q ra : BitVec 64) (last : Nat) (byte : Nat → BitVec 8)
    (leaf : LeafInput ra c) (data : EqualPrefix p q last byte c)
    (regs : GHolds c.σ (strncmpFirstInput p q (BitVec.ofNat 64 (last + 1))))
    (unaligned : strncmpAlignment p q ≠ 0#64) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [10, 11, 12, 14, 15] [] c ra 0#64 (strncmpEqualRegs p q ra last byte)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have positive : BitVec.ofNat 64 (last + 1) ≠ 0#64 := by
    have upper := data.left.upper
    intro eq
    have natEq := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at natEq
    rw [Nat.mod_eq_of_lt (by omega)] at natEq
    omega
  obtain ⟨entry, dispatchRun, dispatch⟩ := (strncmp_dispatch c p q _ ra leaf regs positive unaligned).run c ⟨pc, rfl⟩
  have entryLeaf : LeafInput ra entry := ⟨dispatch.good, dispatch.image, dispatch.minstret,
    (dispatch.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, dispatch.tick⟩
  have entryRegs : GHolds entry.σ (strncmpFirstInput p q (BitVec.ofNat 64 (last + 1))) :=
    dispatch.regs.2
  have leftWindow : ReadWindow p 1 := by simpa only [nameCursor, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using name_window data.left (k := 0) (Nat.zero_le _)
  have rightWindow : ReadWindow q 1 := by simpa only [nameCursor, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using name_window data.right (k := 0) (Nat.zero_le _)
  have dispatchMemory : entry.σ.mem = c.σ.mem := dispatch.memory
  have pinL : (entry.σ.mem[p.toNat]?).getD 0 = byte 0 := by
    rw [dispatchMemory]; simpa only [Nat.add_zero] using data.leftByte 0 (Nat.zero_le _)
  have pinR : (entry.σ.mem[q.toNat]?).getD 0 = byte 0 := by
    rw [dispatchMemory]; simpa only [Nat.add_zero] using data.rightByte 0 (Nat.zero_le _)
  obtain ⟨firstState, firstRun, first⟩ := (strncmp_first entry p q _ ra (byte 0) entryLeaf entryRegs leftWindow rightWindow pinL pinR).run entry ⟨dispatch.pc, rfl⟩
  have start : StrncmpAt p q ra last 0 byte c firstState := {
    leaf := ⟨first.good, first.image, first.minstret,
      (first.frame .x1 (by decide) (by decide)).trans entryLeaf.raReg, leaf.aligned, first.tick⟩
    bound := Nat.zero_le _
    pc := first.pc
    regs := by
      have cursor0 (a : BitVec 64) : nameCursor a 0 = a := BitVec.add_zero a
      rw [show strncmpTestInput (nameCursor p 0) (nameCursor q 0) (nameCursor p last) (byte 0) =
        [(10, p), (11, q), (12, nameCursor p last), (15, nameByteWord (byte 0)), (14, nameByteWord (byte 0))] from by rw [cursor0, cursor0]; rfl]
      refine ⟨first.result, gholds_lookup (n := 11) _ first.regs (by rfl), ?_,
        gholds_lookup (n := 15) _ first.regs (by rfl), gholds_lookup (n := 14) _ first.regs (by rfl), trivial⟩
      have stop := gholds_lookup (n := 12) _ first.regs (by rfl)
      rw [strncmpEnd_cursor] at stop
      exact stop
    memory := first.memory.trans dispatch.memory
    output := first.output.trans dispatch.output
    frame := fun r outside noise =>
      (first.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise).trans
        (dispatch.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise) }
  obtain ⟨lastState, loopRun, finished⟩ := strncmp_loop c data firstState start
  obtain ⟨exitState, testRun, tested⟩ := (strncmp_test lastState _ _ _ ra (byte last) true finished.leaf finished.regs (by simp)).run lastState ⟨finished.pc, rfl⟩
  have exitLeaf : LeafInput ra exitState := ⟨tested.good, tested.image, tested.minstret,
    (tested.frame .x1 (by decide) (by decide)).trans finished.leaf.raReg, leaf.aligned, tested.tick⟩
  obtain ⟨after, returnRun, returned⟩ := (strncmp_return exitState ra exitLeaf).run exitState ⟨tested.pc, rfl⟩
  refine ⟨after, dispatchRun.trans (firstRun.trans (loopRun.trans (testRun.trans returnRun))), ⟨⟨returned.good,
    returned.image, returned.minstret, returned.tick, returned.pc, returned.result,
    returned.memory.trans (tested.memory.trans finished.memory),
    returned.output.trans (tested.output.trans finished.output), ?_⟩, ?_⟩⟩
  · intro r outside noise
    exact (returned.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise).trans
      ((tested.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise).trans (finished.frame r outside noise))
  · refine ⟨returned.result, gholds_lookup (n := 1) _ returned.regs (by rfl), ?_,
      (returned.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ tested.regs (by rfl)),
      (returned.frame .x15 (by decide) (by decide)).trans (gholds_lookup (n := 15) _ tested.regs (by rfl)),
      (returned.frame .x14 (by decide) (by decide)).trans (gholds_lookup (n := 14) _ tested.regs (by rfl)), trivial⟩
    have next := gholds_lookup (n := 11) _ tested.regs (by rfl)
    rw [nameCursor_next] at next
    exact (returned.frame .x11 (by decide) (by decide)).trans next
end OCaml.Vm.Boot.Startup
