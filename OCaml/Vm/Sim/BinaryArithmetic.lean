import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

/-- ADDINT adjusts one tag bit before adding the represented operands. -/
theorem tag_add (m n : BitVec 63) : tag64 m - 1#64 + tag64 n = tag64 (m + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub, tag_toNat, tag_toNat, tag_toNat, BitVec.toNat_add]
  have hm := m.isLt
  have hn := n.isLt
  change (((2^64 - 1 + (2 * m.toNat + 1)) % 2^64) + (2 * n.toNat + 1)) % 2^64 =
    2 * ((m.toNat + n.toNat) % 2^63) + 1
  omega

/-- Every odd native word is exactly the tag of its semantic untagging.
Bitwise and shift arms discharge the single low-bit premise. -/
theorem tag_untag_odd (w : BitVec 64) (odd : w.getLsbD 0 = true) :
    tag64 (untag w) = w := by
  have parity : w.toNat % 2 = 1 := by
    simpa only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq] using odd
  apply BitVec.eq_of_toNat_eq
  rw [tag_toNat]
  unfold untag
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sshiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  have hw := w.isLt
  split <;> omega

end OCaml.Vm.Sim
