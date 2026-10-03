import OCaml.Vm.Sim.TrapArithmetic
import OCaml.Vm.Sim.RetaddrStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Dividing a bounded byte displacement by the word size is an unsigned
operation even when the native instruction uses arithmetic right shift. -/
theorem trap_shift_words (n : Nat) (small : 8 * n < 2^63) :
    (BitVec.ofNat 64 (8 * n)).sshiftRight 3 = BitVec.ofNat 64 n := by
  have inWord : 8 * n < 2^64 := by omega
  have msb : (BitVec.ofNat 64 (8 * n)).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inWord]
    simp only [show ¬ 2^63 ≤ 8 * n by omega, decide_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight_of_msb_false msb]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inWord, Nat.shiftRight_eq_div_pow]
  omega

/-- The native relative trap link is the tagged logical depth difference. -/
theorem pushtrap_link {sp high depth trap : Nat}
    (shape : sp + 8 * depth = high) (room : 32 ≤ sp)
    (small : high < 2^63) (bound : trap ≤ depth + 4) :
    (((BitVec.ofNat 64 (high - 8 * trap) - BitVec.ofNat 64 (sp - 32)).sshiftRight 3 <<< (1 : Nat)) + 1#64) =
      tag64 (BitVec.ofNat 63 (depth + 4 - trap)) := by
  have difference : high - 8 * trap - (sp - 32) = 8 * (depth + 4 - trap) := by omega
  have ordered : sp - 32 ≤ high - 8 * trap := by omega
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) ordered, difference, trap_shift_words _ (by omega)]
  exact retaddr_extra_word _

end OCaml.Vm.Sim
