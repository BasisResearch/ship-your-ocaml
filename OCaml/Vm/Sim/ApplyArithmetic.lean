import OCaml.Vm.Sim.IndexWord

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- Extracting the low 32 bits of a bounded natural native word. -/
theorem low32_nat (n : Nat) (small : n < 2^64) :
    (BitVec.ofNat 64 n).extractLsb' 0 32 = BitVec.ofNat 32 n := by
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt small]

/-- Small natural operands retain their value across a signed 32-bit load. -/
theorem sign_extend_nat32 (n : Nat) (small : n < 2^31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have fits : n < 2^32 := by omega
  have msb : (BitVec.ofNat 32 n).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simp only [show ¬ 2^31 ≤ n by omega, decide_false]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_signExtend, msb, Bool.false_eq_true, ite_false,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, Nat.add_zero]

/-- APPLY's ADDIW computes its positive arity minus one without signed wrap. -/
theorem apply_count_word (n : BitVec 32) (positive : 0 < n.toInt) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (sign_extend (m := 64) n + sign_extend (m := 64) (0xfff#12)) 31 0) =
      BitVec.ofNat 64 (n.toInt.toNat - 1) := by
  have signed : n.toInt = (n.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · rfl
    · have range := n.isLt
      rw [BitVec.toInt_eq_toNat_cond] at positive
      split at positive <;> omega
  have small : n.toNat < 2^31 := by
    have range := n.isLt
    rw [BitVec.toInt_eq_toNat_cond] at signed
    split at signed <;> omega
  have nat : n.toInt.toNat = n.toNat := by rw [signed]; rfl
  have loaded : sign_extend (m := 64) n = BitVec.ofNat 64 n.toNat := by
    change BitVec.ofInt 64 n.toInt = _
    rw [signed]; rfl
  rw [loaded, nat, show sign_extend (m := 64) (0xfff#12) = -(1#64) from by decide,
    ← BitVec.sub_eq_add_neg, BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega)]
  change ((BitVec.ofNat 64 (n.toNat - 1)).extractLsb' 0 32).signExtend 64 = _
  rw [low32_nat _ (by omega)]
  exact sign_extend_nat32 _ (by omega)

end OCaml.Vm.Sim
