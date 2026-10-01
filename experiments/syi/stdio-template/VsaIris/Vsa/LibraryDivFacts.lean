import VsaIris.Vsa.LibraryStepTac
import Vsa.Sim.DivLoops
namespace VsaIris.Interp
theorem div_of_inv {n d q r : Nat} (hd : 0 < d) (h : n = d * q + r) (hr : r < d) :
    q = n / d ∧ r = n % d := by
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

abbrev DivKeep (R R0 : Nat → BitVec 64) : Prop := ∀ z, z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R z = R0 z

theorem shr1_toNat' (x : BitVec 64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_of_toInt_nonpos {a : BitVec 64} (h : a.toInt ≤ 0) (hne : a.toNat ≠ 0) : 2 ^ 63 ≤ a.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega

theorem toNat_of_toInt_pos {a : BitVec 64} (h : ¬ a.toInt ≤ 0) : a.toNat < 2 ^ 63 := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega

theorem shl1_toNat {a : BitVec 64} (h : a.toNat < 2 ^ 63) : (a <<< 1).toNat = 2 * a.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega

end VsaIris.Interp
