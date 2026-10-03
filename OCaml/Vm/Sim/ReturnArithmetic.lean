import OCaml.Vm.Sim.IndexWord

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- Bounded native extra-argument counts have their ordinary signed value. -/
theorem nat64_toInt (n : Nat) (small : n < 2^63) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2^64 by omega)]
  split <;> omega

/-- A positive extra-argument count takes RETURN's closure-entry path. -/
theorem return_more_guard (n : Nat) (positive : 0 < n) (small : n < 2^63) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 n) = false := by
  unfold zopz0zKzJ_s
  rw [nat64_toInt n small]
  exact decide_eq_false (by change ¬ (0 : Int) ≥ (n : Int); omega)

/-- Decrementing a positive native count agrees with natural subtraction. -/
theorem extra_decrement (n : Nat) (positive : 0 < n) :
    BitVec.ofNat 64 n + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 (n - 1) := by
  rw [show sign_extend (m := 64) (0xfff#12) = -(1#64) from by decide, ← BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) (by omega)

end OCaml.Vm.Sim
