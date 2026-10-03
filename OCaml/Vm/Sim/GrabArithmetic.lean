import OCaml.Vm.Sim.ReturnArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- GRAB's signed native comparison agrees with bounded natural extra counts. -/
theorem grab_fast_guard (extra : Nat) (count : BitVec 32)
    (small : extra < 2^63) (nonnegative : 0 ≤ count.toInt) (enough : count.toInt.toNat ≤ extra) :
    zopz0zI_s (BitVec.ofNat 64 extra) (sign_extend (m := 64) count) = false := by
  rw [nonnegative_word32 count nonnegative]
  unfold zopz0zI_s
  rw [nat64_toInt extra small, nat64_toInt count.toInt.toNat (by omega)]
  exact decide_eq_false (by omega)

/-- Subtracting satisfied arity preserves the natural extra-argument counter. -/
theorem grab_fast_extra (extra : Nat) (count : BitVec 32)
    (small : extra < 2^63) (nonnegative : 0 ≤ count.toInt) (enough : count.toInt.toNat ≤ extra) :
    BitVec.ofNat 64 extra - sign_extend (m := 64) count = BitVec.ofNat 64 (extra - count.toInt.toNat) := by
  rw [nonnegative_word32 count nonnegative]
  exact BitVec.ofNat_sub_ofNat_of_le extra count.toInt.toNat (by omega) enough

end OCaml.Vm.Sim
