import OCaml.Vm.Boot.Startup.LookupAdvance

namespace OCaml.Vm.Boot.Startup
open LeanRV64DExecutable.Functions

/-- The signed 32-bit index instruction increments an in-range table index. -/
theorem nextLookupIndex_nat (i : Nat) (bound : i + 1 < 2^31) :
    nextLookupIndex (BitVec.ofNat 64 i) = BitVec.ofNat 64 (i + 1) := by
  unfold nextLookupIndex sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  rw [BitVec.extractLsb_ofNat]
  have h64 : i + 1 < 2^64 := by omega
  simp only [Nat.mod_eq_of_lt h64, Nat.shiftRight_zero]
  have h32 : i + 1 < 2^32 := by omega
  have msb : (BitVec.ofNat 32 (i + 1)).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) h32

/-- Recover the natural index without modular wrap. -/
theorem lookupIndex_nat (i : Nat) (bound : i < 2^31) :
    (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

end OCaml.Vm.Boot.Startup
