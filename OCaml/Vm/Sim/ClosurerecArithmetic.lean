import OCaml.Vm.Sim.ApplyArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- CLOSUREREC forms three metadata words per function with SLLIW and ADDW. -/
theorem closurerec_twice (n : Nat) (small : 2 * n < 2^31) :
    sign_extend (m := 64) (Sail.shift_bits_left (Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0) (0x01#5)) =
      BitVec.ofNat 64 (2 * n) := by
  change ((BitVec.ofNat 64 n).extractLsb' 0 32 <<< (1 : Nat)).signExtend 64 = _
  rw [low32_nat _ (by omega), BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 32 1 = BitVec.ofNat 32 (2^1) from by decide, ← BitVec.ofNat_mul]
  have equal : n * 2^1 = 2 * n := by omega
  rw [equal]
  exact sign_extend_nat32 _ small

end OCaml.Vm.Sim
