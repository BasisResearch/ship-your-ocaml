import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives LeanRV64DExecutable.Functions

/-- Scaling by eight removes the sign-extension difference modulo 2^64.
Unlike unscaled byte indexing, this holds for every represented 63-bit index. -/
theorem value_index_word (n : BitVec 63) :
    Sail.shift_bits_left
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0))
      (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (8 * n.toNat) := by
  have h := congrArg BitVec.toNat (untag_tag n)
  change ((tag64 n).sshiftRight 1).toNat % 2^63 = n.toNat at h
  change ((tag64 n).sshiftRight 1 <<< (3 : Nat)) = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Sim
