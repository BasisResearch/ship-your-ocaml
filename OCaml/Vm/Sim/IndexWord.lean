import OCaml.Vm.Sim.AtomBinding

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode
open LeanRV64DExecutable.Functions

/-- A nonnegative bytecode index has the same scaled word in the native arm.
The premise is explicit: Int.toNat would otherwise silently clamp negatives. -/
theorem index_word (w : BitVec 32) (nonnegative : 0 ≤ w.toInt) :
    Sail.shift_bits_left (sign_extend (m := 64) w) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (8 * w.toInt.toNat) := by
  change (BitVec.ofInt 64 w.toInt <<< (3 : Nat)) = _
  have cast := congrArg (BitVec.ofInt 64) (Int.toNat_of_nonneg nonnegative)
  change BitVec.ofNat 64 w.toInt.toNat = BitVec.ofInt 64 w.toInt at cast
  rw [← cast, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 w.toInt.toNat * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

/-- Atom value pointers are one word beyond their indexed headers. -/
theorem atom_index_offset (w : BitVec 32) (nonnegative : 0 ≤ w.toInt) :
    Sail.shift_bits_left (sign_extend (m := 64) w) (Sail.BitVec.extractLsb (0x03#6) 5 0) + 8#64 =
      BitVec.ofNat 64 (8 * w.toInt.toNat + 8) := by
  rw [index_word w nonnegative, BitVec.ofNat_add]

/-- Negative bytecode indices expose another semantic-domain mismatch:
ATOM(-1)'s native offset is zero, while Int.toNat makes the model choose atom 0.
This retained word-level witness does not claim a complete machine run. -/
theorem atom_negative_index_obstruction :
    Sail.shift_bits_left (sign_extend (m := 64) (0xffffffff#32))
      (Sail.BitVec.extractLsb (0x03#6) 5 0) + 8#64 ≠
        BitVec.ofNat 64 (8 * ((-1 : Int).toNat) + 8) := by
  decide +kernel

end OCaml.Vm.Sim
