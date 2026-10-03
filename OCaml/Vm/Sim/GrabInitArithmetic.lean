import OCaml.Vm.Sim.GrabAllocationArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- A bounded extra counter cannot equal the initializer's all-ones sentinel. -/
theorem grab_copy_nonempty (extra : Nat) (small : extra < 2^31) :
    (BitVec.ofNat 64 extra == ((0#64) + sign_extend (m := 64) (0xfff#12))) = false := by
  rw [beq_eq_false_iff_ne]
  intro equal
  have nat := congrArg BitVec.toNat equal
  change (BitVec.ofNat 64 extra).toNat = 2^64 - 1 at nat
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show extra < 2^64 by omega)] at nat
  omega

/-- GRAB's final source cursor accounts for the accumulator argument as well. -/
theorem grab_source_end (sp extra : Nat) :
    (Sail.shift_bits_left (BitVec.ofNat 64 extra) (Sail.BitVec.extractLsb (0x03#6) 5 0) +
      sign_extend (m := 64) (0x008#12)) + BitVec.ofNat 64 sp = BitVec.ofNat 64 (sp + 8 * (1 + extra)) := by
  change ((BitVec.ofNat 64 extra <<< (3 : Nat)) + BitVec.ofNat 64 8) + BitVec.ofNat 64 sp = _
  rw [nat_shift_word, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

end OCaml.Vm.Sim
