import OCaml.Vm.Sim.ForwardCopyArithmetic
import OCaml.Vm.Sim.ReturnArithmetic
import OCaml.Vm.Primitives.ScanArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions OCaml.Vm.Primitives

/-- RESTART decodes the number of saved arguments without signed wrap. -/
theorem restart_count_word (n : Nat) (lower : 3 ≤ n) (small : n < 2^31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (BitVec.ofNat 64 n + sign_extend (m := 64) (0xffd#12)) 31 0) = BitVec.ofNat 64 (n - 3) := by
  rw [show sign_extend (m := 64) (0xffd#12) = -(BitVec.ofNat 64 3) from by decide,
    ← BitVec.sub_eq_add_neg, BitVec.ofNat_sub_ofNat_of_le n 3 (by decide) lower]
  change ((BitVec.ofNat 64 (n - 3)).extractLsb' 0 32).signExtend 64 = _
  rw [low32_nat _ (by omega)]
  exact sign_extend_nat32 _ (by omega)

/-- The stack reservation is exactly eight bytes per saved argument. -/
theorem restart_stack_word (sp count : Nat) (room : 8 * count ≤ sp) (small : count < 2^31) :
    BitVec.ofNat 64 sp - Sail.shift_bits_left (BitVec.ofNat 64 count)
      (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (sp - 8 * count) := by
  change BitVec.ofNat 64 sp - (BitVec.ofNat 64 count <<< (3 : Nat)) = _
  rw [nat_shift_word]
  exact BitVec.ofNat_sub_ofNat_of_le sp (8 * count) (by omega) room

/-- Signed nonpositive comparison selects precisely the empty saved-argument path. -/
theorem restart_empty_guard (count : Nat) (small : count < 2^31) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 count) = decide (count = 0) := by
  by_cases zero : count = 0
  · subst count; decide
  · rw [show decide (count = 0) = false from decide_eq_false zero]
    exact return_more_guard count (by omega) (by omega)

end OCaml.Vm.Sim
