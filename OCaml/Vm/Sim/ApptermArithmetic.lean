import OCaml.Vm.Sim.BackwardCopyArithmetic
import OCaml.Vm.Sim.TailcallArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- Signed 32-bit operand values, clamped to naturals, fit the positive counter domain. -/
theorem word32_nat_small (w : BitVec 32) : w.toInt.toNat < 2^31 := by
  have bound := BitVec.toInt_lt (x := w)
  omega

/-- The generic tail-call prefix computes its destination from the two slot counts. -/
theorem appterm_base_word (sp slots count : Nat) (fits : count ≤ slots) (small : count < 2^64) :
    BitVec.ofNat 64 sp + Sail.shift_bits_left (BitVec.ofNat 64 slots - BitVec.ofNat 64 count)
      (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (tailcallStart sp count slots) := by
  change BitVec.ofNat 64 sp + ((BitVec.ofNat 64 slots - BitVec.ofNat 64 count) <<< (3 : Nat)) = _
  rw [BitVec.ofNat_sub_ofNat_of_le slots count small fits, nat_shift_word, ← BitVec.ofNat_add]
  rfl

/-- Both cursors initially point to the highest argument word. -/
theorem appterm_cursor_word (base count : Nat) (room : 8 ≤ base) (positive : 0 < count) :
    BitVec.ofNat 64 base + Sail.shift_bits_left (BitVec.ofNat 64 (count - 1))
      (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (backwardCursor base count) := by
  change BitVec.ofNat 64 base + (BitVec.ofNat 64 (count - 1) <<< (3 : Nat)) = _
  rw [nat_shift_word, ← BitVec.ofNat_add]
  congr 1
  unfold backwardCursor
  omega

theorem appterm_counter_word (count : Nat) (positive : 0 < count) :
    BitVec.ofNat 64 (count - 1) = backwardCounter count := by
  unfold backwardCounter
  exact (BitVec.ofNat_sub_ofNat_of_le count 1 (by decide) (by omega)).symm

/-- A positive argument count takes the generic copy-loop entry branch. -/
theorem appterm_prefix_guard (count : Nat) (small : count < 2^31) :
    zopz0zI_s (BitVec.ofNat 64 (count - 1)) (0#64) = false := by
  unfold zopz0zI_s
  rw [nat64_toInt (count - 1) (by omega)]
  exact decide_eq_false (by change ¬ ((count - 1 : Nat) : Int) < 0; omega)

end OCaml.Vm.Sim
