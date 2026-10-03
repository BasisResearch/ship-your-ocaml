import OCaml.Vm.Sim.ApplyArithmetic
import OCaml.Vm.Sim.ReturnArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- The loop counter is one below the number of unread words, including -1 at exit. -/
def backwardCounter (remaining : Nat) : BitVec 64 := BitVec.ofNat 64 remaining - 1#64

/-- Source and destination cursors have a natural address even on the final exit. -/
def backwardCursor (base remaining : Nat) : Nat := base - 8 + 8 * remaining

theorem backward_counter_succ (n : Nat) : backwardCounter (n + 1) = BitVec.ofNat 64 n := by
  simp only [backwardCounter, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem backward_cursor_succ (base n : Nat) (room : 8 ≤ base) :
    backwardCursor base (n + 1) = base + 8 * n := by unfold backwardCursor; omega

theorem backward_cursor_step (base n : Nat) (room : 8 ≤ base) :
    BitVec.ofNat 64 (backwardCursor base (n + 1)) + sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 (backwardCursor base n) := by
  rw [backward_cursor_succ base n room]
  have subtract := BitVec.ofNat_sub_ofNat_of_le (base + 8 * n) 8 (by decide : 8 < 2^64) (by omega)
  rw [show sign_extend (m := 64) (0xff8#12) = -(8#64) from by decide, ← BitVec.sub_eq_add_neg, subtract]
  congr 1
  unfold backwardCursor
  omega

/-- ADDIW's decrement does not wrap while the original argument count fits 31 bits. -/
theorem backward_counter_step (n : Nat) (small : n < 2^31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (backwardCounter (n + 1) + sign_extend (m := 64) (0xfff#12)) 31 0) = backwardCounter n := by
  rw [backward_counter_succ]
  cases n with
  | zero => decide
  | succ n =>
    rw [extra_decrement (n + 1) (by omega)]
    simp only [Nat.add_sub_cancel, backward_counter_succ]
    change ((BitVec.ofNat 64 n).extractLsb' 0 32).signExtend 64 = _
    rw [low32_nat n (by omega)]
    exact sign_extend_nat32 n (by omega)

/-- A live reverse-copy counter differs from the -1 exit sentinel. -/
theorem backward_counter_live (n : Nat) (positive : 0 < n) (small : n < 2^64) :
    (backwardCounter n != -(1#64)) = true := by
  rw [bne_iff_ne]
  intro equal
  have e := congrArg (fun x : BitVec 64 => x + 1#64) equal
  simp only [backwardCounter, BitVec.sub_add_cancel] at e
  have nat := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at nat
  change n = 0 at nat
  omega

end OCaml.Vm.Sim
