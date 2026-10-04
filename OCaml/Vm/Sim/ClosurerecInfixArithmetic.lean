import OCaml.Vm.Sim.ClosurerecInfixState
import OCaml.Vm.Sim.StackPush

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- Each infix cursor advances by one three-word metadata record. -/
theorem infix_target_step (a i : Nat) :
    BitVec.ofNat 64 (a + 24 * (i + 1)) + sign_extend (m := 64) (0x018#12) =
      BitVec.ofNat 64 (a + 24 * (i + 2)) := by
  rw [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 24 from by decide, ← BitVec.ofNat_add]
  congr 1

/-- The next pushed closure pointer is one word below the current stack cursor. -/
theorem infix_stack_step (stackStart i : Nat) (room : 8 * (i + 1) ≤ stackStart) :
    BitVec.ofNat 64 (stackStart - 8 * i) + sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 (stackStart - 8 * (i + 1)) := by
  rw [push_address (show 8 ≤ stackStart - 8 * i by omega)]
  congr 1

/-- Tagged environment offsets decrease by six, including the unused final -1 word. -/
theorem infix_arity_step (functions i : Nat) :
    infixArityWord functions (i + 1) + sign_extend (m := 64) (0xffa#12) =
      infixArityWord functions (i + 2) := by
  have next : BitVec.ofNat 64 (6 * (i + 2)) = BitVec.ofNat 64 (6 * (i + 1)) + 6#64 := by
    rw [← BitVec.ofNat_add]
    congr 1
  rw [infixArityWord, infixArityWord, show sign_extend (m := 64) (0xffa#12) = -(6#64) from by decide,
    ← BitVec.sub_eq_add_neg, next, BitVec.sub_sub]

/-- Distinct bounded triple counters take the continuing native branch. -/
theorem infix_more_guard (count i : Nat) (more : i + 1 < count) (small : 3 * (count + 1) < 2^31) :
    (BitVec.ofNat 64 (3 * (count + 1)) != BitVec.ofNat 64 (3 * (i + 2))) = true := by
  rw [bne_iff_ne]
  intro same
  have nat := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 3 * (count + 1) < 2^64 by omega),
    Nat.mod_eq_of_lt (show 3 * (i + 2) < 2^64 by omega)] at nat
  omega

end OCaml.Vm.Sim
