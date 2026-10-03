import OCaml.Vm.Sim.ApplyArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- RESTART's field counter advances by one without signed 32-bit wrap. -/
theorem forward_counter_step (n : Nat) (small : n + 1 < 2^31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (BitVec.ofNat 64 n + sign_extend (m := 64) (0x001#12)) 31 0) = BitVec.ofNat 64 (n + 1) := by
  rw [show sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 1 from by decide, ← BitVec.ofNat_add]
  change ((BitVec.ofNat 64 (n + 1)).extractLsb' 0 32).signExtend 64 = _
  rw [low32_nat _ (by omega)]
  exact sign_extend_nat32 _ small

/-- An indexed base plus a biased field counter selects its copy window. -/
theorem indexed_copy_address (a bias i : Nat) :
    Sail.shift_bits_left (BitVec.ofNat 64 (bias + i)) (Sail.BitVec.extractLsb (0x03#6) 5 0) + BitVec.ofNat 64 a =
      BitVec.ofNat 64 (a + 8 * bias + 8 * i) := by
  change (BitVec.ofNat 64 (bias + i) <<< (3 : Nat)) + BitVec.ofNat 64 a = _
  rw [nat_shift_word, ← BitVec.ofNat_add]
  congr 1
  omega

/-- RESTART skips the closure code, arity metadata and environment. -/
theorem forward_source_address (a i : Nat) :
    Sail.shift_bits_left (BitVec.ofNat 64 (3 + i)) (Sail.BitVec.extractLsb (0x03#6) 5 0) + BitVec.ofNat 64 a =
      BitVec.ofNat 64 (a + 24 + 8 * i) := indexed_copy_address a 3 i

theorem forward_cursor_step (base i : Nat) :
    BitVec.ofNat 64 (base + 8 * i) + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (base + 8 * (i + 1)) := by
  rw [show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 8 from by decide, ← BitVec.ofNat_add]
  congr 1

/-- The post-increment store still writes the old destination cursor. -/
theorem forward_store_address (base i : Nat) :
    (BitVec.ofNat 64 (base + 8 * i) + sign_extend (m := 64) (0x008#12)) + sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 (base + 8 * i) := by
  rw [show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) (0xff8#12) = -(8#64) from by decide,
    ← BitVec.sub_eq_add_neg, BitVec.add_sub_cancel]

/-- The continuing branch compares distinct, non-wrapping field indices. -/
theorem indexed_copy_guard (bias count i : Nat) (more : i + 1 < count) (small : count + bias < 2^31) :
    (BitVec.ofNat 64 (count + bias) != BitVec.ofNat 64 (bias + i + 1)) = true := by
  rw [bne_iff_ne]
  intro equal
  have nat := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show count + bias < 2^64 by omega),
    Nat.mod_eq_of_lt (show bias + i + 1 < 2^64 by omega)] at nat
  omega

/-- RESTART's three metadata words specialize the common non-wrapping guard. -/
theorem forward_copy_guard (count i : Nat) (more : i + 1 < count) (small : count + 3 < 2^31) :
    (BitVec.ofNat 64 (count + 3) != BitVec.ofNat 64 (3 + i + 1)) = true :=
  indexed_copy_guard 3 count i more small

end OCaml.Vm.Sim
