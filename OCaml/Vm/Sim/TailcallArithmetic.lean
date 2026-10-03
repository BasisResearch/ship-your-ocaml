import OCaml.Vm.Sim.TailcallRestore
import OCaml.Vm.Sim.IndexWord

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- The native scaled slot count minus argument bytes is the natural move offset. -/
theorem tailcall_offset {slots arity : Nat} (fits : arity ≤ slots) (small : 8 * arity < 2^64) :
    BitVec.ofNat 64 (8 * slots) - BitVec.ofNat 64 (8 * arity) =
      BitVec.ofNat 64 (8 * (slots - arity)) := by
  rw [BitVec.ofNat_sub_ofNat_of_le (8 * slots) (8 * arity) small (by omega)]
  congr 1
  omega

/-- Pointer arithmetic agrees with moving arguments above the discarded slots. -/
theorem tailcall_address {sp slots arity : Nat} {offset : BitVec 12}
    (fits : arity ≤ slots) (small : 8 * arity < 2^64)
    (encoded : sign_extend (m := 64) offset = -BitVec.ofNat 64 (8 * arity)) :
    BitVec.ofNat 64 sp + (BitVec.ofNat 64 (8 * slots) + sign_extend (m := 64) offset) =
      BitVec.ofNat 64 (tailcallStart sp arity slots) := by
  rw [encoded, ← BitVec.sub_eq_add_neg, tailcall_offset fits small, ← BitVec.ofNat_add]
  rfl

/-- Natural extra-argument accounting commutes with the native modular addition. -/
theorem tailcall_extra (extra arity : Nat) (positive : 1 ≤ arity) :
    BitVec.ofNat 64 extra + BitVec.ofNat 64 (arity - 1) =
      BitVec.ofNat 64 (extra + arity - 1) := by
  rw [← BitVec.ofNat_add]
  congr 1
  omega

end OCaml.Vm.Sim
