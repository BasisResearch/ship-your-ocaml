import OCaml.Vm.Sim.SwitchArithmetic
import OCaml.Vm.Sim.TrapPayload

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives
open LeanRV64DExecutable.Functions

/-- An in-range trap link fits in a positive signed tagged integer because
the represented stack occupies fewer than 2^64 bytes. -/
theorem trap_link_nonnegative {c : Config} {pl : Place} {sp high : Nat}
    {stack : List Val} {link : BitVec 63}
    (words : StackRepr c pl sp high stack) (highNat : high < 2^64)
    (bound : link.toNat ≤ stack.length) : 0 ≤ link.toInt := by
  have shape := words.1
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- POPTRAP's tagged relative link restores the previous absolute trap pointer. -/
theorem poptrap_link {c : Config} {pl : Place} {sp high : Nat}
    {stack : List Val} {link : BitVec 63}
    (words : StackRepr c pl sp high stack) (highNat : high < 2^64)
    (bound : link.toNat ≤ stack.length) :
    BitVec.ofNat 64 sp + Sail.shift_bits_left
      (shift_bits_right_arith (tag64 link) (Sail.BitVec.extractLsb (0x01#6) 5 0))
      (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (high - 8 * (stack.length - link.toNat)) := by
  rw [longVal_native, longVal_nonnegative link (trap_link_nonnegative words highNat bound)]
  change BitVec.ofNat 64 sp + (BitVec.ofNat 64 link.toNat <<< (3 : Nat)) = _
  rw [nat_shift_word, ← BitVec.ofNat_add]
  congr 1
  have shape := words.1
  omega

end OCaml.Vm.Sim
