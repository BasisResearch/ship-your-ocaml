import OCaml.Vm.Sim.ClosurerecInfixLog
import OCaml.Vm.Sim.RetaddrStore
import OCaml.Vm.Sim.MakeblockArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A natural arity offset uses the ordinary tagged-integer encoding. -/
theorem tagged_nat_word (n : Nat) :
    BitVec.ofNat 64 (2 * n + 1) = tag64 (BitVec.ofNat 63 n) := by
  have tagged := retaddr_extra_word n
  rw [nat_shift_word] at tagged
  simpa only [BitVec.ofNat_add, show 2^1 = 2 from rfl] using tagged

/-- Live infix arities are nonnegative offsets to the common environment. -/
theorem infix_arity_word (functions index : Nat)
    (bound : index < functions) (small : 6 * functions < 2^64) :
    infixArityWord functions index = tag64 (BitVec.ofNat 63 (3 * functions - 1 - 3 * index)) := by
  unfold infixArityWord
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have arithmetic : 6 * functions - 1 - 6 * index = 2 * (3 * functions - 1 - 3 * index) + 1 := by omega
  rw [arithmetic, tagged_nat_word]

/-- Infix headers are raw metadata words, with no value-pointer interpretation. -/
theorem infix_header_word (index : Nat) :
    blockHeader (3 * index) infixTag = BitVec.ofNat 64 ((3 * index) * 1024 + infixTag) := by
  rw [← makeblock_header_word, Nat.mul_comm (3 * index) 1024, BitVec.ofNat_add, BitVec.add_comm]

end OCaml.Vm.Sim
