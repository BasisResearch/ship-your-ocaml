import OCaml.Vm.Primitives.TagArithmetic
import OCaml.Vm.Repr

namespace OCaml.Vm.Primitives
open OCaml.Bytecode

/-- The runtime object-ID counter is stored as a tagged machine integer. -/
def counterWord (n : Nat) : BitVec 64 := tag64 (BitVec.ofNat 63 n)

theorem counterWord_succ (n : Nat) : counterWord n + 2 = counterWord (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [counterWord, BitVec.toNat_add, tag_toNat, BitVec.toNat_ofNat]
  rw [show (2 : BitVec 64).toNat = 2 from rfl]
  omega

theorem counterWord_repr (pl : Place) (n : Nat) : valWord pl (Val.ofInt n) = some (counterWord n) := by
  simp [valWord, Val.ofInt, counterWord]

end OCaml.Vm.Primitives
