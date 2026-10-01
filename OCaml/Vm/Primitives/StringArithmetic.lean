import OCaml.Vm.Primitives.TagArithmetic

namespace OCaml.Vm.Primitives
open OCaml.Bytecode

/-- Offset of the final padding-count byte from the string value pointer. -/
def stringLast (header : BitVec 64) : BitVec 64 :=
  ((header >>> (10 : Nat)) <<< (3 : Nat)) - 1

/-- The length routine's tagged result from its header and padding byte. -/
def stringLengthWord (header : BitVec 64) (padding : BitVec 8) : BitVec 64 :=
  ((stringLast header - padding.setWidth 64) <<< (1 : Nat)) + 1

theorem stringLast_toNat (header : BitVec 64) (n : Nat)
    (hs : header.toNat / 1024 = (n + 8) / 8) :
    (stringLast header).toNat = 8 * ((n + 8) / 8) - 1 := by
  have hh := header.isLt
  simp only [stringLast, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem stringLengthWord_tag (header : BitVec 64) (padding : BitVec 8) (n : Nat)
    (hs : header.toNat / 1024 = (n + 8) / 8)
    (hp : padding.toNat = 8 * ((n + 8) / 8) - 1 - n) :
    stringLengthWord header padding = tag64 (BitVec.ofNat 63 n) := by
  have hh := header.isLt
  have hb := padding.isLt
  apply BitVec.eq_of_toNat_eq
  rw [tag_toNat]
  simp only [stringLengthWord, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_sub, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, stringLast_toNat header n hs]
  rw [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

end OCaml.Vm.Primitives
