import OCaml.Vm.Sim.SignedDivisionState
import OCaml.Vm.Sim.MulArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

/-- Native unboxing is sign extension of the represented 63-bit integer. -/
theorem unbox_signExtend (x : BitVec 63) : (tag64 x).sshiftRight 1 = x.signExtend 64 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, tag_toInt, BitVec.toInt_signExtend_of_le (by decide), Int.shiftRight_eq_div_pow]
  omega

/-- The unsigned magnitude is unchanged when widening a signed VM integer. -/
theorem division_magnitude_widen (x : BitVec 63) :
    (divisionMagnitude (x.signExtend 64)).toNat = (divisionMagnitude x).toNat := by
  have small := x.isLt
  have wideSign : (x.signExtend 64).msb = x.msb := by simp [BitVec.msb_signExtend]
  cases sign : x.msb
  · simp only [divisionMagnitude, wideSign, sign, Bool.false_eq_true, ite_false,
      BitVec.toNat_signExtend, BitVec.toNat_setWidth, Nat.add_zero]
    omega
  · have lower := BitVec.toNat_ge_of_msb_true sign
    simp only [divisionMagnitude, wideSign, sign, ite_true, BitVec.toNat_neg,
      BitVec.toNat_signExtend, BitVec.toNat_setWidth]
    omega

/-- Truncation commutes with the signed wrapper's modular negation. -/
theorem division_truncate_neg (x : BitVec 64) : (-x).truncate 63 = -(x.truncate 63) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_neg]
  omega

/-- Widened magnitudes compute the same unsigned quotient or remainder. -/
theorem division_unsigned_widen (kind : DivisionKind) (x y : BitVec 63) :
    (divisionUnsigned kind (x.signExtend 64) (y.signExtend 64)).truncate 63 =
      divisionUnsigned kind x y := by
  have bound := (divisionMagnitude x).isLt
  cases kind
  · apply BitVec.eq_of_toNat_eq
    simp only [divisionUnsigned, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_udiv, division_magnitude_widen]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) bound)
  · apply BitVec.eq_of_toNat_eq
    simp only [divisionUnsigned, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_umod, division_magnitude_widen]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) bound)

/-- Truncation preserves both signed results, including overflow of the 63-bit minimum divided by negative one. -/
theorem division_result_widen (kind : DivisionKind) (x y : BitVec 63) :
    (divisionResult kind (x.signExtend 64) (y.signExtend 64)).truncate 63 = divisionResult kind x y := by
  have signs : divisionNegative kind (x.signExtend 64) (y.signExtend 64) = divisionNegative kind x y := by
    cases kind <;> simp [divisionNegative, BitVec.msb_signExtend]
  rw [division_result_sign kind (x.signExtend 64) (y.signExtend 64), division_result_sign kind x y, signs]
  cases sign : divisionNegative kind x y
  · exact division_unsigned_widen kind x y
  · simp only [ite_true]
    rw [division_truncate_neg, division_unsigned_widen]

/-- The caller's actual unbox/divide/retag sequence equals the bytecode operation. -/
theorem tag_division_native (kind : DivisionKind) (x y : BitVec 63) :
    ((divisionResult kind ((tag64 x).sshiftRight 1) ((tag64 y).sshiftRight 1)) <<< 1) + 1#64 =
      tag64 (divisionResult kind x y) := by
  rw [unbox_signExtend, unbox_signExtend, ← tag_truncate, division_result_widen]

/-- A nonzero VM divisor takes the native nonzero branch. -/
theorem division_unbox_nonzero {x : BitVec 63} (nonzero : x ≠ 0) : (tag64 x).sshiftRight 1 ≠ 0 := by
  intro zero
  have truncated := congrArg (fun w : BitVec 64 => w.truncate 63) zero
  change untag (tag64 x) = 0 at truncated
  rw [untag_tag] at truncated
  exact nonzero truncated

end OCaml.Vm.Sim
