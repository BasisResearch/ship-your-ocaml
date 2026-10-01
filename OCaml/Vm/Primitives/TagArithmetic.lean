import OCaml.Logic.Symbolic
import Vsa.Sim.BlockMem
namespace OCaml.Vm.Primitives
open OCaml.Bytecode

theorem tag_toNat (n : BitVec 63) : (tag64 n).toNat = 2 * n.toNat + 1 := by
  have hb := n.isLt
  have e : ∀ y : BitVec 64, y <<< (1 : Nat) ||| 1 = y <<< (1 : Nat) + 1 := by
    intro y
    have h := @BitVec.shiftLeft_add_eq_shiftLeft_or 64 1#64 y
    rw [BitVec.shiftLeft_eq'] at h
    exact h.symm
  unfold tag64
  rw [e]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  rw [show (1 : BitVec 64).toNat = 1 from rfl]
  split <;> omega

theorem tag_toInt (n : BitVec 63) : (tag64 n).toInt = 2 * n.toInt + 1 := by
  rw [BitVec.toInt_eq_toNat_cond, tag_toNat]
  simp only [BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

theorem tag_signed_lt (a b : BitVec 63) :
    (tag64 a).toInt < (tag64 b).toInt ↔ a.toInt < b.toInt := by
  rw [tag_toInt, tag_toInt]
  omega
open LeanRV64DExecutable LeanRV64DExecutable.Functions

def signedBit (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))

def compareWord (x y : BitVec 64) : BitVec 64 :=
  ((signedBit y x - signedBit x y) <<< (1 : Nat)) + 1

theorem signedBit_eq (x y : BitVec 64) :
    signedBit x y = if x.toInt < y.toInt then 1 else 0 := by
  by_cases h : x.toInt < y.toInt <;>
    simp [signedBit, zero_extend, bool_to_bit, zopz0zI_s, bool_bit_forwards,
      Sail.BitVec.zeroExtend, h]

def compareResult (a b : BitVec 63) : BitVec 63 :=
  BitVec.ofInt 63 (if a.toInt < b.toInt then -1 else if a.toInt > b.toInt then 1 else 0)

theorem compareWord_tag (a b : BitVec 63) :
    compareWord (tag64 a) (tag64 b) = tag64 (compareResult a b) := by
  by_cases hab : a.toInt < b.toInt
  · have hba : ¬ b.toInt < a.toInt := by omega
    simp only [compareWord, signedBit_eq, tag_signed_lt, compareResult, hab, hba, ite_true, ite_false]
    decide
  · by_cases hba : b.toInt < a.toInt
    · simp only [compareWord, signedBit_eq, tag_signed_lt, compareResult, hab, hba, ite_true, ite_false]
      decide
    · simp only [compareWord, signedBit_eq, tag_signed_lt, compareResult, hab, hba, ite_true, ite_false]
      decide

end OCaml.Vm.Primitives
