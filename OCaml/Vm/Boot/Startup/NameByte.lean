import OCaml.Vm.Primitives.Control
import OCaml.Vm.Primitives.Read
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def nameByteWord (b : BitVec 8) : BitVec 64 := b.setWidth 64

def nameSignedByte (b : BitVec 8) : BitVec 64 :=
  Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (nameByteWord b + Functions.sign_extend (m := 64) 0#12) 31 0)

/-- The compiled sext.w cannot change a zero-extended byte. -/
theorem nameSignedByte_eq (b : BitVec 8) : nameSignedByte b = nameByteWord b := by
  have cut : Sail.BitVec.extractLsb (nameByteWord b + Functions.sign_extend (m := 64) 0#12) 31 0 = b.setWidth 32 := by
    change ((b.setWidth 64 + 0#64).extractLsb 31 0) = b.setWidth 32
    rw [BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
    have bound := b.isLt
    omega
  unfold nameSignedByte
  rw [cut]
  change (b.setWidth 32).signExtend 64 = b.setWidth 64
  have msb : (b.setWidth 32).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, decide_eq_false_iff_not]
    have bound := b.isLt
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have bound := b.isLt
  omega

theorem nameByteWord_zero (b : BitVec 8) : nameByteWord b = 0#64 ↔ b = 0#8 := by
  simp only [← BitVec.toNat_inj, nameByteWord, BitVec.toNat_setWidth, BitVec.toNat_zero]
  have bound := b.isLt
  omega

theorem nameByte_equals (b : BitVec 8) : nameSignedByte b + (-61#64) = 0#64 ↔ b = 61#8 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.sub_eq_iff_eq_add, BitVec.zero_add, nameSignedByte_eq]
  simp only [← BitVec.toNat_inj, nameByteWord, BitVec.toNat_setWidth]
  change b.toNat % 18446744073709551616 = 61 ↔ b.toNat = 61
  have bound := b.isLt
  omega
theorem name_lbu_value (b : BitVec 8) : bytesVal .lbu [b] = nameByteWord b := by
  change b.zeroExtend 64 = b.setWidth 64
  exact BitVec.zeroExtend_eq_setWidth

theorem nameByte_zero_guard {b : BitVec 8} {finished : Bool} (zero : b = 0#8 ↔ finished = true) :
    guardB bop.BEQ (nameByteWord b) 0#64 = finished := by
  apply Bool.eq_iff_iff.mpr
  simpa only [guardB, beq_iff_eq, nameByteWord_zero] using zero

theorem nameByte_equals_guard {b : BitVec 8} (neq : b ≠ 61#8) :
    guardB bop.BNE (nameSignedByte b + (-61#64)) 0#64 = true := by
  rw [guardB, bne_iff_ne]
  exact fun eq => neq ((nameByte_equals b).mp eq)
theorem nameByteWord_ne_of {b : BitVec 8} {v : Nat} (ne : b ≠ BitVec.ofNat 8 v) (small : v < 256) :
    nameByteWord b ≠ BitVec.ofNat 64 v := by
  intro h
  apply ne
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [nameByteWord, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this ⊢
  have := b.isLt
  omega

end OCaml.Vm.Boot.Startup
