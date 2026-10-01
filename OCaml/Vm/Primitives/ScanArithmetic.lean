import OCaml.Vm.Primitives.StringRead

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A full-word scan lies inside ordinary RAM, including its header. -/
structure WordRange (a n : Nat) : Prop where
  lower : 0x80000000 + 8 ≤ a
  upper : a + 8 * n ≤ 0x100000000
  htif : a + 8 * n ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ a - 8

def scanPtr (a i : Nat) : BitVec 64 := BitVec.ofNat 64 (a + 8 * i)

theorem StringGeometry.wordRange {a length} (h : StringGeometry a length) :
    WordRange a ((length + 8) / 8) := ⟨h.lower, h.upper, h.htif⟩

theorem WordRange.ptr_nat {a n i} (h : WordRange a n) (hi : i ≤ n) :
    (scanPtr a i).toNat = a + 8 * i := by
  have upper := h.upper
  simp only [scanPtr, BitVec.toNat_ofNat]
  omega

theorem WordRange.window {a n i} (h : WordRange a n) (hi : i < n) :
    ReadWindow (scanPtr a i) 8 := by
  have hl := h.lower
  have hu := h.upper
  have ht := h.htif
  constructor <;> rw [h.ptr_nat (Nat.le_of_lt hi)] <;> omega

theorem scanPtr_succ (a i : Nat) : scanPtr a i + 8#64 = scanPtr a (i + 1) := by
  simp [scanPtr, Nat.mul_add, BitVec.add_assoc, BitVec.ofNat_add]

theorem scanPtr_delta (a b i : Nat) :
    scanPtr a i + (BitVec.ofNat 64 b - BitVec.ofNat 64 a) = scanPtr b i := by
  simp only [scanPtr, BitVec.ofNat_add, BitVec.sub_eq_add_neg]
  rw [BitVec.add_comm (BitVec.ofNat 64 a), BitVec.add_assoc,
    ← BitVec.add_assoc (BitVec.ofNat 64 a), BitVec.add_comm (BitVec.ofNat 64 a),
    BitVec.add_assoc, BitVec.add_right_neg, BitVec.add_zero, BitVec.add_comm]

theorem WordRange.ptr_eq_limit {a n i} (h : WordRange a n) (hi : i ≤ n) :
    scanPtr a i = scanPtr a n ↔ i = n := by
  constructor
  · intro he
    have hn := congrArg BitVec.toNat he
    rw [h.ptr_nat hi, h.ptr_nat (Nat.le_refl n)] at hn
    omega
  · intro he; rw [he]

/-- Shifting a decoded header gives the represented payload-word count. -/
theorem header_words (header : BitVec 64) (n : Nat)
    (size : header.toNat / 1024 = n) :
    header >>> (10 : Nat) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have bound := header.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

/-- The scan's setup computes the exclusive payload end. -/
theorem WordRange.limit {a n} (h : WordRange a n) :
    (BitVec.ofNat 64 n <<< (3 : Nat)) + BitVec.ofNat 64 a = scanPtr a n := by
  apply BitVec.eq_of_toNat_eq
  have bound := h.upper
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, scanPtr]
  omega

/-- Word counts in a RAM range fit in one machine register. -/
theorem WordRange.count_nat {a n} (h : WordRange a n) :
    (BitVec.ofNat 64 n).toNat = n := by
  have bound := h.upper
  simp only [BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Primitives
