import OCaml.Vm.Gc.FieldCopyAccess
import OCaml.Vm.Primitives.ScanArithmetic

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives OCaml.Bytecode

/-- Source/destination payloads lie in RAM and are disjoint. Fresh allocation
supplies the destination alignment and its position above HTIF. -/
structure Geometry (source target count : Nat) : Prop where
  sourceRange : WordRange source count
  targetRange : WordRange target count
  aligned : target % 8 = 0
  writable : Layout.sym_tohost + 16 ≤ target
  separate : source + 8 * count ≤ target ∨ target + 8 * count ≤ source

theorem header_nat {a n} (range : WordRange a n) :
    (BitVec.ofNat 64 a - 8#64).toNat = a - 8 := by
  have lower := range.lower
  have upper := range.upper
  change ((18446744073709551616 - 8 + a % 18446744073709551616) % 18446744073709551616) = a - 8
  omega

theorem header_window {a n} (range : WordRange a n) :
    ReadWindow (BitVec.ofNat 64 a - 8#64) 8 := by
  have lower := range.lower
  have upper := range.upper
  have htif := range.htif
  constructor <;> rw [header_nat range] <;> omega

theorem Geometry.write_window {a b n i} (geometry : Geometry a b n) (bound : i < n) :
    WriteWindow (scanPtr b i) 8 := by
  have lower := geometry.targetRange.lower
  have upper := geometry.targetRange.upper
  have htif := geometry.writable
  have aligned := geometry.aligned
  constructor <;> rw [geometry.targetRange.ptr_nat (Nat.le_of_lt bound)] <;> omega

theorem Geometry.windows {a b n i} (geometry : Geometry a b n) (bound : i < n) :
    Windows (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a) (BitVec.ofNat 64 b) := by
  refine ⟨geometry.sourceRange.window bound, ?_, header_window geometry.targetRange⟩
  rw [BitVec.add_comm, scanPtr_delta]
  exact geometry.write_window bound

def scanWindow (b start count : Nat) : List W := [⟨b + 8 * start, b + 8 * count⟩]

/-- A framed byte range preserves each disjoint scalar word observation. -/
theorem word_frame {before after : Config} {b start count a : Nat}
    (frame : FrameOn (scanWindow b start count) before.σ.mem after.σ.mem)
    (outside : a + 8 ≤ b + 8 * start ∨ b + 8 * count ≤ a) :
    word after a = word before a := by
  apply Reloc.bytesT_congr
  intro j hj
  change byte after (a + j) = byte before (a + j)
  rw [byte_total, byte_total, frame (a + j) ⟨by change a + j < b + 8 * start ∨ b + 8 * count ≤ a + j; omega, True.intro⟩]

/-- One represented integer selects the immediate classifier. -/
theorem immediate_tag (value : BitVec 63) :
    guardB .BNE (tag64 value &&& 1#64) 0 = true := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  simp [tag64, guardB]

/-- Header readback and finite word counts turn the actual back-edge guard
into the ordinary strict bound on the next index. -/
theorem again_eq {a b n i c} (geometry : Geometry a b n) (bound : i < n)
    (header : (word c (b - 8)).toNat / 1024 = n) :
    again (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 i) c = decide (i + 1 < n) := by
  have outside : OutLRange (copyLog (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a) c)
      (BitVec.ofNat 64 b - 8#64).toNat 8 := by
    rw [copyLog, BitVec.add_comm, scanPtr_delta, geometry.targetRange.ptr_nat (Nat.le_of_lt bound),
      header_nat geometry.targetRange]
    exact ⟨Or.inl (by have := geometry.targetRange.lower; omega), True.intro⟩
  rw [again, header_unchanged _ _ _ _ outside, header_nat geometry.targetRange, header_words _ n header]
  have upper := geometry.targetRange.upper
  simp [guardB, LeanRV64DExecutable.Functions.zopz0zI_u, Sail.BitVec.toNatInt,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Gc.FieldCopy
