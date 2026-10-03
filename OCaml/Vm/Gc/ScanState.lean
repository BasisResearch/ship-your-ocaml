import OCaml.Vm.Gc.ScanGeometry

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- Loop-head or exhausted-scan state. The footprint and expected field
words are parameters: a relocating scan can include native stack saves and
record forwarding targets, while the original copy scan uses source words. -/
structure ScanAtWith (writes : List Nat) (a b count start : Nat) (initial : Config) (i : Nat) (c : Config)
    (footprint : List W := scanWindow b start count)
    (expected : Nat → BitVec 64 := fun j => word initial (a + 8 * j)) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  lower : start ≤ i
  upper : i ≤ count
  pc : PCAt (if i < count then FieldCopy.pc else exitPc) c
  registers : GHolds c.σ (regs (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
    (BitVec.ofNat 64 b) (BitVec.ofNat 64 i))
  memory : FrameOn footprint initial.σ.mem c.σ.mem
  copied : ∀ j, start ≤ j → j < i → word c (b + 8 * j) = expected j
  output : c.σ.sailOutput = initial.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) →
      c.σ.regs.get? r = initial.σ.regs.get? r

/-- Original immediate-only interface retains its exact register frame. -/
abbrev ScanAt := ScanAtWith [8,9,10,11,15]

def scanIndex (c : Config) : Nat := ((gprGet c.σ 9).getD 0).toNat

theorem ScanAtWith.index_eq {writes a b count start initial i c footprint expected}
    (h : ScanAtWith writes a b count start initial i c footprint expected)
    (geometry : Geometry a b count) : scanIndex c = i := by
  have reg : gprGet c.σ 9 = some (BitVec.ofNat 64 i) := gholds_lookup _ h.registers rfl
  have upper := geometry.targetRange.upper
  have bound := h.upper
  simp only [scanIndex, reg, Option.getD_some, BitVec.toNat_ofNat]
  omega

theorem ScanAt.index_eq {a b count start initial i c} (h : ScanAt a b count start initial i c)
    (geometry : Geometry a b count) : scanIndex c = i := ScanAtWith.index_eq h geometry

end OCaml.Vm.Gc.FieldCopy
