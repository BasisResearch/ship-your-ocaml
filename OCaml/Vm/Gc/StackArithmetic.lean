import OCaml.Vm.Primitives.Write

namespace OCaml.Vm.Gc
open Vsa.Sim Primitives

/-- A small stack-relative displacement cannot wrap into RAM: a wrapped
address would be below the RAM base. Keep the pointer abstract while proving
this arithmetic fact so native-frame expressions never enter normalization. -/
theorem stack_bound (sp : BitVec 64) (off : Nat) (small : off < 0x80000000)
    (window : WriteWindow (sp + BitVec.ofNat 64 off) 8) :
    sp.toNat + off + 8 ≤ 0x100000000 := by
  have lower := window.lower
  have upper := window.upper
  have limit := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at lower upper
  omega

theorem stack_address (sp : BitVec 64) (off extent : Nat)
    (bound : sp.toNat + extent + 8 ≤ 0x100000000) (small : off ≤ extent) :
    (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Gc
