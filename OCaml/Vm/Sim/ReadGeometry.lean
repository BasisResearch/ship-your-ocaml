import OCaml.Vm.Primitives.Read

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Vm.Primitives

/-- A natural-address load lies in architectural RAM and outside HTIF.
Allocator/code placement supplies these facts; reads remain total. -/
structure RamReadAt (a width : Nat) : Prop where
  lower : 0x80000000 ≤ a
  upper : a + width ≤ 0x100000000
  htif : a + width ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ a

/-- RAM placement excludes wraparound independently of the load width. -/
theorem RamReadAt.toNat {a width : Nat} (h : RamReadAt a width) :
    (BitVec.ofNat 64 a).toNat = a := by
  apply Nat.mod_eq_of_lt
  have upper := h.upper
  omega

/-- Feed natural-address geometry into the primitive lane's total-read API. -/
theorem RamReadAt.window {a width : Nat} (h : RamReadAt a width) :
    ReadWindow (BitVec.ofNat 64 a) width := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [h.toNat] using h.lower
  · simpa only [h.toNat] using h.upper
  · simpa only [h.toNat] using h.htif

end OCaml.Vm.Sim
