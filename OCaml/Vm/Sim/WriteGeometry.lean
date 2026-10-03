import OCaml.Vm.Primitives.Write
import OCaml.Vm.Sim.ReadGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Sim OCaml.Vm.Primitives

/-- Natural-address geometry used by generated full-word store parameters. -/
structure RamWriteAt (address width : Nat) : Prop where
  lower : 0x80000000 ≤ address
  upper : address + width ≤ 0x100000000
  htif : tohostAddr + 16 ≤ address
  aligned : address % width = 0

/-- Writable RAM is also readable without observing an HTIF device. -/
theorem RamWriteAt.read {address width : Nat} (h : RamWriteAt address width) : RamReadAt address width := by
  refine ⟨h.lower, h.upper, Or.inr ?_⟩
  have separated := h.htif
  have lower : tohostAddr + 8 ≤ address := by omega
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using lower

/-- Normalize a represented store window once, including the pinned HTIF alias. -/
theorem writeWindow_nat {address width : Nat}
    (window : WriteWindow (BitVec.ofNat 64 address) width)
    (addressNat : (BitVec.ofNat 64 address).toNat = address) :
    RamWriteAt address width := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [addressNat] using window.lower
  · simpa only [addressNat] using window.upper
  · simpa only [addressNat, tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using window.htif
  · simpa only [addressNat] using window.aligned

end OCaml.Vm.Sim
