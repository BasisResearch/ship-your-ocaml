import OCaml.Vm.Boot.Startup.LibraryLive
import OCaml.Vm.Boot.Startup.AllocatorPins
import OCaml.Vm.Primitives.Memmove

/-! newlib's library model over the program image alone (`imageLive`: `.text`,
`.rodata`, the `_impure_ptr` word). Its presence follows from
`ExecutableImage` (`imageLive_present`), so a caller needs no dense RAM. -/
namespace OCaml.Vm.Gc
open OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris.VsaHeap

theorem imageLive_alloc : AllocLive imageLive := by
  intro p hp
  have s := allocator_sources p hp
  unfold AllocatorByteSource at s
  split at s
  · exact .inl ⟨s.1, ‹_›⟩
  · obtain ⟨lo, hi, -⟩ := s
    exact .inr (.inr ⟨by simpa [allocatorImpureAddr, Layout.sym_impure_ptr] using lo,
      by simpa [allocatorImpureAddr, Layout.sym_impure_ptr] using hi⟩)

instance : LibraryLive imageLive := ⟨imageLive_alloc, imageLive_image⟩

end OCaml.Vm.Gc
