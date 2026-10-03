import OCaml.Vm.Boot.Startup.AllocatorReads
import OCaml.Vm.Boot.Startup.AllocatorInitialBins
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

/-- Source allocator metadata before the first allocation. This deliberately
separates the initial dummy top and sentinel from the initialized HeapAt arena. -/
structure InitialArena (m : Mem) : Prop where
  sbrk_base : read64 m sbrkBaseAddr = some (2^64 - 1)
  brk : read64 m brkAddr = some 0
  top : read64 m topAddr = some avAddr
  binblocks : read64 m binblocksAddr = some 0
  bins : ∀ i, 0 < i → i < numBins → BinList m i []
  top_pad : read64 m topPadAddr = some 0
  max_sbrked : read64 m maxSbrkedAddr = some 0
  mallinfo : read64 m mallinfoAddr = some 0
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup

/-- All 127 allocator bins have their source self-links at the actual first call. -/
theorem ResetMallocWitness.empty_bins {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (i : Nat) (lo : 0 < i) (hi : i < numBins) : BinList atMalloc.σ.mem i [] := by
  obtain ⟨forward, backward⟩ := initial_bin_links i lo hi
  have bounds : Vsa.Densify.ramBase ≤ binAt i ∧ binAt i + 32 ≤ Layout.sym_environ ∧
      binAt i + 32 ≤ Layout.sym_bss_start ∧ binAt i < 2^64 := by
    unfold binAt avAddr numBins Vsa.Densify.ramBase Layout.sym_environ Layout.sym_bss_start at *
    omega
  have readForward := w.initial_read (binAt i + 16) (BitVec.ofNat 64 (binAt i))
    (by omega) (by omega) (Or.inl (by omega)) forward
  have readBackward := w.initial_read (binAt i + 24) (BitVec.ofNat 64 (binAt i))
    (by omega) (by omega) (Or.inl (by omega)) backward
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.2.2.2] at readForward readBackward
  exact ⟨binAt i, readForward, .close readBackward⟩

/-- A closed supplier of the first malloc's metadata, derived from loader bytes,
crt0's BSS loop, and the proved call-prefix frames. -/
theorem ResetMallocWitness.initial_arena {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) : InitialArena atMalloc.σ.mem where
  sbrk_base := w.initial_read sbrkBaseAddr _ (by decide) (by decide) (Or.inr (by decide)) initial_sbrk_base
  brk := w.bss_read brkAddr (by decide) (by decide)
  top := w.initial_read topAddr _ (by decide) (by decide) (Or.inl (by decide)) initial_top
  binblocks := w.initial_read binblocksAddr _ (by decide) (by decide) (Or.inl (by decide)) initial_binblocks
  bins := w.empty_bins
  top_pad := w.bss_read topPadAddr (by decide) (by decide)
  max_sbrked := w.bss_read maxSbrkedAddr (by decide) (by decide)
  mallinfo := w.bss_read mallinfoAddr (by decide) (by decide)
end OCaml.Vm.Boot.WhileMinElfParse
