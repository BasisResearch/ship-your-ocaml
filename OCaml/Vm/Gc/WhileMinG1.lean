import OCaml.Vm.Boot.WhileMin
import OCaml.Vm.Gc.WhileMinRoom
import OCaml.Programs.WhileMinChecks
import OCaml.Vm.Gc.FreePlacement
import OCaml.Vm.Gc.LargePlacement

/-! G1 room at the captured `whileMin` cut: the nursery left at the cut
(262,044 words) covers the whole F1 budget beyond the 100-word initial heap,
and the 4096-word VM stack holds the budgeted 3,840 words above its threshold. -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot Boot

/-- **G1 room at the `whileMin` cut.** -/
theorem whileMin_g1Room : G1Room g1Budget whileMin.init WhileMin.cut :=
  whileMin_g1Room_of WhileMin.memory_equiv

end OCaml.Vm.Gc

namespace OCaml.Vm.Gc
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot Boot

/-- **The cut's major free block lies above the nursery**: every best-fit
split from it (`BestFitSplit.Post.placed`) stays out of `[young_start, young_end)`. -/
theorem whileMin_free_above_nursery :
    ∃ b, BestFitSingletonAt WhileMin.cut b ∧ (runtimeFields WhileMin.cut).youngEnd + 8 ≤ b.block ∧
      BestFitSplit.FreeIn (b.block - 8) Layout.sym_heap_end (BitVec.ofNat 64 b.block) WhileMin.cut := by
  obtain ⟨b, shape⟩ := (WhileMinRuntime.freeList WhileMin.memory_equiv).shape
  have root := shape.root
  rw [WhileMinRuntime.read_bf_large_tree WhileMin.memory_equiv] at root
  refine ⟨b, shape, ?_, BestFitSplit.freeIn_singleton shape⟩
  rw [WhileMinRuntime.fields WhileMin.memory_equiv, ← root]
  decide +kernel

end OCaml.Vm.Gc

namespace OCaml.Vm.Gc
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot Boot

/-- The cut's least large block lies in a region starting above the nursery. -/
theorem whileMin_leastIn :
    ∃ lo, (runtimeFields WhileMin.cut).youngEnd ≤ lo ∧
      BestFitLarge.LeastIn lo Layout.sym_heap_end WhileMin.cut := by
  obtain ⟨b, shape, above, free⟩ := whileMin_free_above_nursery
  refine ⟨b.block - 8, by omega, ?_⟩
  have least : BestFitLarge.least WhileMin.cut = BitVec.ofNat 64 b.block := by
    apply BitVec.eq_of_toNat_eq
    rw [show (BestFitLarge.least WhileMin.cut).toNat = b.block from shape.least, BitVec.toNat_ofNat]
    have := shape.fits
    simp only [Layout.sym_heap_end, Layout.value_bytes] at this
    omega
  unfold BestFitLarge.LeastIn
  rw [least]
  exact free
