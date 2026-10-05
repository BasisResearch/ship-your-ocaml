import OCaml.Vm.Boot.WhileMin
import OCaml.Programs.WhileMinChecks
import OCaml.Vm.Gc.FreePlacement

/-! G1 room at the captured `whileMin` cut: the nursery left at the cut
(262,044 words) covers the whole F1 budget beyond the 100-word initial heap,
and the 4096-word VM stack holds the budgeted 3,840 words above its threshold. -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot Boot

theorem whileMin_init_words : whileMin.init.heap.words = 100 := by decide +kernel

/-- Room for any configuration whose memory is the certified cut memory. -/
theorem whileMin_g1Room_of {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial WhileMinLog.log)) :
    G1Room g1Budget whileMin.init c := by
  have dom : (word c Layout.sym_Caml_state).toNat = WhileMinRuntime.domain :=
    congrArg BitVec.toNat (WhileMinRuntime.read_domain memory)
  have threshold : stackThreshold c = 0x80383fb0 := by
    simp only [stackThreshold, domainWord, dom, WhileMinEntry.read_stack_threshold memory]; rfl
  have high : stackHigh c = 0x8038b7b0 := by
    simp only [stackHigh, domainWord, dom, WhileMinEntry.read_stack_high memory]; rfl
  constructor
  · rw [WhileMinRuntime.fields memory, whileMin_init_words]
    decide +kernel
  · rw [threshold, high]
    decide +kernel

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
