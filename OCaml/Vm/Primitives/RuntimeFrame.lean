import OCaml.Vm.Primitives.Payload
import OCaml.Vm.Runtime

namespace OCaml.Vm.Primitives
open Vsa.Machine

/-- The chosen collector invariant is stable under the memory-preserving
primitive family whenever its abstract free-list predicate has that property. -/
theorem runtime_memory_stable {freeList : Config → Prop} (hf : MemoryStable freeList) :
    MemoryStable (RuntimeOk freeList) := by
  intro c c' hm h
  have he : runtimeFields c' = runtimeFields c := by
    simp only [runtimeFields, domainWord, word, word32, hm]
  exact ⟨he ▸ h.bounds, he ▸ h.noPending, hf c c' hm h.freeListShape⟩

end OCaml.Vm.Primitives
