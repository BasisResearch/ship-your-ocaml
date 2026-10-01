import OCaml.Vm.Boot.WhileMinHeapObjects

/-! Assembly of the checked finite object table into the live-heap relation. -/
namespace OCaml.Vm.Boot.WhileMinHeap
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot WhileMinLog

variable {c : Config} {initial : Vsa.MemRepr.Mem} {cp : ChanPlace}

/-- The observed placement covers every object and has disjoint blocks. -/
theorem image (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) :
    HeapImage c place cp whileMin.heap0 where
  objects := objects memory
  separated := by
    intro l l' a a' o o' ne ha ha' ho ho'
    change addresses[l]? = some a at ha
    change addresses[l']? = some a' at ha'
    change whileMinHeap[l]? = some o at ho
    change whileMinHeap[l']? = some o' at ho'
    obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp ho
    obtain ⟨hl', rfl⟩ := List.getElem?_eq_some_iff.mp ho'
    obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp ha'
    exact separated ⟨l, hl⟩ ⟨l', hl'⟩ (fun eq => ne (congrArg Fin.val eq))

/-- The production live-heap predicate for the observed memory candidate. -/
theorem repr (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) :
    HeapRepr c place cp whileMin whileMin.init :=
  (image memory).repr closed

end OCaml.Vm.Boot.WhileMinHeap
