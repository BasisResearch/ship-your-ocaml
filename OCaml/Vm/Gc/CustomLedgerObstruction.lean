import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Boot.WhileMinAllocator

/-! The captured allocator permits a nonexhaustive, empty live ledger.
This refutes the former universal-ledger ownership field at actual arena
bytes. It makes no claim that `CustomMemCall` is globally inconsistent. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.VsaHeap
open OCaml.Vm.Boot OCaml.Vm.Boot.Startup

/-- Erasing the ledger does not erase the certified allocator shape. -/
theorem captured_empty_ready {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem WhileMinImage.initialMem WhileMinLog.log)) :
    HeapReady [] (2 ^ 24) c := by
  have selected := WhileMinAllocator.ready memory
  have transported := WhileMinAllocator.heap_transport memory
  refine { selected with room := ⟨by decide, WhileMinAllocator.memory, WhileMinAllocator.top, WhileMinAllocator.brk,
    WhileMinAllocator.chunks, WhileMinAllocator.bins, ?_, ?_,
    WhileMinAllocator.capacity⟩ }
  · intro a ha
    have ram : Vsa.Densify.ramBase ≤ a ∧
        a < Vsa.Densify.ramBase + Vsa.Densify.ramSize := by
      rcases ha with global | ⟨low, high, _⟩
      · unfold allocGlobal InRange at global
        unfold Vsa.Densify.ramBase Vsa.Densify.ramSize
        omega
      · simp only [heapStart, heapEnd] at low high
        unfold Vsa.Densify.ramBase Vsa.Densify.ramSize
        omega
    rw [show WhileMinAllocator.memory = Vsa.Densify.fillZeroMem
      (Vsa.Sim.Boot.observedMem WhileMinImage.initialMem WhileMinLog.log) from rfl,
      Vsa.Densify.fillZeroMem_ram _ ram.1 ram.2]
    exact congrArg some (memory a).symm
  · exact { heap := ⟨{ WhileMinAllocator.raw_heap with exact := fun _ h => nomatch h }, by decide⟩
            brk_page := transported.brk_page
            bb_lt := WhileMinAllocator.heap.bb_lt }


/-- Every arena byte belongs to the allocator footprint for the empty ledger. -/
theorem empty_ledger_arena {a : Nat} (low : heapStart ≤ a) (high : a < heapEnd) :
    vsaFoot [] a :=
  Or.inr ⟨low, high, fun _ h => nomatch h⟩

/-- The former `CallerApart.free` cannot describe an actual arena byte at
the captured cut, even though the allocator itself is ready there. -/
theorem captured_universal_free_obstruction {c : Config} {a : Nat}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem WhileMinImage.initialMem WhileMinLog.log))
    (low : heapStart ≤ a) (high : a < heapEnd) :
    ¬ (∀ H cap, HeapReady H cap c → ¬ vsaFoot H a) := by
  intro free
  exact free [] (2 ^ 24) (captured_empty_ready memory) (empty_ledger_arena low high)

/-- Two actual custom-state bytes excluded by the old field: the domain's
minor resource accumulator and the custom table's base word. -/
theorem captured_custom_bytes_obstruction {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem WhileMinImage.initialMem WhileMinLog.log)) :
    ∀ a ∈ [WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor,
      WhileMinRuntime.customTable],
      ¬ (∀ H cap, HeapReady H cap c → ¬ vsaFoot H a) := by
  intro a member
  apply captured_universal_free_obstruction memory
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

/-- The actual captured configuration admits empty-ledger readiness. -/
theorem cut_empty_ready : HeapReady [] (2 ^ 24) WhileMin.cut :=
  captured_empty_ready WhileMin.memory_equiv

/-- Premise-free specialization to the actual captured cut and its custom
state addresses. No reset-to-cut execution is asserted. -/
theorem cut_custom_bytes_obstruction :
    ∀ a ∈ [WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor,
      WhileMinRuntime.customTable],
      ¬ (∀ H cap, HeapReady H cap WhileMin.cut → ¬ vsaFoot H a) :=
  captured_custom_bytes_obstruction WhileMin.memory_equiv

end OCaml.Vm.Gc
