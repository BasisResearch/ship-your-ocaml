import OCaml.Vm.Primitives.Allocation

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A memory-only runtime invariant is transported by the fully determined
post-call byte observations. The platform/allocator supplier establishes this
law; it assumes no execution or primitive postcondition. -/
def ObservationRuntime (runtimeOk : Config → Prop) (before : Config)
    (expected : Nat → BitVec 8) : Prop :=
  ∀ after : Config, (∀ x, byte after x = expected x) → runtimeOk before → runtimeOk after

/-- Represented primitive return for library summaries that expose total
observations rather than exact equality of optional memory maps. -/
structure LibraryPrimitivePost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (v : Val) (value : BitVec 64) (heapAfter : Heap) (worldAfter : World)
    (ra : BitVec 64) (after : Config) : Prop extends LeafInput ra after where
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  data : VmPayload P {s with accu := v, heap := heapAfter, world := worldAfter} after pl cp sp high
  primitives : PrimitiveBindings P after
  platform : PlatformOk runtimeOk after
  loop : LoopRegisters after
  resultRepr : valWord pl v = some value
  semantics : primF1Impl name args s.heap s.world = .ok v heapAfter worldAfter

/-- One finite ABI check preserves all dedicated interpreter registers. -/
theorem loop_of_abi_frame {writes : List Nat} {before after : Config}
    (frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ writes → gpr after n = gpr before n)
    (kept : ∀ n ∈ [Layout.reg_dispatchTable, Layout.reg_opcodeBound, Layout.reg_pending, Layout.reg_domain], n ∉ writes)
    (loop : LoopRegisters before) : LoopRegisters after := by
  exact ⟨(frame _ (by decide) (by decide) (kept _ (by simp))).trans loop.dispatchTable,
    (frame _ (by decide) (by decide) (kept _ (by simp))).trans loop.opcodeBound,
    (frame _ (by decide) (by decide) (kept _ (by simp))).trans loop.pending,
    (frame _ (by decide) (by decide) (kept _ (by simp))).trans loop.domain⟩

end OCaml.Vm.Primitives
