import OCaml.Vm.Sim.OutListAdapter

/-! Conditional obstructions to the old listing interfaces. These do not
assert a reachable machine counterexample or inconsistency of the runtime. -/
namespace OCaml.Vm.Sim.OutListWalk
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- The saved-slot interval contains heapEnd at the arbitrary pointer
heapEnd + 16, including when the semantic stack is empty. -/
theorem VmPoint.arbitrary_stack (P : Prog) (s : St) (c : Config)
    (pl : OCaml.Vm.Place) (cp : OCaml.Vm.ChanPlace) :
    VmPoint P s c pl cp (Vsa.Sim.DlHeap.heapEnd + 16) Vsa.Sim.DlHeap.heapEnd := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))

/-- The old entry's bound cannot hold for every sp at any supplied runtime
and geometry witness. No existence or reachability of that witness is claimed. -/
theorem unrestricted_entry_obstruction {L : OCaml.Layout} {P : Prog} {s : St}
    {c : Config} {pl : OCaml.Vm.Place} {cp : OCaml.Vm.ChanPlace} {high : Nat}
    (runtime : L.runtimeOk c) (geometry : OCaml.LoopGeometry L P s c pl cp high)
    (entry : L.runtimeOk c → OCaml.LoopGeometry L P s c pl cp high →
      ∀ sp a, VmPoint P s c pl cp sp a → a < Vsa.Sim.DlHeap.heapEnd) : False := by
  have impossible := entry runtime geometry _ _ (VmPoint.arbitrary_stack P s c pl cp)
  exact Nat.lt_irrefl _ impossible

end OCaml.Vm.Sim.OutListWalk
