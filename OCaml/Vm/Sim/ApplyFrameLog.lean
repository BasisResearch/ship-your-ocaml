import OCaml.Vm.Sim.IndexedStores

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Sim

/-- Native order in which each fixed-arity APPLY saves its new frame words. -/
def applyFrameOrder (arity : Nat) : List Nat :=
  if arity = 1 then [3, 1, 2, 0]
  else if arity = 2 then [2, 3, 1, 0, 4]
  else if arity = 3 then [5, 2, 1, 4, 0, 3]
  else []

/-- Complete logical word order: arguments followed by the saved caller frame. -/
def applyFrameWords (args : List (BitVec 64)) (code env extra : BitVec 64) : List (BitVec 64) :=
  args ++ [code, env, extra]

/-- Indexed native stores, keeping the machine order separate from logical order. -/
def applyFrameEntries (args : List (BitVec 64)) (code env extra : BitVec 64) : List (Nat × BitVec 64) :=
  (applyFrameOrder args.length).map fun i => (i, ((applyFrameWords args code env extra)[i]?).getD 0)

/-- The finite compiler-generated schedules write every frame word exactly once. -/
theorem apply_order_distinct {n : Nat} (positive : 1 ≤ n) (small : n ≤ 3) :
    (applyFrameOrder n).Nodup := by
  have cases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

theorem apply_order_member {n i : Nat} (positive : 1 ≤ n) (small : n ≤ 3) :
    i ∈ applyFrameOrder n ↔ i < n + 3 := by
  have cases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl <;> simp only [applyFrameOrder, ite_true, ite_false,
    Nat.reduceEqDiff, List.mem_cons, List.not_mem_nil, or_false] <;> omega

/-- The indexed-store theorem applies uniformly to every fixed-arity schedule. -/
theorem apply_entries_distinct {args : List (BitVec 64)} (code env extra : BitVec 64)
    (positive : 1 ≤ args.length) (small : args.length ≤ 3) :
    ((applyFrameEntries args code env extra).map Prod.fst).Nodup := by
  simpa [applyFrameEntries, List.map_map, Function.comp_def]
    using apply_order_distinct positive small

/-- A selected logical frame word occurs in the native indexed store list. -/
theorem apply_entries_selected {args : List (BitVec 64)} {code env extra value : BitVec 64} {i : Nat}
    (positive : 1 ≤ args.length) (small : args.length ≤ 3)
    (selected : (applyFrameWords args code env extra)[i]? = some value) :
    (i, value) ∈ applyFrameEntries args code env extra := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  simp only [applyFrameWords, List.length_append, List.length_cons, List.length_nil] at bound
  apply List.mem_map.mpr
  exact ⟨i, (apply_order_member positive small).mpr bound, by rw [selected]; rfl⟩

/-- Every indexed store lies within the newly installed argument/caller prefix. -/
theorem apply_entries_in {args : List (BitVec 64)} (base : Nat) (code env extra : BitVec 64)
    (positive : 1 ≤ args.length) (small : args.length ≤ 3) :
    LogInW [⟨base, base + 8 * (args.length + 3)⟩]
      (indexedLog base (applyFrameEntries args code env extra)) := by
  apply indexed_log_in
  intro entry member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  exact (apply_order_member positive small).mp hi

end OCaml.Vm.Sim
