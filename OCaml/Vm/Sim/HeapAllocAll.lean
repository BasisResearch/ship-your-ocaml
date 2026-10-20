import OCaml.Vm.Sim.AllocChain
import OCaml.Vm.Primitives.Allocation

/-!
# Representing several fresh objects at once

`heap_allocate` extends a represented heap with one object and makes it the
accumulator. A primitive that allocates a chain (each object pointing at the
previous ones, the last one returned) cannot go one object at a time: the
intermediate accumulators drop the earlier objects from the roots.
`heap_allocate_all` extends the heap with all of `allocAll`'s objects and
then sets the accumulator, given that every new pointer is new or old-live.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem Heap.size_alloc (h : Heap) (o : Obj) : (h.alloc o).1.size = h.size + 1 := by
  simp [Heap.alloc, Heap.size]

theorem Heap.loc_alloc (h : Heap) (o : Obj) : (h.alloc o).2 = h.size := rfl

theorem allocAll_size (os : List Obj) : ∀ h : Heap, (allocAll h os).size = h.size + os.length := by
  induction os with
  | nil => intro h; rfl
  | cons o os ih => intro h; simp only [allocAll, ih, Heap.size_alloc, List.length_cons]; omega

theorem allocAll_get_old (os : List Obj) : ∀ (h : Heap) (l : Nat), l < h.size →
    (allocAll h os).get? l = h.get? l := by
  induction os with
  | nil => intro h l _; rfl
  | cons o os ih =>
    intro h l hl
    simp only [allocAll]
    rw [ih _ l (by rw [Heap.size_alloc]; omega), Heap.get_alloc_old _ _ _ (by simpa [Heap.size] using hl)]

theorem allocAll_get_new (os : List Obj) : ∀ (h : Heap) (i : Nat), (allocAll h os).get? (h.size + i) = os[i]? := by
  induction os with
  | nil =>
    intro h i
    simp only [allocAll, List.getElem?_nil]
    simp [Heap.get?, Heap.size]
  | cons o os ih =>
    intro h i
    simp only [allocAll]
    cases i with
    | zero =>
      rw [Nat.add_zero, allocAll_get_old _ _ _ (by rw [Heap.size_alloc]; omega)]
      exact Heap.get_alloc_fresh h o
    | succ i =>
      rw [show h.size + (i + 1) = (h.alloc o).1.size + i by rw [Heap.size_alloc]; omega, ih]; rfl

/-- **Reachability after a chain of allocations**: a live location is new,
or was live before. -/
theorem live_after_allocAll {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {os : List Obj}
    {v : Val} {l : Nat} (h : HeapRepr c pl cp P s)
    (fields : ∀ (i t : Nat) (fs : List Val), os[i]? = some (Obj.block t fs) → ∀ u ∈ fs, ∀ l, Val.loc? u = some l →
      (s.heap.size ≤ l ∧ l < s.heap.size + os.length) ∨ Live s.heap (roots P s) l)
    (vRoot : ∀ l, v.loc? = some l → (s.heap.size ≤ l ∧ l < s.heap.size + os.length) ∨ Live s.heap (roots P s) l)
    (live : Live (allocAll s.heap os) (roots P {s with heap := allocAll s.heap os, accu := v}) l) :
    (s.heap.size ≤ l ∧ l < s.heap.size + os.length) ∨ Live s.heap (roots P s) l := by
  -- discipline: allow(O5-run-induction) induction on heap-graph reachability, not a machine or bytecode run
  induction live with
  | root hv hl =>
    change _ ∈ v :: _ at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact vRoot _ hl
    · exact Or.inr (Live.root (List.mem_cons_of_mem _ hv) hl)
  | @field parent child t fs u hp hg hu hl ih =>
    rcases ih with ⟨lo, hi⟩ | old
    · obtain ⟨i, rfl⟩ : ∃ i, parent = s.heap.size + i := ⟨parent - s.heap.size, by omega⟩
      rw [allocAll_get_new] at hg
      exact fields i t fs hg u hu child hl
    · have bound := heap_live_bound h old
      rw [allocAll_get_old _ _ _ (by simpa [Heap.size] using bound)] at hg
      exact Or.inr (Live.field old hg hu hl)

/-- **Extend a represented heap with a chain of fresh objects**, each placed
and laid out, apart from the old live objects and from each other; the
accumulator becomes `v`. -/
theorem heap_allocate_all {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {os : List Obj}
    {v : Val} (h : HeapRepr c pl cp P s) (addr : Nat → Nat)
    (fields : ∀ (i t : Nat) (fs : List Val), os[i]? = some (Obj.block t fs) → ∀ u ∈ fs, ∀ l, Val.loc? u = some l →
      (s.heap.size ≤ l ∧ l < s.heap.size + os.length) ∨ Live s.heap (roots P s) l)
    (vRoot : ∀ l, v.loc? = some l → (s.heap.size ≤ l ∧ l < s.heap.size + os.length) ∨ Live s.heap (roots P s) l)
    (placed : ∀ i, i < os.length → pl.φ (s.heap.size + i) = some (addr i))
    (layout : ∀ i o, os[i]? = some o → ObjAt c pl cp (addr i) o)
    (outside : ∀ i o, os[i]? = some o → AllocationOutside P s pl (addr i) o)
    (apart : ∀ i j o o', i ≠ j → os[i]? = some o → os[j]? = some o' →
      addr i + 8 * o.wosize ≤ addr j - 8 ∨ addr j + 8 * o'.wosize ≤ addr i - 8) :
    HeapRepr c pl cp P {s with heap := allocAll s.heap os, accu := v} := by
  have newGet : ∀ i, i < os.length → ∃ o, os[i]? = some o := fun i hi => ⟨os[i], List.getElem?_eq_getElem hi⟩
  constructor
  · intro l hl
    rcases live_after_allocAll h fields vRoot hl with ⟨lo, hi⟩ | old
    · obtain ⟨i, rfl⟩ : ∃ i, l = s.heap.size + i := ⟨l - s.heap.size, by omega⟩
      obtain ⟨o, ho⟩ := newGet i (by omega)
      exact ⟨addr i, o, placed i (by omega), by rw [allocAll_get_new]; exact ho, layout i o ho⟩
    · obtain ⟨b, ob, hp, hg, ho⟩ := h.1 l old
      have bound := heap_live_bound h old
      exact ⟨b, ob, hp, by rw [allocAll_get_old _ _ _ (by simpa [Heap.size] using bound)]; exact hg, ho⟩
  · intro l l' b b' ob ob' hl hl' ne hp hp' hg hg'
    rcases live_after_allocAll h fields vRoot hl with ⟨lo, hi⟩ | old <;>
      rcases live_after_allocAll h fields vRoot hl' with ⟨lo', hi'⟩ | old'
    · obtain ⟨i, rfl⟩ : ∃ i, l = s.heap.size + i := ⟨l - s.heap.size, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, l' = s.heap.size + j := ⟨l' - s.heap.size, by omega⟩
      rw [allocAll_get_new] at hg hg'
      rw [placed i (by omega), Option.some.injEq] at hp
      rw [placed j (by omega), Option.some.injEq] at hp'
      subst hp hp'
      exact apart i j ob ob' (fun e => ne (by rw [e])) hg hg'
    · obtain ⟨i, rfl⟩ : ∃ i, l = s.heap.size + i := ⟨l - s.heap.size, by omega⟩
      rw [allocAll_get_new] at hg
      rw [placed i (by omega), Option.some.injEq] at hp
      subst hp
      have bound := heap_live_bound h old'
      rw [allocAll_get_old _ _ _ (by simpa [Heap.size] using bound)] at hg'
      exact outside i ob hg l' b' ob' old' hp' hg'
    · obtain ⟨j, rfl⟩ : ∃ j, l' = s.heap.size + j := ⟨l' - s.heap.size, by omega⟩
      rw [allocAll_get_new] at hg'
      rw [placed j (by omega), Option.some.injEq] at hp'
      subst hp'
      have bound := heap_live_bound h old
      rw [allocAll_get_old _ _ _ (by simpa [Heap.size] using bound)] at hg
      exact (outside j ob' hg' l b ob old hp hg).symm
    · have bound := heap_live_bound h old
      have bound' := heap_live_bound h old'
      rw [allocAll_get_old _ _ _ (by simpa [Heap.size] using bound)] at hg
      rw [allocAll_get_old _ _ _ (by simpa [Heap.size] using bound')] at hg'
      exact h.2 l l' b b' ob ob' old old' ne hp hp' hg hg'

end OCaml.Vm.Sim
