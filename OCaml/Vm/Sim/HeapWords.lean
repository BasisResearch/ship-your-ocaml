import OCaml.Bytecode.Value

/-!
# The budget measure `Heap.words` under allocation and same-size replacement
-/

namespace OCaml.Bytecode.Heap
set_option autoImplicit false

theorem foldl_words (l : List Obj) (acc : Nat) :
    l.foldl (fun a o => a + o.wosize + 1) acc = acc + (l.map (fun o => o.wosize + 1)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons o l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem words_eq_sum (h : Heap) : h.words = (h.objs.map (fun o => o.wosize + 1)).sum := by
  simp only [words, foldl_words, Nat.zero_add]

/-- Allocation adds the new object's words, header included. -/
theorem words_alloc (h : Heap) (o : Obj) : (h.alloc o).1.words = h.words + (o.wosize + 1) := by
  simp only [words_eq_sum, alloc, objs, Array.toList_push, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Replacing an object by one of the same size keeps the words. -/
theorem words_set {h : Heap} {l : Nat} {old new : Obj} (found : h.get? l = some old)
    (size : new.wosize = old.wosize) : (h.set l new).words = h.words := by
  simp only [words_eq_sum, set, objs, Array.toList_setIfInBounds, List.map_set]
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have at_l : (h.storage.toList.map (fun o => o.wosize + 1))[l]'(by simpa using bound) = new.wosize + 1 := by
    simp only [List.getElem_map, size]
    have := (List.getElem?_eq_some_iff.mp found).2
    rw [this]
  rw [← at_l, List.set_getElem_self]

end OCaml.Bytecode.Heap
