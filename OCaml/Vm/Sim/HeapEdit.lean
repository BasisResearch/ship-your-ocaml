import OCaml.Vm.Sim.FieldRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- A bounded heap replacement changes the selected object. -/
theorem heap_set_here {heap : Heap} {l : Nat} {old : Obj} (new : Obj)
    (selected : heap.get? l = some old) : (heap.set l new).get? l = some new := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  simpa only [Heap.set, Heap.get?, Array.toList_setIfInBounds] using
    (List.getElem?_set_self (a := new) bound)

/-- Every other abstract object survives a replacement unchanged. -/
theorem heap_set_other (heap : Heap) (l q : Nat) (new : Obj) (different : l ≠ q) :
    (heap.set l new).get? q = heap.get? q := by
  simp only [Heap.set, Heap.get?, Array.toList_setIfInBounds, List.getElem?_set_ne different]

/-- Updating an existing field introduces no new live objects when its value
is already an old root. This is a heap-graph law, independent of execution. -/
theorem live_field_edit {heap : Heap} {rs : List Val} {l i tag : Nat} {fields : List Val} {value : Val}
    (selected : heap.get? l = some (.block tag fields))
    (root : ∀ loc, value.loc? = some loc → Live heap rs loc)
    {loc : Nat} (live : Live (heap.set l (.block tag (fields.set i value))) rs loc) :
    Live heap rs loc := by
  -- discipline: allow(O5-run-induction) induction on heap-graph reachability, not execution
  induction live with
  | root hv hl => exact Live.root hv hl
  | @field parent child t fs v _ object member pointer ih =>
    by_cases equal : parent = l
    · subst parent
      rw [heap_set_here _ selected] at object
      cases object
      rcases List.mem_or_eq_of_mem_set member with old | rfl
      · exact Live.field ih selected old pointer
      · exact root child pointer
    · rw [heap_set_other heap l parent _ (Ne.symm equal)] at object
      exact Live.field ih object member pointer

/-- A size-preserving replacement retains every object's footprint size. -/
theorem heap_set_size {heap : Heap} {l q : Nat} {old new before after : Obj}
    (selected : heap.get? l = some old) (size : new.wosize = old.wosize)
    (oldLookup : heap.get? q = some before) (newLookup : (heap.set l new).get? q = some after) :
    after.wosize = before.wosize := by
  by_cases equal : q = l
  · subst q
    have beforeEq : before = old := Option.some.inj (oldLookup.symm.trans selected)
    have afterEq : after = new := Option.some.inj (newLookup.symm.trans (heap_set_here new selected))
    simpa only [beforeEq, afterEq] using size
  · rw [heap_set_other heap l q new (Ne.symm equal), oldLookup] at newLookup
    cases newLookup
    rfl

/-- Heap layout restoration factors object readback from reachability and
unchanged footprint sizes. Store-specific proofs supply only ObjAt facts. -/
theorem heap_field_edit {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {l i tag : Nat} {fields : List Val} {value : Val}
    (heap : HeapRepr before pl cp P s)
    (selected : s.heap.get? l = some (.block tag fields))
    (root : ∀ loc, value.loc? = some loc → Live s.heap (roots P s) loc)
    (objects : ∀ q a o, Live s.heap (roots P s) q → pl.φ q = some a →
      (s.heap.set l (.block tag (fields.set i value))).get? q = some o → ObjAt after pl cp a o) :
    HeapRepr after pl cp P {s with heap := s.heap.set l (.block tag (fields.set i value))} := by
  have oldLive {q : Nat} (live : Live (s.heap.set l (.block tag (fields.set i value))) (roots P s) q) :=
    live_field_edit selected root live
  have size : (Obj.block tag (fields.set i value)).wosize = (Obj.block tag fields).wosize := by
    simp only [Obj.wosize, List.length_set]
  constructor
  · intro q live
    have old := oldLive live
    obtain ⟨a, o, placed, lookup, _⟩ := heap.1 q old
    by_cases equal : q = l
    · subst q
      have updated := heap_set_here (.block tag (fields.set i value)) selected
      exact ⟨a, _, placed, updated, objects _ _ _ old placed updated⟩
    · have unchanged := (heap_set_other s.heap l q (.block tag (fields.set i value)) (Ne.symm equal)).trans lookup
      exact ⟨a, o, placed, unchanged, objects _ _ _ old placed unchanged⟩
  · intro q q' a a' o o' live live' different placed placed' lookup lookup'
    obtain ⟨b, old, _, oldLookup, _⟩ := heap.1 q (oldLive live)
    obtain ⟨b', old', _, oldLookup', _⟩ := heap.1 q' (oldLive live')
    rw [heap_set_size selected size oldLookup lookup, heap_set_size selected size oldLookup' lookup']
    exact heap.2 q q' a a' old old' (oldLive live) (oldLive live') different placed placed' oldLookup oldLookup'

end OCaml.Vm.Sim
