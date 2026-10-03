import OCaml.Vm.Sim.FieldRead
import OCaml.Vm.Sim.ValueWords

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Ordinary block-base selection, shared by closure field-copy arms. -/
structure BlockSelection (heap : Heap) (pl : Place) (source : Val) (l a tag : Nat) (fields : List Val) : Prop where
  pointer : source = .ptr l 0
  placed : pl.φ l = some a
  object : heap.get? l = some (.block tag fields)

theorem BlockSelection.sourceWord {heap : Heap} {pl : Place} {source : Val}
    {l a tag : Nat} {fields : List Val} (f : BlockSelection heap pl source l a tag fields) :
    valWord pl source = some (BitVec.ofNat 64 a) := by
  simp only [f.pointer, valWord, f.placed, Option.map_some, Nat.mul_zero, Nat.add_zero]

theorem BlockSelection.live {P : Prog} {s : St} {pl : Place} {source : Val}
    {l a tag : Nat} {fields : List Val} (f : BlockSelection s.heap pl source l a tag fields)
    (member : source ∈ roots P s) : Live s.heap (roots P s) l :=
  Live.root member (by simp [f.pointer, Val.loc?])

/-- An ordinary block's represented header supplies its exact field count. -/
theorem BlockSelection.header {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a tag : Nat} {source : Val} {fields : List Val}
    (f : BlockSelection s.heap pl source l a tag fields) (h : VmPayload P s c pl cp sp high)
    (member : source ∈ roots P s) : (word c (a - 8)).toNat / 1024 = fields.length :=
  (h.object_at (f.live member) f.placed f.object).1.2

/-- Every suffix of the block's fields has a native word-list representation. -/
theorem BlockSelection.words {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a tag : Nat} {source : Val} {fields : List Val}
    (f : BlockSelection s.heap pl source l a tag fields) (h : VmPayload P s c pl cp sp high)
    (member : source ∈ roots P s) (offset : Nat) :
    ValueWords pl (fields.drop offset) (stackWords c (a + 8 * offset) (fields.length - offset)) := by
  have represented := h.object_at (f.live member) f.placed f.object
  constructor
  · simp [stackWords]
  · intro i v selected
    have index := (List.getElem?_eq_some_iff.mp selected).1
    have inside : i < fields.length - offset := by simpa only [List.length_drop] using index
    have original : fields[offset + i]? = some v := by simpa only [List.getElem?_drop] using selected
    have value := represented.2 (offset + i) v original
    simpa only [stackWords, List.getElem?_map, List.getElem?_range, inside, ite_true,
      Option.map_some, Nat.mul_add, Nat.add_assoc] using value

/-- A selected field retains the block's placement and original heap relation. -/
theorem BlockSelection.field {heap : Heap} {pl : Place} {source v : Val} {l a tag i : Nat} {fields : List Val}
    (f : BlockSelection heap pl source l a tag fields) (selected : fields[i]? = some v) :
    FieldSelection heap pl source i v l a 0 := by
  refine ⟨f.pointer, f.placed, ?_⟩
  simpa only [f.pointer, field?, f.object, Nat.zero_add] using selected

/-- A suffix field root is already reachable from its source block. -/
theorem BlockSelection.field_root {P : Prog} {s : St} {pl : Place} {source v : Val}
    {l a tag offset : Nat} {fields : List Val} (f : BlockSelection s.heap pl source l a tag fields)
    (member : source ∈ roots P s) (selected : v ∈ fields.drop offset) :
    ∀ loc, v.loc? = some loc → Live s.heap (roots P s) loc :=
  fun _ loc => Live.field (f.live member) f.object (List.mem_of_mem_drop selected) loc

end OCaml.Vm.Sim
