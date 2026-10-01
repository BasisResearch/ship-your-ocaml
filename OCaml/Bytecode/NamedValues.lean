import OCaml.Bytecode.Semantics

namespace OCaml.Bytecode

/-- Updating a named root makes its newest value observable by that key. -/
theorem registerNamedValue_lookup (name : String) (v : Val) (entries : List (String × Val)) :
    (registerNamedValue name v entries).lookup name = some v := by
  induction entries with
  | nil => simp [registerNamedValue]
  | cons pair rest ih =>
    obtain ⟨key, old⟩ := pair
    by_cases same : key = name
    · simp [registerNamedValue, same]
    · simp [registerNamedValue, same, beq_eq_false_iff_ne.mpr (Ne.symm same), List.lookup, ih]

/-- Registering a key cannot change the lookup result for another key. -/
theorem registerNamedValue_lookup_other (name other : String) (v : Val)
    (entries : List (String × Val)) (different : other ≠ name) :
    (registerNamedValue name v entries).lookup other = entries.lookup other := by
  induction entries with
  | nil => simp [registerNamedValue, List.lookup, beq_eq_false_iff_ne.mpr different]
  | cons pair rest ih =>
    obtain ⟨key, old⟩ := pair
    by_cases same : key = name
    · simp [registerNamedValue, same, List.lookup, beq_eq_false_iff_ne.mpr different]
    · simp [registerNamedValue, same, List.lookup, ih]

/-- Every post-registration root is the new value or a retained old root. -/
theorem registerNamedValue_member (name : String) (v : Val) (entries : List (String × Val))
    (pair : String × Val) (member : pair ∈ registerNamedValue name v entries) :
    pair.2 = v ∨ pair ∈ entries := by
  induction entries with
  | nil =>
    simp only [registerNamedValue, List.mem_singleton] at member
    exact Or.inl (congrArg Prod.snd member)
  | cons head rest ih =>
    obtain ⟨key, old⟩ := head
    by_cases same : key = name
    · simp only [registerNamedValue, same, beq_self_eq_true, ite_true, List.mem_cons] at member
      rcases member with fresh | retained
      · exact Or.inl (congrArg Prod.snd fresh)
      · exact Or.inr (List.mem_cons_of_mem _ retained)
    · simp [registerNamedValue, same] at member
      rcases member with retained | tail
      · exact Or.inr (List.mem_cons.mpr (Or.inl retained))
      · rcases ih tail with fresh | retained
        · exact Or.inl fresh
        · exact Or.inr (List.mem_cons_of_mem _ retained)

/-- Closed observations mirror the host callback.c probe. -/
theorem named_replacement_check :
    registerNamedValue "a1-replaced" (Val.ofInt 22)
      (registerNamedValue "a1-replaced" (Val.ofInt 11) []) =
        [("a1-replaced", Val.ofInt 22)] := by decide +kernel

theorem named_first_nul_check :
    namedValueKey [97, 49, 0, 108] = namedValueKey [97, 49, 0, 114] ∧
    namedValueKey [97, 49, 0, 108] = "a1" := by decide +kernel

/-- The actual primitive transition replaces a named root without keeping its
obsolete value in World.named. This checks the semantics route, not just a helper. -/
theorem named_primitive_replacement (w : World) :
    let heap : Heap := ⟨#[.bytes [97, 49, 0, 108]]⟩
    primF1Impl "caml_register_named_value" [.ptr 0 0, Val.ofInt 44] heap
      {w with named := [("a1", Val.ofInt 33)]} =
      .ok .unit heap {w with named := [("a1", Val.ofInt 44)]} := by rfl

end OCaml.Bytecode
