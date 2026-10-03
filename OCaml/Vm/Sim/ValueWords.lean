import OCaml.Vm.Sim.StackPayload

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Pointwise representation of a finite list of VM values by native words. -/
structure ValueWords (pl : Place) (values : List Val) (words : List (BitVec 64)) : Prop where
  length : words.length = values.length
  slots : ∀ (i : Nat) (v : Val), values[i]? = some v → valWord pl v = words[i]?

/-- The empty value list has an empty native representation. -/
theorem ValueWords.nil (pl : Place) : ValueWords pl [] [] :=
  ⟨rfl, fun _ _ h => by simp at h⟩

/-- A represented head joins a represented tail. -/
theorem ValueWords.cons {pl : Place} {v : Val} {w : BitVec 64}
    {values : List Val} {words : List (BitVec 64)}
    (head : valWord pl v = some w) (tail : ValueWords pl values words) :
    ValueWords pl (v :: values) (w :: words) := by
  refine ⟨by simp only [List.length_cons, tail.length], ?_⟩
  intro i x selected
  cases i with
  | zero => cases selected; exact head
  | succ i => exact tail.slots i x selected

/-- Concatenating represented lists requires no per-slot reconstruction. -/
theorem ValueWords.append {pl : Place} {xs ys : List Val} {ws zs : List (BitVec 64)}
    (left : ValueWords pl xs ws) (right : ValueWords pl ys zs) :
    ValueWords pl (xs ++ ys) (ws ++ zs) := by
  refine ⟨by simp only [List.length_append, left.length, right.length], ?_⟩
  intro i v selected
  by_cases first : i < xs.length
  · rw [List.getElem?_append_left first] at selected
    rw [List.getElem?_append_left (by rw [left.length]; exact first)]
    exact left.slots i v selected
  · rw [List.getElem?_append_right (by omega)] at selected
    rw [List.getElem?_append_right (by rw [left.length]; omega), left.length]
    exact right.slots _ v selected

/-- Native words read from the first n slots of an existing represented stack. -/
def stackWords (c : Config) (sp n : Nat) : List (BitVec 64) :=
  (List.range n).map fun i => word c (sp + 8 * i)

/-- The bounded stack prefix supplies all argument-word representation facts. -/
theorem stack_value_words {c : Config} {pl : Place} {sp high n : Nat} {stack : List Val}
    (h : StackRepr c pl sp high stack) (bound : n ≤ stack.length) :
    ValueWords pl (stack.take n) (stackWords c sp n) := by
  constructor
  · simp only [stackWords, List.length_map, List.length_range, List.length_take]
    omega
  · intro i v selected
    have index := (List.getElem?_eq_some_iff.mp selected).1
    simp only [List.length_take] at index
    have within : i < n := by omega
    have old : stack[i]? = some v := by simpa only [List.getElem?_take, within, ite_true] using selected
    simpa only [stackWords, List.getElem?_map, List.getElem?_range, within, ite_true, Option.map_some]
      using h.2 i v old

end OCaml.Vm.Sim
