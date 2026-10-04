import OCaml.Vm.Sim.ClosurerecLayout
import OCaml.Vm.Sim.AllocateStack

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Read and assemble the descending recursive-closure pointers above an
already represented surviving stack tail. Earlier allocation writes are arbitrary. -/
theorem closurerec_stack_words {before after : Config} {s : St} {pl : Place}
    {sp count a dest fresh high : Nat} {targets : List Nat} {front : List WEntry}
    (placed : pl.φ fresh = some a)
    (room : 8 * targets.length ≤ closurerecStackStart sp count)
    (heapBelow : a + 24 * targets.length + 16 ≤ closurerecStackStart sp count - 8 * targets.length)
    (tail : StackRepr after pl (closurerecStackStart sp count + 8) high (s.stack.drop (count - 1)))
    (memory : after.σ.mem = writeLog before.σ.mem
      ((front ++ closurerecFirstLog pl sp (targets.length + 1) count dest a) ++
        (infixGroups pl a (closurerecStackStart sp count) targets).flatten)) :
    StackRepr after pl (closurerecStackStart sp count - 8 * targets.length) high
      (closurerecStack s count (targets.length + 1) fresh) := by
  have firstPointer : word after (closurerecStackStart sp count) = BitVec.ofNat 64 a := by
    have outside : OutLRange (infixGroups pl a (closurerecStackStart sp count) targets).flatten
        (closurerecStackStart sp count) 8 := by
      apply outLRange_of_windows (infix_groups_in pl a _ targets room)
      exact ⟨Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), trivial⟩
    rw [word, memory, writeLog_append, bytesT_writeLog_out _ outside, writeLog_append]
    apply word_writeLog_at _ _ 0 _ _ rfl
    exact ⟨Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), trivial⟩
  have firstStack : StackRepr after pl (closurerecStackStart sp count) high
      (Val.ptr fresh 0 :: s.stack.drop (count - 1)) := by
    apply stack_prepend (front := [Val.ptr fresh 0]) tail rfl
    intro i v selected
    cases i with
    | zero =>
      cases selected
      simp only [Nat.mul_zero, Nat.add_zero, firstPointer, valWord, placed, Option.map_some]
    | succ i => simp at selected
  apply stack_prepend firstStack
  · simp only [List.length_map, List.length_reverse, List.length_drop, List.length_range, Nat.add_sub_cancel]
    omega
  · intro i v selected
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    simp only [List.length_map, List.length_reverse, List.length_drop, List.length_range, Nat.add_sub_cancel] at bound
    have slot : (((List.range (targets.length + 1)).drop 1).reverse.map
        (fun k => Val.ptr fresh (3 * k)))[i]? = some (Val.ptr fresh (3 * (targets.length - i))) := by
      rw [List.getElem?_map, List.getElem?_reverse (by simpa using bound), List.getElem?_drop]
      simp only [List.length_drop, List.length_range, Nat.add_sub_cancel]
      have indexEq : 1 + (targets.length - 1 - i) = targets.length - i := by omega
      rw [indexEq]
      simp [List.getElem?_range, show targets.length - i < targets.length + 1 by omega]
    have valueEq := Option.some.inj (selected.symm.trans slot)
    subst v
    have jBound : targets.length - i - 1 < targets.length := by omega
    have ptrRead : word after (closurerecStackStart sp count - 8 * targets.length + 8 * i) =
        BitVec.ofNat 64 (a + 24 * (targets.length - i)) := by
      have jEq : targets.length - i - 1 + 1 = targets.length - i := by omega
      have address : closurerecStackStart sp count - 8 * targets.length + 8 * i =
          closurerecStackStart sp count - 8 * (targets.length - i) := by omega
      rw [word, memory, writeLog_append, address, ← jEq]
      exact infix_groups_stack_read pl a _ targets (targets.length - i - 1) jBound room heapBelow _
    rw [ptrRead]
    simp only [valWord, placed, Option.map_some]
    congr 2
    omega

end OCaml.Vm.Sim
