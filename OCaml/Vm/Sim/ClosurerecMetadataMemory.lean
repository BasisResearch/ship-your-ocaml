import OCaml.Vm.Sim.ClosurerecMetadataRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The complete metadata log represents the bytecode model's function fields,
independently of all earlier allocation and capture writes. -/
theorem closurerec_metadata_memory {before after : Config} {pl : Place}
    {a sp count dest : Nat} {targets : List Nat} {front : List WEntry}
    (small : 6 * (targets.length + 1) < 2^64)
    (room : 8 * targets.length ≤ closurerecStackStart sp count)
    (heapBelow : a + 24 * targets.length + 16 ≤ closurerecStackStart sp count - 8 * targets.length)
    (memory : after.σ.mem = writeLog before.σ.mem
      ((front ++ closurerecFirstLog pl sp (targets.length + 1) count dest a) ++
        (infixGroups pl a (closurerecStackStart sp count) targets).flatten)) :
    ∀ i v, (closurerecFunctionValues (dest :: targets))[i]? = some v →
      valWord pl v = some (word after (a + 8 * i)) := by
  have firstRead (i address : Nat) (value : BitVec 64)
      (selected : (closurerecFirstLog pl sp (targets.length + 1) count dest a)[i]? = some (address, 8, value))
      (later : OutLRange ((closurerecFirstLog pl sp (targets.length + 1) count dest a).drop (i + 1)) address 8)
      (upper : address + 8 ≤ a + 16) : word after address = value := by
    have outside : OutLRange (infixGroups pl a (closurerecStackStart sp count) targets).flatten address 8 := by
      apply outLRange_of_windows (infix_groups_in pl a _ targets room)
      exact ⟨Or.inl upper, Or.inl (by dsimp only; omega), trivial⟩
    rw [word, memory, writeLog_append, bytesT_writeLog_out _ outside, writeLog_append]
    exact word_writeLog_at _ _ i address value selected later
  apply closurerec_metadata_read targets small
  · exact firstRead 1 a _ rfl ⟨Or.inl (by dsimp only; omega), trivial⟩ (by omega)
  · exact firstRead 2 (a + 8) _ rfl trivial (by omega)
  · intro j target selected
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    have targetEq : targets[j] = target := (List.getElem?_eq_some_iff.mp selected).2
    rw [← targetEq, memory, writeLog_append]
    exact infix_groups_heap_read pl a _ targets j bound room heapBelow _

end OCaml.Vm.Sim
