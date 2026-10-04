import OCaml.Vm.Sim.ClosurerecInfixLog
import OCaml.Vm.Sim.GroupedRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Local readback of an infix iteration's three adjacent heap words.
Only the intervening stack store needs a heap-separation certificate. -/
structure InfixHeapWords (memory : Std.ExtHashMap Nat (BitVec 8))
    (pl : Place) (a functions index dest : Nat) : Prop where
  header : bytesT memory (a + 24 * index - 8) 8 = blockHeader (3 * index) infixTag
  code : bytesT memory (a + 24 * index) 8 = BitVec.ofNat 64 (pl.codeBase + 4 * dest)
  arity : bytesT memory (a + 24 * index + 8) 8 = infixArityWord functions index

theorem infix_stores_read {pl : Place} {a stackStart functions index dest : Nat}
    (positive : 0 < index)
    (stackOutside : a + 24 * index ≤ stackStart - 8 * index ∨
      stackStart - 8 * index + 8 ≤ a + 24 * index - 8)
    (memory : Std.ExtHashMap Nat (BitVec 8)) :
    InfixHeapWords (writeLog memory (infixStores pl a stackStart functions index dest))
      pl a functions index dest := by
  constructor
  · apply word_writeLog_at _ _ 0 _ _ rfl
    exact ⟨by dsimp only; omega, Or.inl (by omega), Or.inl (by omega), trivial⟩
  · exact word_writeLog_at _ _ 3 _ _ rfl trivial
  · apply word_writeLog_at _ _ 2 _ _ rfl
    exact ⟨Or.inr (by dsimp only; omega), trivial⟩

/-- Every iteration writes three adjacent heap words and one descending
stack slot. This footprint supplies separation for all later readbacks. -/
theorem infix_stores_in (pl : Place) (a stackStart functions index dest : Nat)
    (positive : 0 < index) :
    LogInW [⟨a + 24 * index - 8, a + 24 * index + 16⟩,
            ⟨stackStart - 8 * index, stackStart - 8 * index + 8⟩]
      (infixStores pl a stackStart functions index dest) := by
  exact ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
    Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩),
    Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
    Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, trivial⟩

/-- Every function's metadata reads back after the complete infix loop.
The nursery metadata lies below all descending stack slots. -/
theorem infix_groups_heap_read (pl : Place) (a stackStart : Nat) (targets : List Nat)
    (i : Nat) (bound : i < targets.length)
    (room : 8 * targets.length ≤ stackStart)
    (heapBelow : a + 24 * targets.length + 16 ≤ stackStart - 8 * targets.length)
    (memory : Std.ExtHashMap Nat (BitVec 8)) :
    InfixHeapWords (writeLog memory (infixGroups pl a stackStart targets).flatten)
      pl a (targets.length + 1) (i + 1) targets[i] := by
  have read (address : Nat) (value : BitVec 64)
      (upper : address + 8 ≤ a + 24 * (i + 1) + 16)
      (localRead : ∀ m : Std.ExtHashMap Nat (BitVec 8),
        bytesT (writeLog m (infixStores pl a stackStart (targets.length + 1) (i + 1) targets[i]))
          address 8 = value) :
      bytesT (writeLog memory (infixGroups pl a stackStart targets).flatten) address 8 = value := by
    apply grouped_log_read _ i address value (by rw [infix_groups_length]; exact bound)
    · intro m
      rw [infix_group_at pl a stackStart targets i bound]
      exact localRead m
    · apply grouped_suffix_outside
      intro j hj later
      have jb : j < targets.length := by simpa only [infix_groups_length] using hj
      rw [infix_group_at pl a stackStart targets j jb]
      apply outLRange_of_windows (infix_stores_in pl a stackStart _ (j + 1) targets[j] (by omega))
      exact ⟨Or.inl (by dsimp only; omega), Or.inl (by dsimp only; omega), trivial⟩
  have localRead := fun m => infix_stores_read (pl := pl) (a := a) (stackStart := stackStart)
    (functions := targets.length + 1) (index := i + 1) (dest := targets[i]) (by omega)
    (Or.inl (by omega)) m
  exact ⟨read _ _ (by omega) (fun m => (localRead m).header),
    read _ _ (by omega) (fun m => (localRead m).code),
    read _ _ (by omega) (fun m => (localRead m).arity)⟩

/-- Each pushed interior pointer remains in its stack slot after all later
iterations. This is the stack counterpart of the shared grouped readback. -/
theorem infix_groups_stack_read (pl : Place) (a stackStart : Nat) (targets : List Nat)
    (i : Nat) (bound : i < targets.length)
    (room : 8 * targets.length ≤ stackStart)
    (heapBelow : a + 24 * targets.length + 16 ≤ stackStart - 8 * targets.length)
    (memory : Std.ExtHashMap Nat (BitVec 8)) :
    bytesT (writeLog memory (infixGroups pl a stackStart targets).flatten)
      (stackStart - 8 * (i + 1)) 8 = BitVec.ofNat 64 (a + 24 * (i + 1)) := by
  apply grouped_log_read _ i _ _ (by rw [infix_groups_length]; exact bound)
  · intro m
    rw [infix_group_at pl a stackStart targets i bound]
    apply word_writeLog_at _ _ 1 _ _ rfl
    exact ⟨Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), trivial⟩
  · apply grouped_suffix_outside
    intro j hj later
    have jb : j < targets.length := by simpa only [infix_groups_length] using hj
    rw [infix_group_at pl a stackStart targets j jb]
    apply outLRange_of_windows (infix_stores_in pl a stackStart _ (j + 1) targets[j] (by omega))
    exact ⟨Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), trivial⟩

end OCaml.Vm.Sim
