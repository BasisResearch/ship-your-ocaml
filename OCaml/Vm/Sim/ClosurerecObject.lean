import OCaml.Vm.Sim.ClosureRestore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- One function's header (except function zero), code and environment offset. -/
def closurerecFunctionGroup (functions dest k : Nat) : List Val :=
  (if k = 0 then [] else [Val.raw (BitVec.ofNat 64 ((3 * k) * 1024 + infixTag))]) ++
    [Val.code dest, Val.ofInt (Int.ofNat (3 * functions - 1) - 3 * Int.ofNat k)]

/-- Metadata fields in the recursive-closure object, in bytecode-model order. -/
def closurerecFunctionValues (targets : List Nat) : List Val :=
  (targets.zipIdx.map fun (dest, k) => closurerecFunctionGroup targets.length dest k).flatten

def closurerecObject (s : St) (count : Nat) (targets : List Nat) : Obj :=
  .block closureTag (closurerecFunctionValues targets ++ closureCaptures s count)

/-- Code, arity and raw infix-header fields have no heap locations. -/
theorem closurerec_metadata_no_roots {targets : List Nat} {v : Val}
    (member : v ∈ closurerecFunctionValues targets) : v.loc? = none := by
  obtain ⟨group, member, selected⟩ := List.mem_flatten.mp member
  obtain ⟨⟨dest, k⟩, _, rfl⟩ := List.mem_map.mp member
  dsimp only [closurerecFunctionGroup] at selected
  by_cases zero : k = 0
  · simp only [zero, ite_true, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at selected
    rcases selected with rfl | rfl <;> rfl
  · simp only [zero, ite_false, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at selected
    rcases selected with rfl | rfl | rfl <;> rfl

/-- Recursive closures capture only old roots; their infix headers are raw words. -/
theorem closurerec_allocation_roots {P : Prog} {s : St} {count : Nat} {targets : List Nat} :
    AllocationRoots P s (closurerecObject s count targets) := by
  apply block_allocation_roots
  intro v member l loc
  rcases List.mem_append.mp member with metadata | capture
  · rw [closurerec_metadata_no_roots metadata] at loc
    cases loc
  · exact closure_allocation_roots (P := P) (s := s) (count := count) (dest := 0)
      closureTag _ rfl v (List.mem_append_right _ capture) l loc

/-- The last recursive function is pushed last and becomes the stack head. -/
def closurerecStack (s : St) (count functions fresh : Nat) : List Val :=
  ((List.range functions).drop 1).reverse.map (fun k => Val.ptr fresh (3 * k)) ++
    (Val.ptr fresh 0 :: s.stack.drop (count - 1))

theorem closurerec_stack_roots {P : Prog} {s : St} {count functions : Nat} {o : Obj} :
    ∀ v ∈ closurerecStack s count functions (s.heap.alloc o).2, ∀ l, v.loc? = some l →
      Live (s.heap.alloc o).1
        (roots P {s with heap := (s.heap.alloc o).1, accu := .ptr (s.heap.alloc o).2 0}) l := by
  intro v member l loc
  rcases List.mem_append.mp member with ptr | tail
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp ptr
    have eq : (s.heap.alloc o).2 = l := Option.some.inj loc
    subst l
    exact Live.root (v := .ptr (s.heap.alloc o).2 0) (by simp [roots]) rfl
  · rcases List.mem_cons.mp tail with rfl | old
    · exact Live.root (by simp [roots]) loc
    · exact Live.root (by simp [roots, List.mem_of_mem_drop old]) loc

/-- The first function uses two fields; each remaining function uses three. -/
theorem closurerec_function_values_length (dest : Nat) (targets : List Nat) :
    (closurerecFunctionValues (dest :: targets)).length = 3 * (targets.length + 1) - 1 := by
  let group := fun (p : Nat × Nat) => closurerecFunctionGroup (targets.length + 1) p.1 p.2
  have lengths : ((targets.zipIdx 1).map group).map List.length =
      List.replicate (targets.zipIdx 1).length 3 := by
    rw [List.map_map]
    apply List.map_eq_replicate_iff.mpr
    intro p member
    have lower := List.le_snd_of_mem_zipIdx member
    have nonzero : p.2 ≠ 0 := by omega
    simp [group, closurerecFunctionGroup, nonzero]
  have tailLength : ((targets.zipIdx 1).map group).flatten.length = targets.length * 3 := by
    rw [List.length_flatten, lengths, List.sum_replicate_nat, List.length_zipIdx]
  change ((group (dest, 0)) ++ ((targets.zipIdx 1).map group).flatten).length = _
  rw [List.length_append, tailLength]
  simp only [group, closurerecFunctionGroup, ↓reduceIte, List.nil_append, List.length_cons, List.length_nil]
  omega

end OCaml.Vm.Sim
