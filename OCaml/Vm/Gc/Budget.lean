import OCaml.Refinement

/-! The candidate G2 budget, kept distinct from Fits until collector and
major-heap reclamation proofs justify replacing the allocation budget. -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode Classical

/-- Sum header+payload words for the live locations in a finite heap list.
The original heap is fixed during this fold; `start` is the list index. -/
noncomputable def liveWordsFrom (heap : Heap) (rs : List Val) (start : Nat) : List Obj → Nat
  | [] => 0
  | o :: os => (if Live heap rs start then o.wosize + 1 else 0) +
      liveWordsFrom heap rs (start + 1) os

noncomputable def liveWords (P : Prog) (s : St) : Nat :=
  liveWordsFrom s.heap (roots P s) 0 s.heap.objs

/-- Proposed budget, not yet the production refinement precondition.
Finite live size alone does not prove that the major allocator can provide
space: its reclamation and fragmentation obligations also remain open. -/
def FitsLive (B : Budget) (P : Prog) : Prop :=
  ∀ s, Reach P s → s.stack.length ≤ B.stackWords ∧ liveWords P s ≤ B.heapWords

/-- The live subset never counts more than all allocated objects. -/
theorem liveWordsFrom_le (heap : Heap) (rs : List Val) (os : List Obj) :
    ∀ start acc, acc + liveWordsFrom heap rs start os ≤
      os.foldl (fun a o => a + o.wosize + 1) acc := by
  induction os with
  | nil => intro start acc; simp [liveWordsFrom]
  | cons o os ih =>
    intro start acc
    simp only [liveWordsFrom, List.foldl_cons]
    have next := ih (start + 1) (acc + o.wosize + 1)
    split <;> omega

theorem liveWords_le_allocated (P : Prog) (s : St) : liveWords P s ≤ s.heap.words := by
  simpa only [liveWords, Heap.words, Nat.zero_add] using liveWordsFrom_le s.heap (roots P s) s.heap.objs 0 0

/-- The existing G1 precondition implies the candidate G2 resource bound;
this implication does not discharge any collector execution obligation. -/
theorem fitsLive_of_fits {B : Budget} {P : Prog} (h : Fits B P) : FitsLive B P :=
  fun s hs => ⟨(h s hs).1, Nat.le_trans (liveWords_le_allocated P s) (h s hs).2⟩

end OCaml.Vm.Gc
