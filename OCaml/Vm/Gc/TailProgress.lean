import OCaml.Vm.Gc.ForwardingPrefix

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- Rank component for copying steps of oldify's tail loop: source blocks whose header
has not yet been replaced by the collector's zero forwarding marker.
The heap invariant supplies the finite source list and header separation.
Forward-tag shortcuts need a separate control-progress argument. -/
def tailRemaining (sources : List (BitVec 64)) (c : Config) : Nat :=
  sources.countP (fun source => word c (source - 8#64).toNat != 0)

/-- Strict finite-count progress from pointwise monotonicity and one removed
witness. This concerns the rank only; executions still use the loop kernel. -/
theorem countP_strict {α : Type} {p q : α → Bool} {xs : List α} {a : α}
    (member : a ∈ xs) (before : p a = true) (after : q a = false)
    (mono : ∀ x ∈ xs, q x = true → p x = true) : xs.countP q < xs.countP p := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    have tailMono : ∀ y ∈ xs, q y = true → p y = true := fun y hy => mono y (List.mem_cons_of_mem _ hy)
    rcases List.mem_cons.mp member with same | member
    · subst x
      have bound := List.countP_mono_left tailMono
      simp only [List.countP_cons,before,after,Bool.false_eq_true,ite_false,ite_true] at ⊢
      omega
    · have bound := ih member tailMono
      have top := mono x (List.mem_cons_self ..)
      cases hp : p x <;> cases hq : q x <;>
        simp_all only [List.countP_cons,Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- One real forwarding prefix strictly decreases the tail rank. Preserved
source headers rule out creating new unforwarded objects, including on cycles. -/
theorem SingleField.YoungHead.decreases {q root sp sources before after}
    (head : SingleField.YoungHead q root sp before after)
    (window : WriteWindow q.source 8) (member : q.source ∈ sources)
    (fresh : word before (q.source - 8#64).toNat ≠ 0)
    (outside : ∀ source ∈ sources, source ≠ q.source →
      OutLRange (Enqueue.prefixLog q.source q.target root) (source - 8#64).toNat 8) :
    tailRemaining sources after < tailRemaining sources before := by
  have zero : word after (q.source - 8#64).toNat = 0 :=
    (head.forwarding (pl := ⟨fun _ => none,0,0⟩) window).1
  apply countP_strict (a := q.source) member (by simpa using fresh) (by rw [zero]; decide)
  intro source sourceMember nonzero
  by_cases same : source = q.source
  · subst source
    rw [zero] at nonzero
    contradiction
  · have preserved : word after (source - 8#64).toNat = word before (source - 8#64).toNat := by
      simp only [word,head.memory,bytesT_writeLog_out _ (outside source sourceMember same)]
    simpa only [preserved] using nonzero

end OCaml.Vm.Gc
