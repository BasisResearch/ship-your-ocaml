import OCaml.Vm.Gc.CopySources
import OCaml.Vm.Gc.Readback

/-!
# Ownership supplier for `SourceFrame`

`SourceFrame` asks that every copying iteration's stores miss every source
object it leaves unforwarded. This file reduces that to per-store facts:
each store lands outside the nursery, or inside the header or first field of
a source the iteration publishes as forwarded (`Allowed`). With the nursery's
object footprints disjoint (`Nursery`), `Allowed` stores miss every other
source (`outside_of_allowed`). The parent-forwarding prefix is `Allowed` once
its root slot is outside the nursery (`prefix_allowed`); what remains is the
per-iteration effect log (`OwnedFrame.effect`).
-/

namespace OCaml.Vm.Gc.SingleTail
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives

/-- The young sources lie in the nursery `[lo, hi)`, each with at least one
field, and distinct sources' footprints (header through last field) are disjoint. -/
structure Nursery (lo hi : Nat) (objects : List SourceObjects.Entry) : Prop where
  inside : ∀ e ∈ objects, lo + 8 ≤ e.source.toNat ∧ e.source.toNat + 8 * e.object.wosize ≤ hi
  field : ∀ e ∈ objects, 1 ≤ e.object.wosize
  disjoint : ∀ e ∈ objects, ∀ e' ∈ objects, e.source ≠ e'.source →
    e.source.toNat + 8 * e.object.wosize + 8 ≤ e'.source.toNat ∨
      e'.source.toNat + 8 * e'.object.wosize + 8 ≤ e.source.toNat

/-- A store the copying loop may make: outside the nursery, or within the
header and first field of a source published in `next`. -/
def Allowed (lo hi : Nat) (objects : List SourceObjects.Entry) (next : List PendingCopy) (w : WEntry) : Prop :=
  (w.1 + w.2.1 ≤ lo ∨ hi ≤ w.1) ∨
    ∃ e ∈ objects, (∃ p ∈ next, p.source = e.source) ∧
      e.source.toNat ≤ w.1 + 8 ∧ w.1 + w.2.1 ≤ e.source.toNat + 8

/-- Allowed stores miss every source left unforwarded by `next`. -/
theorem outside_of_allowed {lo hi : Nat} {objects : List SourceObjects.Entry} {next : List PendingCopy}
    {log : List WEntry} (nursery : Nursery lo hi objects) (allowed : ∀ w ∈ log, Allowed lo hi objects next w) :
    SourceObjects.Outside objects next log := by
  intro entry member unforwarded
  have inside := nursery.inside entry member
  have miss : ∀ w ∈ log, entry.source.toNat + 8 * entry.object.wosize ≤ w.1 ∨ w.1 + w.2.1 ≤ entry.source.toNat - 8 := by
    intro w hw
    rcases allowed w hw with outside | ⟨e', member', ⟨p, published, same⟩, low, high⟩
    · omega
    · have different : entry.source ≠ e'.source := fun equal => unforwarded p published (same.trans equal.symm)
      have field := nursery.field e' member'
      rcases nursery.disjoint entry member e' member' different with before | after <;> omega
  constructor
  · exact outLRange_of_forall fun w hw => by rcases miss w hw with h | h <;> omega
  · exact outLRange_of_forall fun w hw => by rcases miss w hw with h | h <;> omega

/-- Both publications place the iteration's own pending copy in the table. -/
theorem Publication.mem_self {sources copies q child next}
    (publication : Publication sources copies q child next) : q ∈ next := by
  cases publication with
  | parent => exact List.mem_cons_self
  | queued => exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The parent-forwarding prefix (root slot, source header, first field) is
allowed once the root slot lies outside the nursery. -/
theorem prefix_allowed {lo hi : Nat} {objects : List SourceObjects.Entry} {next : List PendingCopy}
    {q : PendingCopy} {root : BitVec 64} (rootOutside : root.toNat + 8 ≤ lo ∨ hi ≤ root.toNat)
    (published : q ∈ next) {e : SourceObjects.Entry} (member : e ∈ objects) (same : e.source = q.source)
    (low : 8 ≤ q.source.toNat) :
    ∀ w ∈ Enqueue.prefixLog q.source q.target root, Allowed lo hi objects next w := by
  have header : (q.source - 8#64).toNat = q.source.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using low)]
    rfl
  have forwarded : ∃ p ∈ next, p.source = e.source := ⟨q, published, same.symm⟩
  intro w hw
  simp only [Enqueue.prefixLog, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inl rootOutside
  · exact Or.inr ⟨e, member, forwarded, by simp only [header, same]; omega, by simp only [header, same]; omega⟩
  · exact Or.inr ⟨e, member, forwarded, by simp only [same]; omega, by simp only [same]; omega⟩

/-- Ownership facts per copying head, finer than `SourceFrame`: the root slot
is outside the nursery, the copied source is a recorded young object, and
each iteration's effect log makes only `Allowed` stores. -/
structure OwnedFrame (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (lo hi : Nat) (objects : List SourceObjects.Entry) : Prop where
  rootOutside : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies →
    root.toNat + 8 ≤ lo ∨ hi ≤ root.toNat
  recorded : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies →
    ∃ e ∈ objects, e.source = q.source
  effect : ∀ copies q root c next log, Head sp sources pl initial copies q root c → track copies →
    Publication sources copies q (SingleField.child q root c) next → CopyEffect q root sp c log →
    ∀ w ∈ log, Allowed lo hi objects next w

/-- **`SourceFrame` from nursery ownership.** -/
theorem OwnedFrame.sourceFrame {sp sources pl initial track lo hi objects}
    (nursery : Nursery lo hi objects) (owned : OwnedFrame sp sources pl initial track lo hi objects) :
    SourceFrame sp sources pl initial track objects where
  outside := by
    intro copies q root c next log head tracked publication effect
    obtain ⟨e, member, same⟩ := owned.recorded copies q root c head tracked
    have low : 8 ≤ q.source.toNat := by
      have := (nursery.inside e member).1
      rw [same] at this
      omega
    apply outside_of_allowed nursery
    intro w hw
    rcases List.mem_append.1 hw with prefixed | logged
    · exact prefix_allowed (owned.rootOutside copies q root c head tracked) publication.mem_self member same low
        w prefixed
    · exact owned.effect copies q root c next log head tracked publication effect w logged

end OCaml.Vm.Gc.SingleTail
