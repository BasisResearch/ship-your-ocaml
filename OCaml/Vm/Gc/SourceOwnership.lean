import OCaml.Vm.Gc.CopySources
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.CopyRoots

/-!
# Ownership supplier for `SourceFrame`

`SourceFrame` asks that every copying iteration's stores miss every source
object it leaves unforwarded. This file reduces that to per-store facts:
each store lands outside the nursery, or inside the header or first field of
a source the iteration publishes as forwarded (`Allowed`). With the nursery's
object footprints disjoint (`Nursery`), `Allowed` stores miss every other
source (`outside_of_allowed`). The parent-forwarding prefix is `Allowed`
(`prefix_allowed`), and so is every branch of `CopyStep` (`OwnedFrame.effect`),
given `OwnedFrame`'s address facts: root slot, copy target, queued payload,
both allocator logs and the todo-list global lie outside the nursery.
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

/-- Every store of `log` misses the nursery `[lo, hi)`. -/
def LogOutside (lo hi : Nat) (log : List WEntry) : Prop := ∀ w ∈ log, w.1 + w.2.1 ≤ lo ∨ hi ≤ w.1

/-- Address facts per copying head, finer than `SourceFrame`: the root slot,
the copy target, the queued child's payload, both allocator effect logs and
the todo-list global lie outside the nursery, and every young source is a
recorded object. Each is a fact about one address or one allocator log. -/
structure OwnedFrame (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (lo hi : Nat) (objects : List SourceObjects.Entry) : Prop where
  covers : ∀ src ∈ sources, ∃ e ∈ objects, e.source = src
  rootOutside : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies →
    root.toNat + 8 ≤ lo ∨ hi ≤ root.toNat
  targetOutside : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies →
    q.target.toNat + 8 ≤ lo ∨ hi ≤ q.target.toNat
  exactOutside : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies →
    LogOutside lo hi (AllocWrapper.effect (SingleField.childAllocatorRegs q root sp c) (SingleField.forwardedSnapshot q root c))
  largeOutside : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies →
    LogOutside lo hi (AllocLargeWrapper.effect (SingleField.childAllocatorRegs q root sp c)
      (SingleField.forwardedSnapshot q root c))
  payloadOutside : ∀ copies q root c payload log, Head sp sources pl initial copies q root c → track copies →
    SingleField.QueueAllocation q root sp c payload log →
      (payload.toNat + 16 ≤ lo ∨ hi ≤ payload.toNat) ∧ payload.toNat + 16 ≤ 2 ^ 64
  todoOutside : Layout.sym_oldify_todo_list + 8 ≤ lo ∨ hi ≤ Layout.sym_oldify_todo_list

/-- A recorded source's forwarding stores (header and first field) are allowed
once the source is published. -/
theorem forward_allowed {lo hi : Nat} {objects : List SourceObjects.Entry} {next : List PendingCopy}
    {e : SourceObjects.Entry} (member : e ∈ objects) (published : ∃ p ∈ next, p.source = e.source)
    (low : 8 ≤ e.source.toNat) (v : BitVec 64) :
    Allowed lo hi objects next ((e.source - 8#64).toNat, 8, v) ∧ Allowed lo hi objects next (e.source.toNat, 8, v) := by
  have header : (e.source - 8#64).toNat = e.source.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using low)]
    rfl
  exact ⟨Or.inr ⟨e, member, published, by simp only [header]; omega, by simp only [header]; omega⟩,
    Or.inr ⟨e, member, published, by simp only; omega, by simp only; omega⟩⟩

theorem allowed_of_outside {lo hi : Nat} {objects : List SourceObjects.Entry} {next : List PendingCopy}
    {log : List WEntry} (outside : LogOutside lo hi log) : ∀ w ∈ log, Allowed lo hi objects next w :=
  fun w hw => Or.inl (outside w hw)

/-- Every store of an iteration's effect log is allowed. -/
theorem OwnedFrame.effect {sp sources pl initial track lo hi objects}
    (nursery : Nursery lo hi objects) (owned : OwnedFrame sp sources pl initial track lo hi objects)
    {copies q root c next log} (head : Head sp sources pl initial copies q root c) (tracked : track copies)
    (step : CopyStep sources copies q root sp c next log) : ∀ w ∈ log, Allowed lo hi objects next w := by
  have target := owned.targetOutside copies q root c head tracked
  cases step with
  | ordinary effect =>
    cases effect with
    | plain | forwarded =>
      intro w hw
      simp only [StoreReturn.effect, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact Or.inl target
    | exactSize => exact allowed_of_outside (owned.exactOutside copies q root c head tracked)
    | large => exact allowed_of_outside (owned.largeOutside copies q root c head tracked)
  | queued payload log qs allocation member =>
    have allocated : LogOutside lo hi log := by
      cases allocation with
      | exactSize => exact owned.exactOutside copies q root c head tracked
      | large => exact owned.largeOutside copies q root c head tracked
    obtain ⟨payloadOut, payloadRange⟩ := owned.payloadOutside copies q root c payload log head tracked allocation
    obtain ⟨e, recorded, same⟩ := owned.covers _ member
    have low : 8 ≤ e.source.toNat := by have := (nursery.inside e recorded).1; omega
    have published : ∃ p ∈ (⟨SingleField.child q root c, payload⟩ :: q :: copies : List PendingCopy),
        p.source = e.source := ⟨_, List.mem_cons_self, same.symm⟩
    have second : (payload + 8#64).toNat = payload.toNat + 8 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
      rfl
    have forward := fun v => forward_allowed (lo := lo) (hi := hi) recorded published low v
    simp only [same] at forward
    intro w hw
    rcases List.mem_append.1 hw with inAlloc | inQueue
    · exact Or.inl (allocated w inAlloc)
    · simp only [Fresh.contextQueueEffect, Enqueue.effect, List.mem_cons, List.not_mem_nil, or_false] at inQueue
      rcases inQueue with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl target
      · exact (forward _).1
      · exact (forward _).2
      · exact Or.inl (by simp only; omega)
      · exact Or.inl owned.todoOutside
      · exact Or.inl (by simp only [second]; omega)

/-- **`SourceFrame` from nursery ownership.** -/
theorem OwnedFrame.sourceFrame {sp sources pl initial track lo hi objects}
    (nursery : Nursery lo hi objects) (owned : OwnedFrame sp sources pl initial track lo hi objects) :
    SourceFrame sp sources pl initial track objects where
  outside := by
    intro copies q root c next log head tracked step
    obtain ⟨e, member, same⟩ := owned.covers q.source head.member
    have low : 8 ≤ q.source.toNat := by
      have := (nursery.inside e member).1
      rw [same] at this
      omega
    apply outside_of_allowed nursery
    intro w hw
    rcases List.mem_append.1 hw with prefixed | logged
    · exact prefix_allowed (owned.rootOutside copies q root c head tracked) step.publication.parent_member
        member same low w prefixed
    · exact owned.effect nursery head tracked step w logged

end OCaml.Vm.Gc.SingleTail
