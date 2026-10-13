import OCaml.Vm.Gc.OldifyImmediate
import OCaml.Vm.Gc.NonYoungCall
import OCaml.Vm.Gc.ForwardingDomain
import OCaml.Vm.Gc.FreshLargeEnqueued
import OCaml.Vm.Gc.FreshSingleNonYoung

/-! # `caml_oldify_one` at the level of a root slot

`caml_oldify_one(v, p)` leaves `*p` holding the image of `v` under the
forwarding table: `v` itself when `v` is no source (immediate, outside the
nursery), the published target when `v` is already forwarded, a fresh copy
otherwise. `SlotDone` states that over the published table
(`ForwardingTable.eqv`, `ForwardingTable.relocation`), which only grows.
The root-slot loops (`ref_table`, VM stack) and mopup compose calls through it. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable Reloc

/-- **One `caml_oldify_one(R 10, R 11)` call at the slot level.** -/
structure SlotDone (R : Nat → BitVec 64) (copies copies' : List PendingCopy) (pl : Place)
    (before after : Config) : Prop where
  returned : ∃ log, OldifyReturned R log before after
  table : (ForwardingTable.eqv copies').P pl 0 after
  grows : ∃ new, copies' = new ++ copies
  root : word after (R 11).toNat = BitVec.ofNat 64 (ForwardingTable.relocation copies' (R 10).toNat)

/-- A call that stores the value itself, for a value that is no source. -/
theorem SlotDone.of_identity {R : Nat → BitVec 64} {copies : List PendingCopy} {pl : Place}
    {log : List WEntry} {before after : Config}
    (returned : OldifyReturned R log before after) (root : word after (R 11).toNat = R 10)
    (view : (ForwardingTable.eqv copies).P pl 0 before) (outside : ForwardingTable.Outside copies log)
    (absent : ∀ q ∈ copies, q.source.toNat ≠ (R 10).toNat) :
    SlotDone R copies copies pl before after where
  returned := ⟨log, returned⟩
  table := ForwardingTable.frame view returned.memory outside
  grows := ⟨[], rfl⟩
  root := by
    rw [ForwardingTable.identity_of_absent absent, root]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- An immediate value. -/
theorem OldifyImmediate.slot {R c copies pl} (input : OldifyImmediate.Input R c)
    (view : (ForwardingTable.eqv copies).P pl 0 c)
    (outside : ForwardingTable.Outside copies (OldifyImmediate.callEffect R))
    (absent : ∀ q ∈ copies, q.source.toNat ≠ (R 10).toNat) :
    FnSummary OldifyEntry.pc (fun d => d = c) (SlotDone R copies copies pl c) :=
  (OldifyImmediate.call input).weaken (fun _ h => h) fun _ post =>
    SlotDone.of_identity post.toOldifyReturned post.root view outside absent

/-- A pointer outside the nursery. -/
theorem NonYoung.slot {R domain c copies pl} (input : NonYoung.Input R domain c)
    (view : (ForwardingTable.eqv copies).P pl 0 c)
    (outside : ForwardingTable.Outside copies (NonYoung.effect R))
    (absent : ∀ q ∈ copies, q.source.toNat ≠ (R 10).toNat) :
    FnSummary OldifyEntry.pc (fun d => d = c) (SlotDone R copies copies pl c) :=
  (NonYoung.call input).weaken (fun _ h => h) fun _ post =>
    SlotDone.of_identity post.toOldifyReturned post.root view outside absent

/-- An already forwarded young value: its published entry gives the target. -/
theorem ForwardedCall.slot {R domain c copies pl} {q : PendingCopy} (input : ForwardedCall.Input R domain c)
    (view : (ForwardingTable.eqv copies).P pl 0 c) (member : q ∈ copies) (source : q.source = R 10)
    (outside : ForwardingTable.Outside copies (ForwardedCall.effect R c)) :
    FnSummary OldifyEntry.pc (fun d => d = c) (SlotDone R copies copies pl c) :=
  (ForwardedCall.forwarded_call input).weaken (fun _ h => h) fun after post => by
    have target : word c (R 10).toNat = q.target := source ▸ (view q member).2
    refine ⟨⟨_, post.returned⟩, ForwardingTable.frame view post.memory outside, ⟨[], rfl⟩, ?_⟩
    rw [post.root, target, ← source, ForwardingTable.relocation_member view member]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

namespace Fresh

/-- **A fresh single-field block**: the forwarding entry `queuePending R target`
is published, the child stored into the copy, and the root holds the target. -/
theorem SingleResult.slot {R : Nat → BitVec 64} {target : BitVec 64} {log : List WEntry}
    {pl : Place} {copies : List PendingCopy} {before after : Config}
    (post : SingleResult R target log before after)
    (view : (ForwardingTable.eqv copies).P pl 0 before)
    (allocOutside : ForwardingTable.Outside copies (OldifyEntry.saveLog OldifyEntry.saves R ++ log))
    (prefixOutside : ForwardingTable.Outside copies (Enqueue.prefixLog (R 10) target (R 11)))
    (childOutside : ForwardingTable.Outside (queuePending R target :: copies)
      (StoreReturn.effect (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log before)) target))
    (window : WriteWindow (R 10) 8)
    (rootOutside : OutLRange ((Enqueue.prefixLog (R 10) target (R 11)).drop 1 ++
      StoreReturn.effect (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log before)) target)
      (R 11).toNat 8) :
    SlotDone R copies (queuePending R target :: copies) pl before after where
  returned := ⟨_, post.returned⟩
  table := by
    have snapshot : (queueSnapshot R log before).σ.mem =
        writeLog before.σ.mem (OldifyEntry.saveLog OldifyEntry.saves R ++ log) := by
      simp only [queueSnapshot]
    have allocated := ForwardingTable.frame (after := queueSnapshot R log before) view snapshot allocOutside
    apply ForwardingTable.publish_then (q := queuePending R target) allocated ?_ window prefixOutside childOutside
    rw [post.memory, writeLog_append, snapshot]
    rfl
  grows := ⟨[queuePending R target], rfl⟩
  root := by
    have stored : word after (R 11).toNat = target := by
      rw [word, post.memory, writeLog_append, singleEffect, SingleField.effect]
      exact word_writeLog_at _ _ 0 _ _ rfl rootOutside
    rw [stored]
    show target = BitVec.ofNat 64
      (ForwardingTable.relocation (queuePending R target :: copies) (queuePending R target).source.toNat)
    rw [ForwardingTable.relocation_head]
    simp only [queuePending, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The common return of a queue-inserting allocator route. -/
theorem QueueResult.returned {R : Nat → BitVec 64} {target : BitVec 64} {log : List WEntry}
    {qs : List PendingCopy} {pl : Place} {before after : Config}
    (p : QueueResult R target log qs pl before after) :
    OldifyReturned R ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++ queueEffect R target log qs before)
      before after :=
  ⟨p.good, p.minstret, p.tick, p.code, p.pc, p.registers, p.memory, p.output,
    OldifyReturned.frame_of (by decide) p.native⟩

/-- The queue stores after the forwarding prefix. -/
def queueLinkLog (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry) (qs : List PendingCopy)
    (c : Config) : List WEntry :=
  (queueEffect R target log qs c).drop 3

theorem queueEffect_split (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry)
    (qs : List PendingCopy) (c : Config) :
    queueEffect R target log qs c = Enqueue.prefixLog (R 10) target (R 11) ++ queueLinkLog R target log qs c := rfl

/-- **A fresh block through any queue-inserting allocator route** (exact-size
or least-large-block): the entry `queuePending R target` is published. -/
theorem QueueResult.slot {R : Nat → BitVec 64} {target : BitVec 64} {log : List WEntry}
    {qs : List PendingCopy} {pl : Place} {copies : List PendingCopy} {before after : Config}
    (post : QueueResult R target log qs pl before after)
    (view : (ForwardingTable.eqv copies).P pl 0 before)
    (allocOutside : ForwardingTable.Outside copies (OldifyEntry.saveLog OldifyEntry.saves R ++ log))
    (prefixOutside : ForwardingTable.Outside copies (Enqueue.prefixLog (R 10) target (R 11)))
    (linkOutside : ForwardingTable.Outside (queuePending R target :: copies) (queueLinkLog R target log qs before))
    (window : WriteWindow (R 10) 8) :
    SlotDone R copies (queuePending R target :: copies) pl before after where
  returned := ⟨_, post.returned⟩
  table := by
    have snapshot : (queueSnapshot R log before).σ.mem =
        writeLog before.σ.mem (OldifyEntry.saveLog OldifyEntry.saves R ++ log) := by
      simp only [queueSnapshot]
    have allocated := ForwardingTable.frame (after := queueSnapshot R log before) view snapshot allocOutside
    apply ForwardingTable.publish_then (q := queuePending R target) allocated ?_ window prefixOutside linkOutside
    rw [post.memory, writeLog_append, snapshot]
    exact congrArg _ (queueEffect_split R target log qs before)
  grows := ⟨[queuePending R target], rfl⟩
  root := by
    rw [post.data.root]
    show (queuePending R target).target = BitVec.ofNat 64
      (ForwardingTable.relocation (queuePending R target :: copies) (queuePending R target).source.toNat)
    rw [ForwardingTable.relocation_head]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **A fresh block through the exact-size allocator**, via `QueueResult`. -/
theorem Enqueued.slot {R : Nat → BitVec 64} {qs : List PendingCopy} {pl : Place}
    {copies : List PendingCopy} {before after : Config}
    (post : Enqueued R qs pl before after)
    (view : (ForwardingTable.eqv copies).P pl 0 before)
    (allocOutside : ForwardingTable.Outside copies (allocationEffect R before))
    (prefixOutside : ForwardingTable.Outside copies
      (Enqueue.prefixLog (R 10) (allocatedPayload R before) (R 11)))
    (linkOutside : ForwardingTable.Outside (pending R before :: copies)
      (queueLinkLog R (allocatedPayload R before)
        (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) qs before))
    (window : WriteWindow (R 10) 8) :
    SlotDone R copies (pending R before :: copies) pl before after :=
  post.toQueue.slot view allocOutside prefixOutside linkOutside window

end Fresh

/-- **A `caml_oldify_one(R 10, R 11)` call at `c` with a slot-level result**:
the route dispatcher's interface. Each proved route supplies it from its own
input; the root-slot loops consume one per slot. -/
def SlotCall (R : Nat → BitVec 64) (copies : List PendingCopy) (pl : Place) (c : Config) : Prop :=
  ∃ copies', FnSummary OldifyEntry.pc (fun d => d = c) (SlotDone R copies copies' pl c)

theorem SlotCall.immediate {R c copies pl} (input : OldifyImmediate.Input R c)
    (view : (ForwardingTable.eqv copies).P pl 0 c)
    (outside : ForwardingTable.Outside copies (OldifyImmediate.callEffect R))
    (absent : ∀ q ∈ copies, q.source.toNat ≠ (R 10).toNat) : SlotCall R copies pl c :=
  ⟨_, OldifyImmediate.slot input view outside absent⟩

theorem SlotCall.nonYoung {R domain c copies pl} (input : NonYoung.Input R domain c)
    (view : (ForwardingTable.eqv copies).P pl 0 c)
    (outside : ForwardingTable.Outside copies (NonYoung.effect R))
    (absent : ∀ q ∈ copies, q.source.toNat ≠ (R 10).toNat) : SlotCall R copies pl c :=
  ⟨_, NonYoung.slot input view outside absent⟩

theorem SlotCall.forwarded {R domain c copies pl} {q : PendingCopy} (input : ForwardedCall.Input R domain c)
    (view : (ForwardingTable.eqv copies).P pl 0 c) (member : q ∈ copies) (source : q.source = R 10)
    (outside : ForwardingTable.Outside copies (ForwardedCall.effect R c)) : SlotCall R copies pl c :=
  ⟨_, ForwardedCall.slot input view member source outside⟩

namespace Fresh

/-- Table premises of a fresh queue-inserting call at `c`. -/
structure QueueTable (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry) (qs copies : List PendingCopy)
    (pl : Place) (c : Config) : Prop where
  view : (ForwardingTable.eqv copies).P pl 0 c
  allocOutside : ForwardingTable.Outside copies (OldifyEntry.saveLog OldifyEntry.saves R ++ log)
  prefixOutside : ForwardingTable.Outside copies (Enqueue.prefixLog (R 10) target (R 11))
  linkOutside : ForwardingTable.Outside (queuePending R target :: copies) (queueLinkLog R target log qs c)
  window : WriteWindow (R 10) 8

theorem SlotCall.queue_small {R domain size tag c qs pl copies} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c) (conditions : EnqueueConditions R qs pl c)
    (table : QueueTable R (allocatedPayload R c)
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) qs copies pl c) :
    SlotCall R copies pl c :=
  ⟨_, (enqueue_fresh input allocation conditions).weaken (fun _ h => h) fun _ post =>
    post.toQueue.slot table.view table.allocOutside table.prefixOutside table.linkOutside table.window⟩

theorem SlotCall.queue_large {R domain size tag c qs pl copies} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c) (conditions : LargeEnqueueConditions R qs pl c)
    (table : QueueTable R (largePayload R c)
      (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) qs copies pl c) :
    SlotCall R copies pl c :=
  ⟨_, (enqueue_fresh_large input allocation conditions).weaken (fun _ h => h) fun _ post =>
    QueueResult.slot post table.view table.allocOutside table.prefixOutside table.linkOutside table.window⟩

/-- Table premises of a fresh single-field call at `c`. -/
structure SingleTable (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry) (copies : List PendingCopy)
    (pl : Place) (c : Config) : Prop where
  view : (ForwardingTable.eqv copies).P pl 0 c
  allocOutside : ForwardingTable.Outside copies (OldifyEntry.saveLog OldifyEntry.saves R ++ log)
  prefixOutside : ForwardingTable.Outside copies (Enqueue.prefixLog (R 10) target (R 11))
  childOutside : ForwardingTable.Outside (queuePending R target :: copies)
    (StoreReturn.effect (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c)) target)
  window : WriteWindow (R 10) 8
  rootOutside : OutLRange ((Enqueue.prefixLog (R 10) target (R 11)).drop 1 ++
    StoreReturn.effect (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c)) target)
    (R 11).toNat 8

theorem SingleTable.slot {R target log copies pl before after} (table : SingleTable R target log copies pl before)
    (post : SingleResult R target log before after) :
    SlotDone R copies (queuePending R target :: copies) pl before after :=
  post.slot table.view table.allocOutside table.prefixOutside table.childOutside table.window table.rootOutside

theorem SlotCall.single_small {R domain size tag c pl copies} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c)
    (conditions : SingleConditions R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c)
    (table : SingleTable R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) copies pl c) :
    SlotCall R copies pl c :=
  ⟨_, (single_fresh input allocation conditions).weaken (fun _ h => h) fun _ post => table.slot post⟩

theorem SlotCall.single_large {R domain size tag c pl copies} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c)
    (conditions : SingleConditions R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c)
    (table : SingleTable R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) copies pl c) :
    SlotCall R copies pl c :=
  ⟨_, (single_fresh_large input allocation conditions).weaken (fun _ h => h) fun _ post => table.slot post⟩

theorem SlotCall.single_nonYoung_small {R domain size tag childDomain c pl copies} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c)
    (conditions : NonYoungSingleConditions R (allocatedPayload R c) childDomain
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c)
    (table : SingleTable R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) copies pl c) :
    SlotCall R copies pl c :=
  ⟨_, (single_fresh_nonYoung input allocation conditions).weaken (fun _ h => h) fun _ post => table.slot post⟩

theorem SlotCall.single_nonYoung_large {R domain size tag childDomain c pl copies} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c)
    (conditions : NonYoungSingleConditions R (largePayload R c) childDomain
      (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c)
    (table : SingleTable R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) copies pl c) :
    SlotCall R copies pl c :=
  ⟨_, (single_fresh_large_nonYoung input allocation conditions).weaken (fun _ h => h) fun _ post => table.slot post⟩

end Fresh

end OCaml.Vm.Gc
