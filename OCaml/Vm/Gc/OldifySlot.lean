import OCaml.Vm.Gc.OldifyImmediate
import OCaml.Vm.Gc.NonYoungCall
import OCaml.Vm.Gc.ForwardingDomain

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

end OCaml.Vm.Gc
