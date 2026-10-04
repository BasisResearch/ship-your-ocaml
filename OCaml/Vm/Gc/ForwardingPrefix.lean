import OCaml.Vm.Gc.SingleFieldYoung

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- A copied source's forwarding header and pointer, independent of whether
its destination is queued, active in a register, or completely scanned. -/
def forwardingEqv (q : PendingCopy) : Eqv :=
  Eqv.and (Eqv.rawW (fun _ => (q.source - 8#64).toNat) (· = 0))
    (Eqv.rawW (fun _ => q.source.toNat) (· = q.target))

/-- The real three-store prefix establishes forwarding for every copy,
including size-one objects that never enter the intrusive work queue. -/
theorem forwarding_prefix {q : PendingCopy} {root} {before after : Config} {pl}
    (memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root))
    (lower : 8 ≤ q.source.toNat) : (forwardingEqv q).P pl 0 after := by
  have separated : (q.source - 8#64).toNat + 8 ≤ q.source.toNat := by bv_omega
  constructor
  · change bytesT after.σ.mem (q.source - 8#64).toNat 8 = 0
    rw [memory]
    apply word_writeLog_at _ _ 1 _ _ rfl
    exact ⟨Or.inl separated,True.intro⟩
  · change bytesT after.σ.mem q.source.toNat 8 = q.target
    rw [memory]
    exact word_writeLog_at _ _ 2 _ _ rfl True.intro

/-- Both forwarding observations hold at the actual young-child tail head. -/
theorem SingleField.YoungHead.forwarding {q root sp before after pl}
    (head : SingleField.YoungHead q root sp before after)
    (window : WriteWindow q.source 8) : (forwardingEqv q).P pl 0 after :=
  forwarding_prefix (q := q) (root := root) (before := before) (after := after) head.memory (by have lower := window.lower; omega)

/-- A captured self-pointer follows the new forwarding pointer. This is
where the old register word is resolved to the new destination address. -/
theorem SingleField.YoungHead.self_forwarding {q root sp before after}
    (head : SingleField.YoungHead q root sp before after)
    (window : WriteWindow q.source 8) (self : SingleField.child q root before = q.source) :
    word after (SingleField.child q root before - 8#64).toNat = 0 ∧
      word after (SingleField.child q root before).toNat = q.target := by
  rw [self]
  exact head.forwarding (pl := ⟨fun _ => none,0,0⟩) window

end OCaml.Vm.Gc
