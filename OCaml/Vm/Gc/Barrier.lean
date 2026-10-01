import OCaml.Vm.Gc.Invariant

/-! The remembered-set argument shared by writing arms.
This is the logical store rule, not execution of caml_modify. Its machine
summary must supply the field update, table frame, and insertion branch.
The old-young fast return is justified by PRE-state completeness, exactly
as in runtime/memory.c:caml_modify. No ELF addresses occur in this rule. -/
namespace OCaml.Vm.Gc

/-- Completeness on a fixed set of old scanned slots. Using all old slots
avoids requiring a separate reachability argument when a store adds edges. -/
def SlotComplete (lo hi : Nat) (oldSlot : Nat → Prop)
    (read : Nat → BitVec 64) (refs : List Nat) : Prop :=
  ∀ a, oldSlot a → YoungWord lo hi (read a) → a ∈ refs

/-- The concrete caml_modify summary must establish these observations.
Inserting a new young value needs no table write when the overwritten value
was already young: pre-state SlotComplete covers that early-return branch.
The frame covers old scanned slots only: table storage and major headers
may change. Major-GC darkening has its own obligation and is not proved here. -/
structure BarrierEffect (lo hi : Nat) (oldSlot : Nat → Prop)
    (before after : Nat → BitVec 64) (refs refs' : List Nat)
    (slot : Nat) (value : BitVec 64) : Prop where
  write : ∀ a, oldSlot a → after a = if a = slot then value else before a
  retain : ∀ a, a ∈ refs → a ∈ refs'
  insert : oldSlot slot → YoungWord lo hi value →
    ¬ YoungWord lo hi (before slot) → slot ∈ refs'

/-- The old-young early return and the insertion branch both preserve
remembered completeness. This rule is independent of the placement/image. -/
theorem slotComplete_store {lo hi oldSlot before after refs refs' slot value}
    (complete : SlotComplete lo hi oldSlot before refs)
    (effect : BarrierEffect lo hi oldSlot before after refs refs' slot value) :
    SlotComplete lo hi oldSlot after refs' := by
  intro a ha hy
  by_cases same : a = slot
  · subst a
    rw [effect.write slot ha, if_pos rfl] at hy
    by_cases wasYoung : YoungWord lo hi (before slot)
    · exact effect.retain slot (complete slot ha wasYoung)
    · exact effect.insert ha hy wasYoung
  · rw [effect.write a ha, if_neg same] at hy
    exact effect.retain a (complete a ha hy)

/-- A strong concrete slot invariant supplies the typed live-heap interface.
The representation/arm proof supplies the slot coverage and encoding facts. -/
theorem rememberedComplete_of_slots {P s pl lo hi refs oldSlot read}
    (complete : SlotComplete lo hi oldSlot read refs)
    (slots : ∀ l a t fs i v, Live s.heap (roots P s) l → pl.φ l = some a →
      s.heap.get? l = some (.block t fs) → t < 251 →
      ¬ YoungWord lo hi (BitVec.ofNat 64 a) → fs[i]? = some v →
      oldSlot (a + 8 * i))
    (encoded : ∀ l a t fs i v w, Live s.heap (roots P s) l → pl.φ l = some a →
      s.heap.get? l = some (.block t fs) → fs[i]? = some v →
      valWord pl v = some w → read (a + 8 * i) = w) :
    RememberedComplete P s pl lo hi refs := by
  intro l a t fs i v w hl ha ho ht hy hv hw hwYoung
  apply complete (a + 8 * i) (slots l a t fs i v hl ha ho ht hy hv)
  rw [encoded l a t fs i v w hl ha ho hv hw]
  exact hwYoung

end OCaml.Vm.Gc
