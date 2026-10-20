import OCaml.Vm.Gc.RootLoops
import OCaml.Vm.Gc.RefScan

/-! # The remembered-set loop from the collection in progress

`RefScan.ScanStep` from `SlotSupply`, as `RootLoops.Stack.scanStep`: the
entries `p, p + 8, …` below the table's end `limit` hold root slots; the
entries themselves and the bound test's three words (`Caml_state`, the
domain's `ref_table`, its `ptr`) lie outside the calls' writes, the callee's
frame and every root slot. -/
namespace OCaml.Vm.Gc.RefLoops
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable RefScan
open RootLoops (CallRoom textEnd frame_high slot_high byte_one)
open StackScan (statePtr headRegs)

/-- `q` is one of the entries `p, p + 8, …` below `limit`. -/
def Slot (p limit : BitVec 64) (q : Nat) : Prop := p.toNat ≤ q ∧ q + 8 ≤ limit.toNat ∧ (q - p.toNat) % 8 = 0

def word8 (x : Nat) (a : Nat) : Prop := x ≤ a ∧ a < x + 8

/-- The words the loop reads besides the slots. -/
def Watched (m : Std.ExtHashMap Nat (BitVec 8)) (p limit : BitVec 64) (a : Nat) : Prop :=
  word8 Layout.sym_Caml_state a ∨ word8 (bytesT m Layout.sym_Caml_state 8 + 104#64).toNat a ∨
  word8 (refTable m + 24#64).toNat a ∨ ∃ q, Slot p limit q ∧ word8 q a

/-- **The remembered-set loop's invariant** at entry `p`. -/
structure Inv (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) (writes : Nat → Prop)
    (Extra : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (R : Nat → BitVec 64) (limit p : BitVec 64) (copies : List PendingCopy) (c : Config) : Prop where
  head : HeadInput R p c
  extra : Extra c.σ.mem
  room : p.toNat + 8 ≤ limit.toNat
  aligned : (limit.toNat - p.toNat) % 8 = 0
  ready : Ready copies c.σ.mem
  ptrWord : tablePtr c.σ.mem = limit
  roots : ∀ q, Slot p limit q → Root c.σ.mem (entry c.σ.mem (BitVec.ofNat 64 q)).toNat
  frameWindows : ∀ x ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 x.2) 8
  entries : ∀ q, Slot p limit q → ReadWindow (BitVec.ofNat 64 q) 8
  slots : ∀ q, Slot p limit q → WriteWindow (entry c.σ.mem (BitVec.ofNat 64 q)) 8 ∧
    ReadWindow (entry c.σ.mem (BitVec.ofNat 64 q)) 8 ∧
    ((entry c.σ.mem (BitVec.ofNat 64 q)).toNat + 8 ≤ (OldifyEntry.frameSp R).toNat ∨
      (R 2).toNat ≤ (entry c.σ.mem (BitVec.ofNat 64 q)).toNat)
  stateRead : ReadWindow statePtr 8
  fieldRead : ReadWindow (bytesT c.σ.mem Layout.sym_Caml_state 8 + 104#64) 8
  ptrRead : ReadWindow (refTable c.σ.mem + 24#64) 8
  watched : ∀ a, Watched c.σ.mem p limit a → ¬ writes a ∧
    (a < (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a) ∧
    ∀ q, Slot p limit q → a < (entry c.σ.mem (BitVec.ofNat 64 q)).toNat ∨
      (entry c.σ.mem (BitVec.ofNat 64 q)).toNat + 8 ≤ a

/-- At the loop's exit. -/
structure Exit (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (Extra : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (R : Nat → BitVec 64) (copies : List PendingCopy) (after : Config) : Prop where
  extra : Extra after.σ.mem
  ready : Ready copies after.σ.mem
  pc : PCAt exitPc after
  registers : ∃ p, GHolds after.σ (headRegs R p)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  code : Code.Caml_empty_minor_heapLoaded after.σ.mem

theorem linked_eq (R : Nat → BitVec 64) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    EmptyMinorRefsSites.refsSite.linked (calleeR R p m) 2 = R 2 ∧
    EmptyMinorRefsSites.refsSite.linked (calleeR R p m) 10 = bytesT m (entry m p).toNat 8 ∧
    EmptyMinorRefsSites.refsSite.linked (calleeR R p m) 11 = entry m p ∧
    EmptyMinorRefsSites.refsSite.linked (calleeR R p m) 1 = EmptyMinorRefsSites.refsSite.call.link := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [SlotSite.linked, calleeR]

theorem frameSp_linked (R : Nat → BitVec 64) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    OldifyEntry.frameSp (EmptyMinorRefsSites.refsSite.linked (calleeR R p m)) = OldifyEntry.frameSp R := by
  simp [OldifyEntry.frameSp, SlotSite.linked, calleeR]

theorem slot_self {p limit : BitVec 64} (room : p.toNat + 8 ≤ limit.toNat) : Slot p limit p.toNat :=
  ⟨Nat.le_refl _, room, by simp⟩

theorem ofNat_self (p : BitVec 64) : BitVec.ofNat 64 p.toNat = p := by simp

variable {Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop}
  {Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop} {pl : Place} {support writes : Nat → Prop}
  {Extra : Std.ExtHashMap Nat (BitVec 8) → Prop}

theorem room_of {R limit p copies c} (inv : Inv Ready Root writes Extra R limit p copies c) :
    CallRoom R (entry c.σ.mem p) := by
  obtain ⟨w, -, apart⟩ := inv.slots p.toNat (slot_self inv.room)
  rw [ofNat_self] at w apart
  exact ⟨inv.frameWindows, w, apart⟩

theorem slotEntry {R limit p copies c e} (inv : Inv Ready Root writes Extra R limit p copies c)
    (jumped : Jumped R p c e) :
    SlotEntry (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) c.σ.mem e := by
  obtain ⟨sp2, v10, v11, v1⟩ := linked_eq R p c.σ.mem
  have room := room_of inv
  refine ⟨jumped.good, jumped.minstret, jumped.tick, jumped.memory, jumped.registers, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frameSp_linked]; exact room.windows
  · rw [v10, v11]
  · rw [v11]; exact room.slotWrite
  · rw [v11, frameSp_linked, sp2]; exact room.slotApart
  · rw [v1]; exact EmptyMinorRefsSites.refsSite.aligned

theorem image_transport {m m' : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Caml_empty_minor_heapLoaded m)
    (same : ∀ a, a < textEnd → m'[a]? = m[a]?) : Code.Caml_empty_minor_heapLoaded m' :=
  Code.caml_empty_minor_heap_transport code (fun a _ hi => same a (by simp only [textEnd]; omega))

/-- **One call keeps** the loop's words and the code, and readiness. -/
theorem call_keeps (S : SlotSupply Ready Root pl support writes) {R limit p copies copies' c e mid}
    (inv : Inv Ready Root writes Extra R limit p copies c) (jumped : Jumped R p c e)
    (done : SlotDone (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid) :
    (Ready copies' mid.σ.mem ∧ ∀ q, Root c.σ.mem q → Root mid.σ.mem q) ∧
    ∀ a, (Watched c.σ.mem p limit a ∨ a < textEnd) → mid.σ.mem[a]? = c.σ.mem[a]? := by
  have room := room_of inv
  have entryE := slotEntry inv jumped
  obtain ⟨sp2, -, v11, -⟩ := linked_eq R p c.σ.mem
  have root : Root c.σ.mem ((EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) 11).toNat := by
    rw [v11]
    have h := inv.roots _ (slot_self inv.room)
    rwa [ofNat_self] at h
  refine ⟨S.preserve _ copies copies' c.σ.mem e mid inv.ready root entryE done, ?_⟩
  intro a where_
  apply S.footprint _ copies copies' c.σ.mem e mid inv.ready root entryE done a
  · rcases where_ with w | low
    · exact (inv.watched a w).1
    · exact S.codeOutside a (by simp only [textEnd, tohostAddr, LibraryLayout.tohostAddr] at low ⊢; omega)
  · rw [frameSp_linked, sp2]
    rcases where_ with w | low
    · exact (inv.watched a w).2.1
    · exact Or.inl (by have := frame_high room; omega)
  · rw [v11]
    rcases where_ with w | low
    · have h := (inv.watched a w).2.2 p.toNat (slot_self inv.room)
      rwa [ofNat_self] at h
    · exact Or.inl (by have := slot_high room; omega)

theorem word_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} {x : Nat} (same : ∀ a, word8 x a → m'[a]? = m[a]?) :
    bytesT m' x 8 = bytesT m x 8 := by
  apply OCaml.Vm.Reloc.bytesT_congr (x := x) (x' := x)
  intro j hj
  rw [byte_one, byte_one, same _ ⟨by omega, by omega⟩]

theorem words_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} {p limit : BitVec 64}
    (same : ∀ a, Watched m p limit a → m'[a]? = m[a]?) :
    bytesT m' Layout.sym_Caml_state 8 = bytesT m Layout.sym_Caml_state 8 ∧ refTable m' = refTable m ∧
    tablePtr m' = tablePtr m ∧ ∀ q, Slot p limit q → entry m' (BitVec.ofNat 64 q) = entry m (BitVec.ofNat 64 q) := by
  have st := word_kept (m := m) (m' := m') (fun a w => same a (Or.inl w))
  have fld : refTable m' = refTable m := by
    unfold refTable
    rw [st]
    exact word_kept (fun a w => same a (Or.inr (Or.inl (by rw [← st] at w ⊢; exact w))))
  refine ⟨st, fld, ?_, ?_⟩
  · unfold tablePtr
    rw [fld]
    exact word_kept (fun a w => same a (Or.inr (Or.inr (Or.inl (by rw [← fld] at w ⊢; exact w)))))
  · intro q hq
    have small : q < 2 ^ 64 := by have := limit.isLt; have := hq.2.1; omega
    have addr : (BitVec.ofNat 64 q).toNat = q := by simp only [BitVec.toNat_ofNat]; omega
    unfold entry
    rw [addr]
    exact word_kept (fun a w => same a (Or.inr (Or.inr (Or.inr ⟨q, hq, w⟩))))

theorem watched_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} {p limit : BitVec 64}
    (same : ∀ a, Watched m p limit a → m'[a]? = m[a]?) (a : Nat) :
    Watched m' p limit a ↔ Watched m p limit a := by
  obtain ⟨st, fld, -, -⟩ := words_kept same
  unfold Watched
  rw [st, fld]

theorem slot_next {p limit : BitVec 64} {q : Nat} (h : Slot (p + 8#64) limit q) (room : p.toNat + 8 ≤ limit.toNat) :
    Slot p limit q := by
  have lim := limit.isLt
  have addr : (p + 8#64).toNat = p.toNat + 8 := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨lo, hi, al⟩ := h
  rw [addr] at lo al
  exact ⟨by omega, hi, by omega⟩

theorem refs_next (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Extra m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Extra m') {R limit p copies c after}
    (inv : Inv Ready Root writes Extra R limit p copies c) (post : Iterated R p copies pl c after)
    (pc : PCAt bodyPc after) : ∃ copies', Inv Ready Root writes Extra R limit (p + 8#64) copies' after := by
  obtain ⟨e, copies', mid, jumped, done, memory, pcIf⟩ := post.slot
  obtain ⟨⟨ready', roots'⟩, keep⟩ := call_keeps S inv jumped done
  have sameW : ∀ a, Watched c.σ.mem p limit a → after.σ.mem[a]? = c.σ.mem[a]? := fun a w => by
    rw [memory]; exact keep a (Or.inl w)
  obtain ⟨st, fld, ptrEq, entryEq⟩ := words_kept sameW
  have ptrMid : tablePtr mid.σ.mem = limit := by rw [← memory, ptrEq, inv.ptrWord]
  have more : continues (p + 8#64) mid.σ.mem = true := by
    by_cases h : continues (p + 8#64) mid.σ.mem = true
    · exact h
    · rw [if_neg h] at pcIf
      rw [PCAt] at pcIf pc
      rw [pcIf] at pc
      exact absurd (Option.some.inj pc) (by decide)
  have below : (p + 8#64).toNat < limit.toNat := by
    have := of_decide_eq_true more
    rwa [ptrMid] at this
  have lim := limit.isLt
  have addr : (p + 8#64).toNat = p.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := inv.room; omega
  have room' : (p + 8#64).toNat + 8 ≤ limit.toNat := by have := inv.aligned; omega
  have slotNext : Slot p limit (p.toNat + 8) := ⟨by omega, by omega, by simp⟩
  have pAddr : BitVec.ofNat 64 (p.toNat + 8) = p + 8#64 := by
    apply BitVec.eq_of_toNat_eq; rw [addr]; simp only [BitVec.toNat_ofNat]; omega
  have win := inv.entries _ slotNext
  have slotRd := (inv.slots _ slotNext).2.1
  rw [pAddr] at win slotRd
  have entryNext : entry after.σ.mem (p + 8#64) = entry c.σ.mem (p + 8#64) := by
    rw [← pAddr]; exact entryEq _ slotNext
  refine ⟨copies', ?_⟩
  exact
    { head := { good := post.good, tick := post.tick, minstret := post.minstret
                code := image_transport inv.head.code (fun a ha => by rw [memory]; exact keep a (Or.inr ha))
                pc := pc, registers := post.registers, window := win
                slotRead := by rw [entryNext]; exact slotRd }
      extra := transport _ _ inv.extra (fun a ha => by rw [memory]; exact keep a (Or.inr ha))
      room := room'
      aligned := by have := inv.aligned; omega
      ready := by rw [memory]; exact ready'
      ptrWord := by rw [ptrEq, inv.ptrWord]
      roots := fun q hq => by
        rw [entryEq q (slot_next hq inv.room), memory]
        exact roots' _ (inv.roots q (slot_next hq inv.room))
      frameWindows := inv.frameWindows
      entries := fun q hq => inv.entries q (slot_next hq inv.room)
      slots := fun q hq => by rw [entryEq q (slot_next hq inv.room)]; exact inv.slots q (slot_next hq inv.room)
      stateRead := inv.stateRead
      fieldRead := by rw [st]; exact inv.fieldRead
      ptrRead := by rw [fld]; exact inv.ptrRead
      watched := fun a w => by
        have w' : Watched c.σ.mem p limit a := by
          unfold Watched at w
          rw [st, fld] at w
          rcases w with h | h | h | ⟨q, hq, hw⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr ⟨q, slot_next hq inv.room, hw⟩))
        obtain ⟨notW, frame, slots⟩ := inv.watched a w'
        exact ⟨notW, frame, fun q hq => by
          rw [entryEq q (slot_next hq inv.room)]; exact slots q (slot_next hq inv.room)⟩ }

theorem refs_done (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Extra m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Extra m') {R limit p copies c after}
    (inv : Inv Ready Root writes Extra R limit p copies c) (post : Iterated R p copies pl c after)
    (pc : PCAt exitPc after) : ∃ copies', Exit Ready Extra R copies' after := by
  obtain ⟨e, copies', mid, jumped, done, memory, -⟩ := post.slot
  obtain ⟨⟨ready', -⟩, keep⟩ := call_keeps S inv jumped done
  exact ⟨copies', transport _ _ inv.extra (fun a ha => by rw [memory]; exact keep a (Or.inr ha)),
    by rw [memory]; exact ready', pc, ⟨_, post.registers⟩, post.good, post.tick, post.minstret,
    image_transport inv.head.code (fun a ha => by rw [memory]; exact keep a (Or.inr ha))⟩

theorem callee_frame (S : SlotSupply Ready Root pl support writes) {R limit p copies copies' c e mid}
    (inv : Inv Ready Root writes Extra R limit p copies c) (jumped : Jumped R p c e)
    (done : SlotDone (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid) :
    CalleeFrame c mid := by
  obtain ⟨-, keep⟩ := call_keeps S inv jumped done
  obtain ⟨st, fld, -, -⟩ := words_kept (fun a w => keep a (Or.inl w))
  refine ⟨image_transport inv.head.code (fun a ha => keep a (Or.inr ha)), inv.stateRead, ?_, ?_⟩
  · rw [st]; exact inv.fieldRead
  · rw [fld]; exact inv.ptrRead

/-- **The remembered-set loop's obligations from the collection in progress.** -/
theorem scanStep (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Extra m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Extra m')
    (R : Nat → BitVec 64) (limit : BitVec 64) :
    ScanStep R limit pl (Inv Ready Root writes Extra R limit) (fun after => ∃ copies, Exit Ready Extra R copies after) where
  head := fun _ _ _ inv => ⟨inv.head, inv.room⟩
  supply := fun p copies c inv e jumped => by
    apply S.supply _ copies c.σ.mem e inv.ready _ (slotEntry inv jumped)
    rw [(linked_eq R p c.σ.mem).2.2.1]
    have h := inv.roots _ (slot_self inv.room)
    rwa [ofNat_self] at h
  frame := fun _ _ _ inv _ _ _ jumped done => callee_frame S inv jumped done
  next := fun _ _ _ _ inv post pc => refs_next S transport inv post pc
  done := fun _ _ _ _ inv post pc => refs_done S transport inv post pc
  donePc := fun _ ⟨_, exit⟩ => exit.pc

end OCaml.Vm.Gc.RefLoops
