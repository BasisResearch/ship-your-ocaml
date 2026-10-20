import OCaml.Vm.Gc.SlotSupply
import OCaml.Vm.Gc.RootLoops
import OCaml.Vm.Gc.ForwardedCall

/-! # Route inputs from a root-slot call's entry

Toward instantiating `SlotSupply`: each `caml_oldify_one` route's input
from `SlotEntry` (the caller's side) plus the few facts the collection state
contributes. The slot lies outside the callee's 112-byte frame, so it is
apart from every saved word. -/
namespace OCaml.Vm.Gc.RouteSupply
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The callee's frame `[frameSp, R 2)` in the native stack. -/
theorem frame_top {R : Nat → BitVec 64}
    (windows : ∀ cell ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8) :
    (OldifyEntry.frameSp R).toNat + 112 = (R 2).toNat ∧ (OldifyEntry.frameSp R).toNat + 112 ≤ 0x100000000 := by
  obtain ⟨cell, member, top⟩ : ∃ cell ∈ OldifyEntry.saves, cell.2 = 104 := ⟨(1, 104), by decide, rfl⟩
  have w := windows cell member
  rw [top] at w
  have h := RootLoops.window_base (by decide) w
  have limit := (R 2).isLt
  have neg : (-OldifyReturn.frameSize : BitVec 64) = 18446744073709551504#64 := by decide
  have sp : (OldifyEntry.frameSp R).toNat = ((R 2).toNat + 18446744073709551504) % 18446744073709551616 := by
    rw [OldifyEntry.frameSp, neg, BitVec.toNat_add]
    rfl
  simp only [Layout.sym_tohost] at h
  have big : 112 ≤ (R 2).toNat := by
    by_cases small : (R 2).toNat < 112
    · have wrap : ((R 2).toNat + 18446744073709551504) % 18446744073709551616 = (R 2).toNat + 18446744073709551504 :=
        Nat.mod_eq_of_lt (by omega)
      rw [wrap] at sp
      rw [sp] at h
      omega
    · omega
  have exact : ((R 2).toNat + 18446744073709551504) % 18446744073709551616 = (R 2).toNat - 112 := by
    have split : (R 2).toNat + 18446744073709551504 = ((R 2).toNat - 112) + 18446744073709551616 := by omega
    rw [split, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [exact] at sp
  rw [sp] at h ⊢
  constructor <;> omega

/-- The slot is apart from every word the callee saves. -/
theorem slot_outside {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config} (entry : SlotEntry R m e) :
    ∀ off ∈ OldifyReturn.offsets,
      (R 11).toNat + 8 ≤ (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat ∨
        (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat + 8 ≤ (R 11).toNat := by
  intro off member
  have small : off ≤ 104 := (show ∀ x ∈ OldifyReturn.offsets, x ≤ 104 by decide) off member
  obtain ⟨top, bound⟩ := frame_top entry.windows
  have addr : (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat = (OldifyEntry.frameSp R).toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [addr]
  rcases entry.slotApart with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem outLRange_append : ∀ (l1 l2 : List WEntry) (a n : Nat), OutLRange l1 a n → OutLRange l2 a n →
    OutLRange (l1 ++ l2) a n
  | [], _, _, _, _, h => h
  | _ :: l1, l2, a, n, ⟨h, t⟩, h2 => ⟨h, outLRange_append l1 l2 a n t h2⟩

/-- A word apart from the callee's frame is outside its saves. -/
theorem save_out {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config} (entry : SlotEntry R m e)
    {slots : List (Nat × Nat)} (small : ∀ cell ∈ slots, cell.2 ≤ 104) {a : Nat}
    (apart : a + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a) :
    OutLRange (OldifyEntry.saveLog slots R) a 8 := by
  apply outLRange_of_forall
  intro w member
  obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp member
  obtain ⟨top, bound⟩ := frame_top entry.windows
  have off := small cell hc
  have addr : (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = (OldifyEntry.frameSp R).toNat + cell.2 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := cell.2) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rw [addr]
  rcases apart with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- A word apart from the callee's frame and the slot is outside a route's
saves-then-root-store effect. -/
theorem effect_out {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config} (entry : SlotEntry R m e)
    {slots : List (Nat × Nat)} (small : ∀ cell ∈ slots, cell.2 ≤ 104) (v : BitVec 64) {a : Nat}
    (frame : a + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a)
    (slot : a + 8 ≤ (R 11).toNat ∨ (R 11).toNat + 8 ≤ a) :
    OutLRange (OldifyEntry.saveLog slots R ++ [((R 11).toNat, 8, v)]) a 8 :=
  outLRange_append _ _ _ _ (save_out entry small frame) ⟨slot, trivial⟩

/-- The published sources' header and first words, apart from the callee's
frame and the slot (sources lie in the nursery; frames and root slots do not). -/
def SourcesApart (R : Nat → BitVec 64) (copies : List PendingCopy) : Prop :=
  ∀ q ∈ copies, ∀ a ∈ [(q.source - 8#64).toNat, q.source.toNat],
    (a + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a) ∧ (a + 8 ≤ (R 11).toNat ∨ (R 11).toNat + 8 ≤ a)

theorem table_outside {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config} (entry : SlotEntry R m e)
    {copies : List PendingCopy} (apart : SourcesApart R copies)
    {slots : List (Nat × Nat)} (small : ∀ cell ∈ slots, cell.2 ≤ 104) (v : BitVec 64) :
    ForwardingTable.Outside copies (OldifyEntry.saveLog slots R ++ [((R 11).toNat, 8, v)]) := by
  intro q member
  have h1 := apart q member (q.source - 8#64).toNat (List.mem_cons_self ..)
  have h2 := apart q member q.source.toNat (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact ⟨effect_out entry small v h1.1 h1.2, effect_out entry small v h2.1 h2.2⟩

/-- **The immediate route** from a call's entry: an odd value. -/
theorem immediate_call {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config}
    {copies : List PendingCopy} {pl : Place} (entry : SlotEntry R m e)
    (code : Code.Caml_oldify_oneLoaded e.σ.mem) (odd : (R 10).toNat % 2 = 1)
    (view : (ForwardingTable.eqv copies).P pl 0 e) (apart : SourcesApart R copies)
    (aligned : ∀ q ∈ copies, q.source.toNat % 8 = 0) : SlotCall R copies pl e := by
  have outside := slot_outside entry
  refine SlotCall.immediate ⟨entry.good, entry.minstret, entry.tick, code, entry.registers, entry.windows, odd,
    entry.slotWrite, fun off h => outside off (by revert off h; decide), entry.aligned⟩ view ?_ ?_
  · unfold OldifyImmediate.callEffect
    exact table_outside entry apart (by decide) _
  · intro q hq same
    have := aligned q hq
    omega

/-- The words the classifier reads (`Caml_state`, the domain's `young_start`
and `young_end`), apart from the callee's frame. -/
def DomainApart (R : Nat → BitVec 64) (domain : BitVec 64) : Prop :=
  ∀ a ∈ [Layout.sym_Caml_state, (domain + BitVec.ofNat 64 Layout.off_young_start).toNat,
      (domain + BitVec.ofNat 64 Layout.off_young_end).toNat],
    a + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a

theorem domain_outside {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config} (entry : SlotEntry R m e)
    {domain : BitVec 64} (apart : DomainApart R domain) : OldifyEntry.DomainOutside R domain :=
  ⟨save_out entry (by decide) (apart _ (List.mem_cons_self ..)),
   save_out entry (by decide) (apart _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
   save_out entry (by decide) (apart _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))⟩

/-- **The non-young route** from a call's entry: an even value outside the nursery. -/
theorem nonYoung_call {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config}
    {copies : List PendingCopy} {pl : Place} {domain : BitVec 64} (entry : SlotEntry R m e)
    (code : Code.Caml_oldify_oneLoaded e.σ.mem) (even : (R 10).toNat % 2 = 0)
    (root : word e Layout.sym_Caml_state = domain) (windows : Young.Windows domain)
    (domainApart : DomainApart R domain)
    (notYoung : ¬ ((Young.lowerWord domain e).toNat < (R 10).toNat ∧ (R 10).toNat < (Young.upperWord domain e).toNat))
    (view : (ForwardingTable.eqv copies).P pl 0 e) (apart : SourcesApart R copies)
    (young : ∀ q ∈ copies, (Young.lowerWord domain e).toNat < q.source.toNat ∧
      q.source.toNat < (Young.upperWord domain e).toNat) : SlotCall R copies pl e := by
  refine SlotCall.nonYoung (domain := domain)
    { root := root, domainWindows := windows, domainOutside := domain_outside entry domainApart
      notYoung := notYoung, rootWrite := entry.slotWrite, rootOutside := slot_outside entry
      aligned := entry.aligned
      entry := ⟨entry.good, entry.minstret, entry.tick, code, entry.registers, entry.windows, even⟩ } view ?_ ?_
  · unfold NonYoung.effect
    exact table_outside entry apart (by decide) _
  · intro q hq same
    exact notYoung (by rw [← same]; exact young q hq)

/-- **The forwarded route** from a call's entry: a young value already copied. -/
theorem forwarded_call {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {e : Config}
    {copies : List PendingCopy} {pl : Place} {domain : BitVec 64} {q : PendingCopy} (entry : SlotEntry R m e)
    (code : Code.Caml_oldify_oneLoaded e.σ.mem) (even : (R 10).toNat % 2 = 0)
    (root : word e Layout.sym_Caml_state = domain) (windows : Young.Windows domain)
    (domainApart : DomainApart R domain)
    (lower : (Young.lowerWord domain e).toNat < (R 10).toNat) (upper : (R 10).toNat < (Young.upperWord domain e).toNat)
    (header : word e (R 10 - 8#64).toNat = 0) (headerRead : ReadWindow (R 10 - 8#64) 8)
    (sourceRead : ReadWindow (R 10) 8)
    (valueApart : ∀ a ∈ [(R 10 - 8#64).toNat, (R 10).toNat], a + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a)
    (view : (ForwardingTable.eqv copies).P pl 0 e) (apart : SourcesApart R copies)
    (member : q ∈ copies) (source : q.source = R 10) : SlotCall R copies pl e := by
  refine SlotCall.forwarded (domain := domain)
    { root := root, domainWindows := windows, domainOutside := domain_outside entry domainApart
      lower := lower, upper := upper, header := header, headerRead := headerRead, sourceRead := sourceRead
      headerOutside := save_out entry (by decide) (valueApart _ (List.mem_cons_self ..))
      sourceOutside := save_out entry (by decide) (valueApart _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      rootWrite := entry.slotWrite, rootOutside := slot_outside entry, aligned := entry.aligned
      entry := ⟨entry.good, entry.minstret, entry.tick, code, entry.registers, entry.windows, even⟩ }
    view member source ?_
  unfold ForwardedCall.effect
  exact table_outside entry apart (by decide) _

end OCaml.Vm.Gc.RouteSupply
