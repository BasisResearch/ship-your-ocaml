import OCaml.Vm.Boot.Startup.DomainInit
import OCaml.Vm.Boot.Startup.BacktraceLayout
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.VsaHeap OCaml.Vm.Primitives

/-! The first domain's record and its minor ref tables as startup leaves them,
and `LiveFrame`: the bytes of a run's owned allocator blocks are unchanged. -/

/-- A field of the first domain's state. -/
def domainField (off : Nat) : Nat := firstDomainPtr.toNat + off

/-- A ref-table record of 56 bytes in the arena. -/
structure RefTableSpot (t : BitVec 64) : Prop where
  low : heapStart ≤ t.toNat
  high : t.toNat + 56 ≤ heapEnd
  aligned : t.toNat % 8 = 0

/-- The ref tables' facts that do not mention the page table. -/
structure RefTablesPre (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (t1 t2 t3 : BitVec 64) : Prop where
  ptr1 : bytesT m (domainField 104) 8 = t1
  ptr2 : bytesT m (domainField 112) 8 = t2
  ptr3 : bytesT m (domainField 120) 8 = t3
  spot1 : RefTableSpot t1
  spot2 : RefTableSpot t2
  spot3 : RefTableSpot t3
  empty1 : bytesT m t1.toNat 8 = 0#64
  empty2 : bytesT m t2.toNat 8 = 0#64
  empty3 : bytesT m t3.toNat 8 = 0#64
  apart12 : t1.toNat + 56 ≤ t2.toNat ∨ t2.toNat + 56 ≤ t1.toNat
  apart23 : t2.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t2.toNat
  domain1 : t1.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t1.toNat
  apart13 : t1.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t1.toNat
  domain2 : t2.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t2.toNat
  domain3 : t3.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t3.toNat
  owned1 : (t1.toNat, 56) ∈ H
  owned2 : (t2.toNat, 56) ∈ H
  owned3 : (t3.toNat, 56) ∈ H

/-- Bytes of a live block are outside the allocator's footprint. -/
theorem owned_not_foot {H : List (Nat × Nat)} {a : Nat} (above : heapStart ≤ a) (owned : ∃ e ∈ H, InExt e a) :
    ¬ vsaFoot H a := by
  obtain ⟨e, he, inside⟩ := owned
  rintro (global | ⟨_, _, out⟩)
  · unfold allocGlobal InRange heapStart at *; omega
  · exact out e he inside


/-- A fresh block lies apart from every live block. -/
theorem FreshBlock.apart {L : DlLayout} {H : List (Nat × Nat)} {p n : Nat} (fresh : FreshBlock L H p n)
    {q m : Nat} (owned : (q, m) ∈ H) (pos : 0 < n) (qpos : 0 < m) : p + n ≤ q ∨ q + m ≤ p := by
  have a := fresh.2.2.2 _ owned
  rcases Nat.lt_or_ge p q with h | h
  · rcases Nat.lt_or_ge (p + n) (q + 1) with h' | h'
    · exact Or.inl (by omega)
    · exact absurd (show InExt (q, m) q by unfold InExt; dsimp only; omega) (a q (by unfold InExt; dsimp only; omega))
  · rcases Nat.lt_or_ge p (q + m) with h' | h'
    · exact absurd (show InExt (q, m) p by unfold InExt; dsimp only; omega) (a p (by unfold InExt; dsimp only; omega))
    · exact Or.inr h'

/-- Every byte inside an owned block of `H` is unchanged from `before` to `after`. -/
structure LiveFrame (H : List (Nat × Nat)) (before after : Config) : Prop where
  -- discipline: allow(O9-hand-live-frame) the definition of LiveFrame itself
  byte : ∀ e ∈ H, ∀ x, InExt e x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem LiveFrame.trans {H : List (Nat × Nat)} {before middle after : Config} (first : LiveFrame H before middle)
    (second : LiveFrame H middle after) : LiveFrame H before after :=
  ⟨fun e he x hx => (second.byte e he x hx).trans (first.byte e he x hx)⟩

theorem LiveFrame.of_memory {H : List (Nat × Nat)} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    LiveFrame H before after :=
  ⟨fun _ _ _ _ => by rw [memory]⟩

theorem LiveFrame.mono {H H' : List (Nat × Nat)} {before after : Config} (h : LiveFrame H' before after)
    (sub : ∀ e ∈ H, e ∈ H') : LiveFrame H before after :=
  ⟨fun e he x hx => h.byte e (sub e he) x hx⟩

/-- A change confined outside the arena keeps every block that lies in it. -/
theorem LiveFrame.of_arena {H : List (Nat × Nat)} {before after : Config}
    (bounds : ∀ e ∈ H, heapStart ≤ e.1 ∧ e.1 + e.2 ≤ heapEnd)
    (f : ∀ x, heapStart ≤ x → x < heapEnd → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0) :
    LiveFrame H before after :=
  ⟨fun e he x hx => by have b := bounds e he; unfold InExt at hx; exact f x (by omega) (by omega)⟩

/-- A change outside the allocator's footprint keeps every owned block. -/
theorem LiveFrame.of_foot {H : List (Nat × Nat)} {before after : Config}
    (bounds : ∀ e ∈ H, heapStart ≤ e.1 ∧ e.1 + e.2 ≤ heapEnd)
    (f : ∀ x, x < heapEnd → ¬ vsaFoot H x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0) :
    LiveFrame H before after :=
  ⟨fun e he x hx => by
    have b := bounds e he
    have hx' := hx
    unfold InExt at hx'
    exact f x (by omega) (owned_not_foot (by omega) ⟨e, he, hx⟩)⟩

/-- caml_init_domain's record and the minor ref tables as caml_init_gc reads
them: the record is owned, `young_limit` equals `young_trigger`, there is no
minor heap and no major heap yet, and the three tables are empty. -/
structure DomainKept (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (t1 t2 t3 : BitVec 64) : Prop where
  owned : (firstDomainPtr.toNat, 928) ∈ H
  idle : bytesT m (domainField 8) 8 = bytesT m (domainField 56) 8
  noYoung : bytesT m (domainField 32) 8 = 0#64
  noHeap : bytesT m (domainField 336) 8 = 0#64
  refs : RefTablesPre H m t1 t2 t3
  lastExn : bytesT m (domainField backtrace_last_exnOffset) 8 = 1#64

/-- The record and the tables survive any change that keeps the memory below the arena's end. -/
theorem DomainKept.of_low {H : List (Nat × Nat)} {m m' : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 : BitVec 64}
    (h : DomainKept H m t1 t2 t3) (f : ∀ x, x < heapEnd → (m'[x]?).getD 0 = (m[x]?).getD 0) :
    DomainKept H m' t1 t2 t3 := by
  have word (a : Nat) (ha : a + 8 ≤ heapEnd) : bytesT m' a 8 = bytesT m a 8 :=
    word_observed _ fun i hi => f _ (by omega)
  have field (off : Nat) (hoff : off + 8 ≤ 928) : bytesT m' (domainField off) 8 = bytesT m (domainField off) 8 :=
    word _ (by
      have : firstDomainPtr.toNat + 928 ≤ heapEnd := by decide
      unfold domainField; omega)
  have table {t : BitVec 64} (spot : RefTableSpot t) : bytesT m' t.toNat 8 = bytesT m t.toNat 8 :=
    word _ (by have := spot.high; omega)
  have R := h.refs
  exact ⟨h.owned, (field 8 (by decide)).trans (h.idle.trans (field 56 (by decide)).symm),
    (field 32 (by decide)).trans h.noYoung, (field 336 (by decide)).trans h.noHeap,
    { R with
      ptr1 := (field 104 (by decide)).trans R.ptr1
      ptr2 := (field 112 (by decide)).trans R.ptr2
      ptr3 := (field 120 (by decide)).trans R.ptr3
      empty1 := (table R.spot1).trans R.empty1
      empty2 := (table R.spot2).trans R.empty2
      empty3 := (table R.spot3).trans R.empty3 },
    (field backtrace_last_exnOffset (by decide)).trans h.lastExn⟩


/-- The record and the tables survive any change confined outside the arena. -/
theorem DomainKept.of_arena {H : List (Nat × Nat)} {m m' : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 : BitVec 64}
    (h : DomainKept H m t1 t2 t3) (f : ∀ x, heapStart ≤ x → x < heapEnd → (m'[x]?).getD 0 = (m[x]?).getD 0) :
    DomainKept H m' t1 t2 t3 := by
  have word (a : Nat) (lo : heapStart ≤ a) (ha : a + 8 ≤ heapEnd) : bytesT m' a 8 = bytesT m a 8 :=
    word_observed _ fun i hi => f _ (by omega) (by omega)
  have field (off : Nat) (hoff : off + 8 ≤ 928) : bytesT m' (domainField off) 8 = bytesT m (domainField off) 8 :=
    have lo : heapStart ≤ firstDomainPtr.toNat := by decide
    have hi : firstDomainPtr.toNat + 928 ≤ heapEnd := by decide
    word _ (Nat.le_trans lo (Nat.le_add_right _ _))
      (by show firstDomainPtr.toNat + off + 8 ≤ heapEnd
          rw [Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hoff _) hi)
  have table {t : BitVec 64} (spot : RefTableSpot t) : bytesT m' t.toNat 8 = bytesT m t.toNat 8 :=
    word _ spot.low (Nat.le_trans (Nat.add_le_add_left (by decide) _) spot.high)
  have R := h.refs
  exact ⟨h.owned, (field 8 (by decide)).trans (h.idle.trans (field 56 (by decide)).symm),
    (field 32 (by decide)).trans h.noYoung, (field 336 (by decide)).trans h.noHeap,
    { R with
      ptr1 := (field 104 (by decide)).trans R.ptr1
      ptr2 := (field 112 (by decide)).trans R.ptr2
      ptr3 := (field 120 (by decide)).trans R.ptr3
      empty1 := (table R.spot1).trans R.empty1
      empty2 := (table R.spot2).trans R.empty2
      empty3 := (table R.spot3).trans R.empty3 },
    (field backtrace_last_exnOffset (by decide)).trans h.lastExn⟩

/-- The record and the tables survive any run that keeps the owned blocks. -/
theorem DomainKept.live {H : List (Nat × Nat)} {before after : Config} {t1 t2 t3 : BitVec 64}
    (h : DomainKept H before.σ.mem t1 t2 t3) (f : LiveFrame H before after) : DomainKept H after.σ.mem t1 t2 t3 := by
  have field (off : Nat) (hoff : off + 8 ≤ 928) : bytesT after.σ.mem (domainField off) 8 = bytesT before.σ.mem (domainField off) 8 :=
    word_observed _ fun i hi => f.byte _ h.owned _ (by unfold InExt domainField; dsimp only; omega)
  have table {t : BitVec 64} (owned : (t.toNat, 56) ∈ H) : bytesT after.σ.mem t.toNat 8 = bytesT before.σ.mem t.toNat 8 :=
    word_observed _ fun i hi => f.byte _ owned _ (by unfold InExt; dsimp only; omega)
  have R := h.refs
  exact ⟨h.owned, (field 8 (by decide)).trans (h.idle.trans (field 56 (by decide)).symm),
    (field 32 (by decide)).trans h.noYoung, (field 336 (by decide)).trans h.noHeap,
    { R with
      ptr1 := (field 104 (by decide)).trans R.ptr1
      ptr2 := (field 112 (by decide)).trans R.ptr2
      ptr3 := (field 120 (by decide)).trans R.ptr3
      empty1 := (table R.owned1).trans R.empty1
      empty2 := (table R.owned2).trans R.empty2
      empty3 := (table R.owned3).trans R.empty3 },
    (field backtrace_last_exnOffset (by decide)).trans h.lastExn⟩

/-- More owned blocks keep the record's facts. -/
theorem DomainKept.mono {H H' : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 : BitVec 64}
    (h : DomainKept H m t1 t2 t3) (sub : ∀ e ∈ H, e ∈ H') : DomainKept H' m t1 t2 t3 :=
  ⟨sub _ h.owned, h.idle, h.noYoung, h.noHeap,
    { h.refs with owned1 := sub _ h.refs.owned1, owned2 := sub _ h.refs.owned2, owned3 := sub _ h.refs.owned3 }, h.lastExn⟩
end OCaml.Vm.Boot.Startup
