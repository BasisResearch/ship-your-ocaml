import OCaml.Vm.Boot.Startup.MajorHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.VsaHeap OCaml.Vm.Primitives

/-! The runtime's page table as a concrete predicate on memory, for a6-gc's
`PageTableLookup Table` / `PageTableFrame Table tfoot` (`Table := PageClasses`).
It reads memory only inside `pageTableFoot`: the 0x28-byte record at
`caml_page_table` and the 16 KiB entry block whose address the record holds. -/

/-- The entry block's address, read from the record. -/
def pageEntWord (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (pageTable + 0x20) 8

/-- The page-table bytes: the record and the entry block it names. -/
def pageTableFoot (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : Prop :=
  (pageTable ≤ a ∧ a < pageTable + 0x28) ∨ ((pageEntWord m).toNat ≤ a ∧ a < (pageEntWord m).toNat + 16384)

/-- Whether slot `i` holds page `p` (page bits of a nonzero entry). -/
def slotHolds (m : Std.ExtHashMap Nat (BitVec 8)) (p i : Nat) : Bool :=
  slotWord m (pageEntWord m) i != 0#64 && ((slotWord m (pageEntWord m) i) &&& 0xfffffffffffff000#64).toNat == p

/-- The class of page `p`: the kind bits of the first slot holding it, 0 when absent. -/
def clsOf (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) : Nat :=
  match (List.range 2048).find? (slotHolds m p) with
  | some i => ((slotWord m (pageEntWord m) i) &&& 0xfff#64).toNat
  | none => 0

/-- The page table maps each page to `cls`. -/
structure PageClasses (m : Std.ExtHashMap Nat (BitVec 8)) (cls : Nat → Nat) : Prop where
  size : bytesT m (pageTable + 0) 8 = 2048#64
  shift : read4 m (pageTable + 8) = [53#8, 0#8, 0#8, 0#8]
  mask : bytesT m (pageTable + 0x10) 8 = 2047#64
  entLow : heapStart ≤ (pageEntWord m).toNat
  entHigh : (pageEntWord m).toNat + 16384 ≤ heapEnd
  classes : cls = clsOf m

/-- The startup table is a `PageClasses`. -/
theorem MajorTableAt.pageClasses {H : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64}
    (T : MajorTableAt H m ent) : PageClasses m (clsOf m) := by
  have e : pageEntWord m = ent := T.fields.entries
  exact ⟨T.fields.size, T.fields.shift, T.fields.mask, by rw [e]; exact T.high, by rw [e]; exact T.low, rfl⟩

theorem find?_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons]
    rw [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- `PageClasses` reads memory only inside `pageTableFoot`. -/
theorem PageClasses.frame {m m' : Std.ExtHashMap Nat (BitVec 8)} {cls : Nat → Nat} (h : PageClasses m cls)
    (same : ∀ a, pageTableFoot m a → (m'[a]?).getD 0 = (m[a]?).getD 0) : PageClasses m' cls := by
  have recw (off : Nat) (hoff : off + 8 ≤ 0x28) : bytesT m' (pageTable + off) 8 = bytesT m (pageTable + off) 8 :=
    word_observed _ fun i hi => same _ (Or.inl ⟨by omega, by omega⟩)
  have ent : pageEntWord m' = pageEntWord m := recw 0x20 (by decide)
  have slot (i : Nat) (hi : i < 2048) : slotWord m' (pageEntWord m') i = slotWord m (pageEntWord m) i := by
    rw [ent]
    have fits : (pageEntWord m).toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans h.entHigh (by decide)
    exact slotWord_window_agree fits (fun x inT => by
      rcases inT with r | b
      · exact same x (Or.inl r)
      · exact same x (Or.inr b)) i hi
  have holds (p i : Nat) (hi : i ∈ List.range 2048) : slotHolds m' p i = slotHolds m p i := by
    simp only [slotHolds, slot i (List.mem_range.mp hi)]
  have cl : clsOf m' = clsOf m := by
    funext p
    unfold clsOf
    rw [find?_congr_mem (holds p)]
    split
    · next i hfind =>
      rw [slot i (List.mem_range.mp (List.mem_of_find?_eq_some hfind))]
    · rfl
  refine ⟨(recw 0 (by decide)).trans h.size, ?_, (recw 0x10 (by decide)).trans h.mask, by rw [ent]; exact h.entLow,
    by rw [ent]; exact h.entHigh, by rw [cl]; exact h.classes⟩
  rw [← h.shift]
  simp only [read4]
  rw [show pageTable + 8 = pageTable + 8 + 0 from rfl,
    same _ (Or.inl ⟨by omega, by omega⟩), same (pageTable + 8 + 1) (Or.inl ⟨by omega, by omega⟩),
    same (pageTable + 8 + 2) (Or.inl ⟨by omega, by omega⟩), same (pageTable + 8 + 3) (Or.inl ⟨by omega, by omega⟩)]
end OCaml.Vm.Boot.Startup
