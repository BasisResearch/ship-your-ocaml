import OCaml.Vm.Boot.Startup.MinorRefSteps
import OCaml.Vm.Boot.Startup.StatAligned
import OCaml.Vm.Boot.Startup.PageAdd
import OCaml.Vm.Boot.Startup.PageTable
import OCaml.Vm.Primitives.Memprof.RenewCall
import OCaml.Vm.Boot.Startup.RuntimeKept
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_set_minor_heap_size(size) on the first call at startup: the domain
has no minor heap yet, the page table is the one caml_page_table_initialize
cleared, and the three ref tables have no storage. -/

theorem bytesT_empty (a w : Nat) : bytesT (∅ : Std.ExtHashMap Nat (BitVec 8)) a w = 0 := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    apply BitVec.eq_of_toNat_eq
    simp [bytesT, ih]
    rfl

theorem PageTableAt.slot_zero {m : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64} (T : PageTableAt m ent)
    (fits : ent.toNat + 16384 ≤ 2 ^ 64) (i : Nat) (hi : i < 2048) : slotWord m ent i = 0#64 := by
  unfold slotWord
  rw [slotAddr_nat ent i hi fits, word_observed (m := (∅ : Std.ExtHashMap Nat (BitVec 8))) _ fun k hk => by
    rw [show ent.toNat + 8 * i + k = ent.toNat + (8 * i + k) by omega, T.cleared _ (by omega)]; simp]
  exact bytesT_empty _ _

theorem PageTableAt.count {m : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64} (T : PageTableAt m ent)
    (fits : ent.toNat + 16384 ≤ 2 ^ 64) : pageCount m ent.toNat = 0 := by
  unfold pageCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro i member
  rw [← slotWord_pageSlot m ent i (List.mem_range.mp member) fits, T.slot_zero fits i (List.mem_range.mp member)]
  decide

theorem PageTableAt.fields {m : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64} (T : PageTableAt m ent)
    (fits : ent.toNat + 16384 ≤ 2 ^ 64) : PageTableFields m (BitVec.ofNat 64 (pageCount m ent.toNat)) ent := by
  rw [T.count fits]
  exact ⟨by simpa using T.size, T.shift, T.mask, T.occupancy, T.entries⟩

/-- The table record and its slots carry over to memory that agrees on them. -/
theorem PageTableAt.agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64} (T : PageTableAt m ent)
    (record : ∀ x, pageTable ≤ x → x < pageTable + 0x28 → (m'[x]?).getD 0 = (m[x]?).getD 0)
    (slots : ∀ x, ent.toNat ≤ x → x < ent.toNat + 16384 → (m'[x]?).getD 0 = (m[x]?).getD 0) :
    PageTableAt m' ent where
  size := by rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact T.size
  shift := by rw [read4_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact T.shift
  mask := by rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact T.mask
  occupancy := by rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact T.occupancy
  entries := by rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact T.entries
  cleared := fun k hk => by rw [slots _ (by omega) (by omega)]; exact T.cleared k hk

theorem pageTable_record_not_foot {H : List (Nat × Nat)} {x : Nat} (lo : pageTable ≤ x) (hi : x < pageTable + 0x28) :
    ¬ vsaFoot H x := by
  have hP : pageTable = 0x800684b8 := rfl
  rw [hP] at lo hi
  rintro (global | ⟨above, _, _⟩)
  · unfold allocGlobal InRange at global; omega
  · unfold heapStart at above; omega

theorem owned_not_foot' {H : List (Nat × Nat)} {p n x : Nat} (high : heapStart ≤ p) (owned : (p, n) ∈ H)
    (lo : p ≤ x) (hi : x < p + n) : ¬ vsaFoot H x := fun foot => by
  have := block_foot_out high owned foot
  omega

theorem read8_agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (same : ∀ i, i < 8 → (m'[a + i]?).getD 0 = (m[a + i]?).getD 0) : read8 m' a = read8 m a := by
  have h0 := same 0 (by decide)
  rw [Nat.add_zero] at h0
  simp only [Primitives.read8, h0, same 1 (by decide), same 2 (by decide), same 3 (by decide), same 4 (by decide),
    same 5 (by decide), same 6 (by decide), same 7 (by decide)]

/-- A frame slot lies above the arena. -/
theorem NativeFrame.slot_above {sp : BitVec 64} {size off : Nat} (frame : NativeFrame sp size) (bound : off + 8 ≤ size) :
    heapEnd ≤ (nativeStack sp size + BitVec.ofNat 64 off).toNat := by
  rw [nativeStack, frame.address _ (by omega), frame.slot_nat (by omega)]
  have := frame.lower
  unfold nativeFrameBase
  omega

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
/-- caml_memprof_renew_minor_sample's stores, with its saved `ra` above the arena. -/
theorem renew_log_outside {sp ra start trig : BitVec 64} (high : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    ImageOutside (renewLog sp ra firstDomainPtr start trig) := by
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at high
  constructor <;> simp only [renewLog, OutLRange, and_true] <;>
    simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize,
      show triggerAddr.toNat = 2147896520 from rfl, show firstDomainPtr.toNat = 0x8007d150 from rfl] <;> omega

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
theorem renew_slot_apart {sp ra : BitVec 64} (high : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    ∀ a ∈ [2147896584#64, firstDomainPtr + 48#64, firstDomainPtr + 72#64, 2147896112#64],
      OutLRange [((sp - 16#64 + 8#64).toNat, 8, ra)] a.toNat 8 := by
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at high
  intro a member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h <;> subst h <;> simp only [OutLRange, and_true] <;>
    simp only [show (2147896584#64).toNat = 2147896584 from rfl, show (2147896112#64).toNat = 2147896112 from rfl,
      show (firstDomainPtr + 48#64).toNat = 0x8007d150 + 48 from rfl,
      show (firstDomainPtr + 72#64).toNat = 0x8007d150 + 72 from rfl] <;> omega

/-- A byte of the domain record lies below the arena's end, outside the page
table's occupancy word and slots, and is not the allocator's. -/
structure InDomain (x : Nat) : Prop where
  lo : firstDomainPtr.toNat ≤ x
  hi : x < firstDomainPtr.toNat + 928

theorem InDomain.field {off i : Nat} (h : off + 8 ≤ 928) (hi : i < 8) : InDomain (domainField off + i) := by
  constructor <;> unfold domainField <;> omega

theorem InDomain.below {x : Nat} (d : InDomain x) : x < heapEnd := by
  have := d.hi
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  unfold heapEnd; omega

theorem InDomain.table {x : Nat} {ent : BitVec 64} (d : InDomain x)
    (apart : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat) :
    OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x := by
  have lo := d.lo
  have hi := d.hi
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  simp only [OutW, hP, and_true]
  omega

theorem InDomain.not_foot {x : Nat} {H : List (Nat × Nat)} (d : InDomain x) (owned : (firstDomainPtr.toNat, 928) ∈ H) :
    ¬ vsaFoot H x :=
  owned_not_foot' (by decide) owned d.lo d.hi

/-- A byte below the arena's end that the page-table insertions, the young-field
stores and the memprof renewal all missed. -/
structure EarlierOut (ent : BitVec 64) (fields renew : List WEntry) (x : Nat) : Prop where
  below : x < heapEnd
  tables : OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x
  fields : OutL fields x
  renew : OutL renew x

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
/-- A byte of a ref table misses everything written before the resets. -/
theorem RefTableSpot.byte_out {t ent sp ra start trig blk top tr wsize raw : BitVec 64} {x : Nat}
    (spot : RefTableSpot t) (lo : t.toNat ≤ x) (hi : x < t.toNat + 56)
    (domain : t.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t.toNat)
    (slots : t.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t.toNat)
    (slotHigh : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    EarlierOut ent (minorFieldsLog blk top tr wsize raw) (renewLog sp ra firstDomainPtr start trig) x := by
  have low := spot.low
  have high := spot.high
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  unfold heapStart at low
  rw [hE] at high slotHigh
  rw [dom] at domain
  refine ⟨by rw [hE]; omega, ?_, ?_, ?_⟩ <;>
    simp only [OutW, OutL, minorFieldsLog, renewLog, domainField, dom, hP,
      show triggerAddr.toNat = 2147896520 from rfl, and_true] <;> omega

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
/-- A byte of the domain record at or above the ref-table pointers misses everything written before the resets. -/
theorem domain_byte_out {ent sp ra start trig blk top tr wsize raw : BitVec 64} {off i : Nat}
    (lo : 104 ≤ off) (hi : off + 8 ≤ 928) (hi8 : i < 8)
    (tableDomain : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat)
    (slotHigh : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    EarlierOut ent (minorFieldsLog blk top tr wsize raw) (renewLog sp ra firstDomainPtr start trig)
      (domainField off + i) := by
  have inDomain : InDomain (domainField off + i) := InDomain.field (by omega) hi8
  refine ⟨inDomain.below, inDomain.table tableDomain, ?_, ?_⟩ <;>
  · have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
    unfold heapEnd at slotHigh
    simp only [OutL, minorFieldsLog, renewLog, domainField, dom, show triggerAddr.toNat = 2147896520 from rfl,
      and_true]
    omega

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
/-- A byte of the domain's ref-table pointers misses everything written before the resets. -/
theorem ptr_byte_out {ent sp ra start trig blk top tr wsize raw : BitVec 64} {off i : Nat}
    (lo : 104 ≤ off) (hi : off + 8 ≤ 128) (hi8 : i < 8)
    (tableDomain : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat)
    (slotHigh : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    EarlierOut ent (minorFieldsLog blk top tr wsize raw) (renewLog sp ra firstDomainPtr start trig)
      (domainField off + i) :=
  domain_byte_out lo (by omega) hi8 tableDomain slotHigh

theorem RefTableSpot.clear_miss {t : BitVec 64} (spot : RefTableSpot t) {a n : Nat}
    (apart : a + n ≤ t.toNat ∨ t.toNat + 56 ≤ a) : OutLRange (tableClearLog t) a n := by
  simp only [tableClearLog, OutLRange, spot.field_nat 40 (by decide), spot.field_nat 48 (by decide), and_true]
  omega

theorem RefTableSpot.reset_miss {t : BitVec 64} (spot : RefTableSpot t) {a n : Nat}
    (apart : a + n ≤ t.toNat ∨ t.toNat + 56 ≤ a) : OutLRange (tableResetLog t) a n := by
  simp only [tableResetLog, OutLRange, spot.field_nat 8 (by decide), spot.field_nat 16 (by decide),
    spot.field_nat 24 (by decide), spot.field_nat 32 (by decide), and_true]
  omega

theorem RefTableSpot.tail_miss {t : BitVec 64} (spot : RefTableSpot t) {a n : Nat}
    (apart : a + n ≤ t.toNat ∨ t.toNat + 56 ≤ a) : OutLRange (tableTailLog t) a n := by
  simp only [tableTailLog, OutLRange, spot.field_nat 8 (by decide), spot.field_nat 16 (by decide),
    spot.field_nat 24 (by decide), spot.field_nat 32 (by decide), and_true]
  omega

/-- A field of the domain record is apart from a table apart from the record. -/
theorem domain_field_apart {t : BitVec 64} {off : Nat} (h : off + 8 ≤ 928)
    (domain : t.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t.toNat) :
    domainField off + 8 ≤ t.toNat ∨ t.toNat + 56 ≤ domainField off := by
  unfold domainField; omega

/-- The base word of one table is apart from another. -/
theorem table_base_apart {t u : BitVec 64} (apart : t.toNat + 56 ≤ u.toNat ∨ u.toNat + 56 ≤ t.toNat) :
    u.toNat + 8 ≤ t.toNat ∨ t.toNat + 56 ≤ u.toNat := by omega

/-- The runtime's globals lie below every table. -/
theorem global_below_table {t : BitVec 64} (spot : RefTableSpot t) {a : Nat} (h : a + 8 ≤ heapStart) :
    a + 8 ≤ t.toNat ∨ t.toNat + 56 ≤ a := Or.inl (Nat.le_trans h spot.low)

/-- The stack lies above every table. -/
theorem stack_above_table {t : BitVec 64} (spot : RefTableSpot t) {a n : Nat} (h : heapEnd ≤ a) :
    a + n ≤ t.toNat ∨ t.toNat + 56 ≤ a := Or.inr (Nat.le_trans spot.high h)

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
/-- A word of the caller's frame misses the young-field stores and the renewal. -/
theorem stack_word_out {sp ra start trig blk top tr wsize raw : BitVec 64} {a : Nat} (high : heapEnd ≤ a)
    (slot : (sp - 16#64 + 8#64).toNat + 8 ≤ a) :
    OutLRange (minorFieldsLog blk top tr wsize raw) a 8 ∧ OutLRange (renewLog sp ra firstDomainPtr start trig) a 8 := by
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at high
  constructor <;> simp only [OutLRange, minorFieldsLog, renewLog, domainField, dom,
    show triggerAddr.toNat = 2147896520 from rfl, and_true] <;> omega

theorem minorSlots_bound {ra s0 s1 s2 s3 v : BitVec 64} {off : Nat} (member : (off, v) ∈ minorSlots ra s0 s1 s2 s3) :
    24 ≤ off ∧ off + 8 ≤ 64 := by
  simp [minorSlots] at member; omega

/-- caml_set_minor_heap_size's frame and what lies below it. -/
structure MinorFrame (sp : BitVec 64) : Prop where
  outer : NativeFrame sp 64
  inner : NativeFrame (nativeStack sp 64) 16
  /-- The callees' scratch lies below. -/
  room : heapEnd + (64 + 16) ≤ sp.toNat

theorem MinorFrame.of {sp : BitVec 64} (frame : NativeFrame sp (64 + (32 + allocHeadroom))) : MinorFrame sp where
  outer := frame.resize (by unfold allocHeadroom; omega) (by decide)
  inner := (frame.nested (front := 64) (by decide)).resize (by unfold allocHeadroom; omega) (by decide)
  room := Nat.le_trans (Nat.add_le_add_left (show 64 + 16 ≤ 64 + (32 + allocHeadroom) by unfold allocHeadroom; decide)
    heapEnd) frame.lower

theorem MinorFrame.slot_high {sp : BitVec 64} (F : MinorFrame sp) (off : Nat) :
    heapEnd ≤ nativeFrameBase sp 64 + off := by
  have := F.room; unfold nativeFrameBase; omega

theorem MinorFrame.stack_le {sp : BitVec 64} (F : MinorFrame sp) (k : Nat) :
    (nativeStack sp 64).toNat ≤ nativeFrameBase sp 64 + k := by
  rw [F.outer.stack_nat]; omega

theorem MinorFrame.renew_slot {sp : BitVec 64} (F : MinorFrame sp) (off : Nat) :
    (nativeStack sp 64 - 16#64 + 8#64).toNat + 8 ≤ nativeFrameBase sp 64 + off := by
  have eq : nativeStack sp 64 - 16#64 + 8#64 = nativeStack (nativeStack sp 64) 16 + BitVec.ofNat 64 8 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rw [eq, show nativeStack (nativeStack sp 64) 16 + BitVec.ofNat 64 8 =
      BitVec.ofNat 64 (nativeFrameBase (nativeStack sp 64) 16 + 8) from F.inner.address 8 (by decide),
    F.inner.slot_nat (by decide)]
  have := F.inner.stack_nat
  have := F.outer.stack_nat
  have := F.inner.lower
  unfold nativeFrameBase at *
  omega

theorem MinorFrame.past_out {sp : BitVec 64} (F : MinorFrame sp) {off i : Nat} (lo : 24 ≤ off) :
    nativeFrameBase sp 64 + 8 + 8 ≤ nativeFrameBase sp 64 + off + i := by omega

/-- Windows that readiness can be carried across (`RuntimeReadyL.window_log`). -/
structure WindowsOk (H : List (Nat × Nat)) (ws : List W) : Prop where
  pins : ∀ pin ∈ VsaIris.Sym.allocText, OutW ws pin.1
  domain : OutWRange ws Layout.sym_Caml_state 8
  pool : OutWRange ws Layout.sym_pool 8
  heap : ∀ a, vsaFoot H a → OutW ws a

/-- caml_memprof_renew_minor_sample's stores: its saved `ra`, the trigger
global, the domain's `young_limit`. -/
def renewWindows (slot : Nat) : List W :=
  [⟨slot, slot + 8⟩, ⟨0x80064cc8, 0x80064cd0⟩, ⟨firstDomainPtr.toNat, firstDomainPtr.toNat + 928⟩]

theorem renewWindows_ok {H : List (Nat × Nat)} {slot : Nat} (high : heapEnd ≤ slot)
    (owned : (firstDomainPtr.toNat, 928) ∈ H) : WindowsOk H (renewWindows slot) := by
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at high
  refine ⟨fun pin member => ?_, ?_, ?_, fun a foot => ?_⟩
  · have source := allocator_sources pin member
    unfold AllocatorByteSource at source
    simp only [OutW, renewWindows, dom, and_true]
    split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega
  · simp only [OutWRange, renewWindows, dom, and_true]; refine ⟨Or.inl ?_, by decide, by decide⟩
    have : Layout.sym_Caml_state + 8 ≤ heapEnd := by decide
    omega
  · simp only [OutWRange, renewWindows, dom, and_true]; refine ⟨Or.inl ?_, by decide, by decide⟩
    have : Layout.sym_pool + 8 ≤ heapEnd := by decide
    omega
  · have apart := block_foot_out (by rw [dom]; decide) owned foot
    simp only [OutW, renewWindows, and_true]
    rw [dom] at apart ⊢
    rcases foot with global | ⟨above, below, _⟩
    · unfold allocGlobal InRange at global; omega
    · have hS : heapStart = 0x8007d140 := rfl
      rw [hS] at above
      rw [hE] at below
      omega

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
theorem renewLog_in {sp ra start trig : BitVec 64} :
    LogInW (renewWindows (sp - 16#64 + 8#64).toNat) (renewLog sp ra firstDomainPtr start trig) := by
  simp only [renewLog, renewWindows, LogInW, InsideW, show triggerAddr.toNat = 0x80064cc8 from rfl]
  exact ⟨Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩, Or.inr (Or.inl ⟨by decide, by decide⟩),
    Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩)), trivial⟩

/-- The windows of live ref-table records. -/
def tableWindows (ts : List (BitVec 64)) : List W := ts.map fun t => ⟨t.toNat, t.toNat + 56⟩

theorem tableWindows_ok {H : List (Nat × Nat)} :
    ∀ (ts : List (BitVec 64)), (∀ t ∈ ts, RefTableSpot t) → (∀ t ∈ ts, (t.toNat, 56) ∈ H) →
      WindowsOk H (tableWindows ts)
  | [], _, _ => ⟨fun _ _ => trivial, trivial, trivial, fun _ _ => trivial⟩
  | t :: ts, spots, owned => by
    have rest := tableWindows_ok ts (fun u m => spots u (List.mem_cons_of_mem _ m))
      (fun u m => owned u (List.mem_cons_of_mem _ m))
    have spot := spots t (List.mem_cons_self ..)
    have low := spot.low
    have stateLow : Layout.sym_Caml_state + 8 ≤ heapStart := by decide
    have poolLow : Layout.sym_pool + 8 ≤ heapStart := by decide
    refine ⟨fun pin m => ⟨?_, rest.pins pin m⟩, ⟨Or.inl (show Layout.sym_Caml_state + 8 ≤ t.toNat by omega), rest.domain⟩,
      ⟨Or.inl (show Layout.sym_pool + 8 ≤ t.toNat by omega), rest.pool⟩,
      fun a foot => ⟨block_foot_out low (owned t (List.mem_cons_self ..)) foot, rest.heap a foot⟩⟩
    have := (arenaWindow_out_pins (n := 56) low pin m)
    simp only [OutW, and_true] at this
    exact this

theorem RefTableSpot.clear_in {t : BitVec 64} (spot : RefTableSpot t) (ts : List (BitVec 64)) :
    LogInW (tableWindows (t :: ts)) (tableClearLog t) := by
  simp only [tableWindows, List.map_cons, tableClearLog, LogInW, InsideW, spot.field_nat 40 (by decide),
    spot.field_nat 48 (by decide), and_true]
  omega

theorem RefTableSpot.tail_in {t : BitVec 64} (spot : RefTableSpot t) (ts : List (BitVec 64)) :
    LogInW (tableWindows (t :: ts)) (tableTailLog t) := by
  simp only [tableWindows, List.map_cons, tableTailLog, LogInW, InsideW, spot.field_nat 8 (by decide),
    spot.field_nat 16 (by decide), spot.field_nat 24 (by decide), spot.field_nat 32 (by decide), and_true]
  omega

theorem RefTableSpot.reset_clear_in {t u : BitVec 64} (spot : RefTableSpot t) (spotU : RefTableSpot u) :
    LogInW (tableWindows [t, u]) (tableResetLog t ++ tableClearLog u) := by
  simp only [tableWindows, List.map_cons, List.map_nil, tableResetLog, tableClearLog, List.cons_append,
    List.nil_append, LogInW, InsideW, spot.field_nat 8 (by decide), spot.field_nat 16 (by decide),
    spot.field_nat 24 (by decide), spot.field_nat 32 (by decide), spotU.field_nat 40 (by decide),
    spotU.field_nat 48 (by decide), and_true]
  omega

/-- The page table's record and slots. -/
def InTable (ent : BitVec 64) (x : Nat) : Prop :=
  (pageTable ≤ x ∧ x < pageTable + 0x28) ∨ (ent.toNat ≤ x ∧ x < ent.toNat + 16384)

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
theorem InTable.late_out {ent sp ra start trig blk top tr wsize raw : BitVec 64} {x : Nat} (inT : InTable ent x)
    (tableDomain : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat)
    (tableLow : ent.toNat + 16384 ≤ heapEnd) (tableHigh : heapStart ≤ ent.toNat)
    (slotHigh : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    OutL (minorFieldsLog blk top tr wsize raw) x ∧ OutL (renewLog sp ra firstDomainPtr start trig) x := by
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  unfold InTable at inT
  unfold heapEnd at tableLow slotHigh
  unfold heapStart at tableHigh
  rw [dom] at tableDomain
  rw [hP] at inT
  constructor <;> simp only [OutL, minorFieldsLog, renewLog, domainField, dom,
    show triggerAddr.toNat = 2147896520 from rfl, and_true] <;> omega

theorem InTable.apart {ent t : BitVec 64} {x : Nat} (inT : InTable ent x) (spot : RefTableSpot t)
    (slots : t.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t.toNat) : x + 1 ≤ t.toNat ∨ t.toNat + 56 ≤ x := by
  have low := spot.low
  have hP : pageTable = 0x800684b8 := rfl
  unfold InTable at inT
  unfold heapStart at low
  rw [hP] at inT
  omega

theorem outL_of_range1 {log : List WEntry} {x : Nat} (h : OutLRange log x 1) : OutL log x :=
  outL_of_range h (Nat.le_refl _) (Nat.lt_succ_self _)

/-- Table facts carry over to memory agreeing on the record and the slots. -/
theorem PageTableFields.window_agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {occ ent : BitVec 64}
    (same : ∀ x, InTable ent x → (m'[x]?).getD 0 = (m[x]?).getD 0) (F : PageTableFields m occ ent) :
    PageTableFields m' occ ent := by
  have record (x : Nat) (lo : pageTable ≤ x) (hi : x < pageTable + 0x28) := same x (Or.inl ⟨lo, hi⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact F.size
  · rw [read4_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact F.shift
  · rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact F.mask
  · rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact F.occupancy
  · rw [word_observed (m := m) _ fun i hi => record _ (by omega) (by omega)]; exact F.entries

theorem slotWord_window_agree {m m' : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64}
    (fits : ent.toNat + 16384 ≤ 2 ^ 64) (same : ∀ x, InTable ent x → (m'[x]?).getD 0 = (m[x]?).getD 0)
    (i : Nat) (hi : i < 2048) : slotWord m' ent i = slotWord m ent i := by
  unfold slotWord
  rw [slotAddr_nat ent i hi fits]
  exact word_observed _ fun k hk => same _ (Or.inr ⟨by omega, by omega⟩)

/-- The first domain's young fields after caml_set_minor_heap_size. -/
structure YoungAt (m : Std.ExtHashMap Nat (BitVec 8)) (blk size raw : BitVec 64) : Prop where
  limit : bytesT m (domainField 0) 8 = blk
  ptr : bytesT m (domainField 8) 8 = blk + size
  base : bytesT m (domainField 24) 8 = raw
  start : bytesT m (domainField 32) 8 = blk
  stop : bytesT m (domainField 40) 8 = blk + size
  allocStart : bytesT m (domainField 48) 8 = blk
  allocEnd : bytesT m (domainField 56) 8 = blk + size
  allocMid : bytesT m (domainField 64) 8 = youngTrigger blk size
  trigger : bytesT m (domainField 72) 8 = blk
  wsize : bytesT m (domainField 80) 8 = size >>> 3

open OCaml.Vm.Primitives.Memprof.RenewMinorSample in
theorem renew_field_miss {sp ra start trig : BitVec 64} {off : Nat} (lo : 8 ≤ off) (hi : off + 8 ≤ 928)
    (slotHigh : heapEnd ≤ (sp - 16#64 + 8#64).toNat) :
    OutLRange (renewLog sp ra firstDomainPtr start trig) (domainField off) 8 := by
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  unfold heapEnd at slotHigh
  simp only [OutLRange, renewLog, domainField, dom, show triggerAddr.toNat = 2147896520 from rfl, and_true]
  omega

/-- The domain's three ref-table records, each still without storage. -/
structure RefTablesAt (H : List (Nat × Nat)) (ent : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (t1 t2 t3 : BitVec 64) : Prop where
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
  /-- Apart from the page table's slots. -/
  slots1 : t1.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t1.toNat
  slots2 : t2.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t2.toNat
  slots3 : t3.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t3.toNat
  owned1 : (t1.toNat, 56) ∈ H
  owned2 : (t2.toNat, 56) ∈ H
  owned3 : (t3.toNat, 56) ∈ H

/-- caml_init_gc calls caml_set_minor_heap_size(size), `size = 4096 n`. -/
structure MinorHeapCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra size s0 s1 s2 s3 ent t1 t2 t3 : BitVec 64)
    (n : Nat) (c : Config) : Prop where
  pc : PCAt 0x8000a23c#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, size), (8, s0), (9, s1), (18, s2), (19, s3)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (64 + (32 + allocHeadroom))
  sizeAt : size = BitVec.ofNat 64 (4096 * n)
  pages : 0 < n
  halfFull : n ≤ 1024
  charged : vsaChg (size + 4096#64).toNat charge
  /-- The minor heap is empty and absent. -/
  idle : bytesT c.σ.mem (domainField 8) 8 = bytesT c.σ.mem (domainField 56) 8
  noYoung : bytesT c.σ.mem (domainField 32) 8 = 0#64
  domainOwned : (firstDomainPtr.toNat, 928) ∈ H
  table : PageTableAt c.σ.mem ent
  tableLow : ent.toNat + 16384 ≤ heapEnd
  tableHigh : heapStart ≤ ent.toNat
  tableOwned : (ent.toNat, 16384) ∈ H
  tableWindows : ∀ i, i < 2048 → WriteWindow (slotAddr ent (BitVec.ofNat 64 i)) 8
  tableDomain : ent.toNat + 16384 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ ent.toNat
  refs : RefTablesAt H ent c.σ.mem t1 t2 t3
  /-- Memprof never started: `lambda = 0.0`, no pending action. -/
  lambdaOff : bytesT c.σ.mem 0x80064cf0 8 = 0#64
  memprofIdle : bytesVal .lw (read8 c.σ.mem 0x80064b30) = 0#64

/-- caml_set_minor_heap_size returned: the minor heap is the block above `raw`
and its `n` pages are in the page table. -/
structure MinorHeapSet (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 size ent : BitVec 64) (n : Nat)
    (raw : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (19, s3), (18, s2), (9, s1), (8, s0), (1, ra), (10, 0#64)]
  ready : RuntimeReady ((raw.toNat, (size + 4096#64).toNat) :: H) capacity sp ra after
  fresh : FreshBlock vsaLayoutP H raw.toNat (size + 4096#64).toNat
  /-- s4–s11 are the caller's. -/
  saved : ∀ k, 20 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  young : YoungAt after.σ.mem (pageAbove raw) size raw
  table : PageTableFields after.σ.mem (BitVec.ofNat 64 n) ent
  count : pageCount after.σ.mem ent.toNat = n
  present : ∀ j, j < n → ∃ i, i < 2048 ∧ slotWord after.σ.mem ent i = 2#64 ||| blockPage (pageAbove raw) j
  only : ∀ i, i < 2048 → slotWord after.σ.mem ent i ≠ 0#64 →
    ∃ j, j < n ∧ slotWord after.σ.mem ent i = 2#64 ||| blockPage (pageAbove raw) j
  /-- Domain fields from `mark_stack` on are the caller's. -/
  domainHigh : ∀ off, 128 ≤ off → off + 8 ≤ 928 →
    bytesT after.σ.mem (domainField off) 8 = bytesT before.σ.mem (domainField off) 8
  /-- Below the arena, outside the allocator's globals, the table's occupancy and
  memprof's trigger, memory is the caller's. -/
  lowKept : ∀ x, x < heapStart → ¬ allocGlobal x → (x < pageTable + 0x18 ∨ pageTable + 0x20 ≤ x) →
    (x < 0x80064cc8 ∨ 0x80064cc8 + 8 ≤ x) → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  /-- The caller's frame and everything above it are untouched. -/
  caller : ∀ x, sp.toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem minor_heap_set (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra size s0 s1 s2 s3 ent t1 t2 t3 : BitVec 64) (n : Nat)
    (A : MinorHeapCall H capacity charge sp ra size s0 s1 s2 s3 ent t1 t2 t3 n c) :
    ∃ raw after, Steps c after ∧ MinorHeapSet H capacity sp ra s0 s1 s2 s3 size ent n raw c after := by
  have frame64 : NativeFrame sp 64 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 64) (32 + allocHeadroom) := A.frame.nested (front := 64) (by decide)
  have frame144 : NativeFrame (nativeStack sp 64) 144 := frameIn.resize (by unfold allocHeadroom; omega) (by decide)
  have stackNat : (nativeStack sp 64).toNat = sp.toNat - 64 := frame64.stack_nat
  have base64 : nativeFrameBase sp 64 = sp.toNat - 64 := rfl
  have spLow := A.frame.lower
  have regs := A.regs
  have fits64 : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans A.tableLow (by decide)
  -- addi sp, sp, -64
  obtain ⟨d1, run1, p1⟩ := (minor_frame c sp ra size A.ready.toLeafInput
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 10) _ regs rfl, trivial⟩).run c ⟨A.pc, rfl⟩
  -- discipline: allow(O8-hand-gpr-frame) landed before GprsSame; migrate when this composition is next touched
  have keep1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [2]) : gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready1 : RuntimeReady H (capacity + charge) (nativeStack sp 64) ra d1 :=
    A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p1.regs rfl)
      ((keep1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg) A.ready.aligned frame64
      (by simp only [LogInW])
  -- save s1, s2, ra, s0, s3
  obtain ⟨d2, run2, p2⟩ := (minor_save d1 sp ra s0 s1 s2 s3 size ready1.toLeafInput frame64
    ⟨(keep1 9 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ regs rfl),
      gholds_lookup (n := 2) _ p1.regs rfl,
      (keep1 18 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 18) _ regs rfl),
      (keep1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg,
      (keep1 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ regs rfl),
      (keep1 19 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 19) _ regs rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have inside2 : LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (nativeWordLog sp 64 (minorSlots ra s0 s1 s2 s3)) :=
    frame64.word_log_inside fun off value member => by simp [minorSlots] at member; omega
  have ready2 : RuntimeReady H (capacity + charge) (nativeStack sp 64) ra d2 :=
    ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p2.regs rfl)
      (gholds_lookup (n := 1) _ p2.regs rfl) A.ready.aligned frame64 inside2
  -- below the frame, d2 is c
  have low2 (x : Nat) (hx : x < nativeFrameBase sp 64) : (d2.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p2.memory, frameOn_writeLog _ _ _ inside2 x ⟨Or.inl hx, trivial⟩, p1.memory]; rfl
  have domainLow : firstDomainPtr.toNat + 928 ≤ nativeFrameBase sp 64 := by
    have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
    have hE : heapEnd = 0x86800000 := rfl
    rw [base64, dom]; unfold allocHeadroom at spLow; rw [hE] at spLow; omega
  have field2 (off : Nat) (h : off + 8 ≤ 928) : bytesT d2.σ.mem (domainField off) 8 = bytesT c.σ.mem (domainField off) 8 :=
    word_observed _ fun i hi => low2 _ (by unfold domainField; omega)
  -- s1 = &Caml_state, s2 = size; the minor heap is empty
  obtain ⟨d3, run3, p3⟩ := (minor_state d2 ra size ready2.toLeafInput ⟨gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩
    ready2.domainWord (by rw [field2 8 (by decide), field2 56 (by decide)]; exact A.idle)).run d2 ⟨p2.pc, rfl⟩
  have keep3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [9, 15, 18, 13, 14]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready3 : RuntimeReady H (capacity + charge) (nativeStack sp 64) ra d3 :=
    ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep3 2 (by decide) (by decide) (by decide)).trans ready2.stack)
      ((keep3 1 (by decide) (by decide) (by decide)).trans ready2.raReg) A.ready.aligned frame64 (by simp only [LogInW])
  -- caml_stat_alloc_aligned_noexc(size, 0, &raw)
  obtain ⟨d4, run4, p4⟩ := (minor_alloc_call d3 sp ra size size ready3.toLeafInput
    ⟨(keep3 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ p2.regs rfl),
      gholds_lookup (n := 18) _ p3.regs rfl, gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩).run d3 ⟨p3.pc, rfl⟩
  have keep4 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [12, 11, 10] ++ [1]) : gprGet d4.σ r = gprGet d3.σ r :=
    p4.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready4 : RuntimeReady H (capacity + charge) (nativeStack sp 64) jal_8000a290_call.link d4 :=
    ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep4 2 (by decide) (by decide) (by decide)).trans ready3.stack) (gholds_lookup (n := 1) _ p4.regs rfl)
      (by decide) frame64 (by simp only [LogInW])
  obtain ⟨raw, d5, run5, D⟩ := stat_alloc_aligned d4 H capacity charge (nativeStack sp 64) jal_8000a290_call.link
    size (nativeStack sp 64 + 8#64) sp 64 8 {
      pc := by rw [← jal_8000a290_call_target]; exact p4.pc
      regs := ⟨gholds_lookup (n := 2) _ p4.regs rfl, gholds_lookup (n := 1) _ p4.regs rfl,
        gholds_lookup (n := 10) _ p4.regs rfl, gholds_lookup (n := 11) _ p4.regs rfl,
        gholds_lookup (n := 12) _ p4.regs rfl, trivial⟩
      ready := ready4
      frame := frameIn
      charged := A.charged
      outFrame := frame64
      outAt := rfl
      outBound := by decide
      outAligned := by decide
      outAbove := by rw [stackNat, base64]; exact Nat.le_refl _ }
  have fresh := D.fresh
  have rawLo : heapStart ≤ raw.toNat := fresh.2.1
  have rawHi : raw.toNat + (size + 4096#64).toNat ≤ heapEnd := fresh.2.2.1
  have sizeNat : size.toNat = 4096 * n := by
    rw [A.sizeAt, BitVec.toNat_ofNat]; have := A.halfFull; exact Nat.mod_eq_of_lt (by omega)
  have bigNat : (size + 4096#64).toNat = 4096 * n + 4096 := by
    rw [BitVec.toNat_add, sizeNat]; have := A.halfFull; simp only [BitVec.toNat_ofNat]; omega
  rw [bigNat] at rawHi
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  rw [hE] at rawHi
  rw [hS] at rawLo
  have inside := pageAbove_inside raw (4096 * n) (by omega)
  generalize hblk : pageAbove raw = blk at inside
  have blkRegs : gprGet d5.σ 10 = some blk := by rw [← hblk]; exact gholds_lookup (n := 10) _ D.regs rfl
  have blkAligned : blk.toNat % 4096 = 0 := inside.2.2
  have blkFits : blk.toNat + 4096 * n < 2 ^ 64 := by omega
  have blkNonzero : blk ≠ 0#64 := fun h => by rw [h] at inside; simp at inside
  -- caml_page_table_add(In_young, blk, blk + size)
  have saved5 (k : Nat) (member : k ∈ abiSaved) : gprGet d5.σ k = gprGet d4.σ k := D.saved k member
  obtain ⟨d6, run6, p6⟩ := (minor_add_call d5 jal_8000a290_call.link blk size D.ready.toLeafInput
    ⟨blkRegs, (saved5 18 (by decide)).trans ((keep4 18 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 18) _ p3.regs rfl)), trivial⟩ blkNonzero).run d5 ⟨D.pc, rfl⟩
  have keep6 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [8, 19, 11, 12, 10] ++ [1]) :
      gprGet d6.σ r = gprGet d5.σ r :=
    p6.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready6 : RuntimeReady ((raw.toNat, (size + 4096#64).toNat) :: H) capacity (nativeStack sp 64)
      jal_8000a2ac_call.link d6 :=
    D.ready.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep6 2 (by decide) (by decide) (by decide)).trans D.ready.stack) (gholds_lookup (n := 1) _ p6.regs rfl)
      (by decide) frame64 (by simp only [LogInW])
  -- the table is still the cleared one
  have tableKept (x : Nat) (out : ¬ vsaFoot H x) (low : x < heapEnd) :
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p6.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl,
      D.kept x (by rw [stackNat]; rw [hE] at low; unfold allocHeadroom at spLow ⊢; rw [hE] at spLow; omega) out,
      p4.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, p3.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl,
      low2 x (by rw [base64]; rw [hE] at low; unfold allocHeadroom at spLow; rw [hE] at spLow; omega)]
  have table6 : PageTableAt d6.σ.mem ent := A.table.agree
    (fun x lo hi => tableKept x (pageTable_record_not_foot lo hi) (by
      have : pageTable + 0x28 ≤ heapEnd := by decide
      omega))
    (fun x lo hi => tableKept x (owned_not_foot' A.tableHigh A.tableOwned lo hi) (by have := A.tableLow; omega))
  have count6 := table6.count fits64
  obtain ⟨d7, run7, PA⟩ := page_table_add d6 ((raw.toNat, (size + 4096#64).toNat) :: H) capacity
    (nativeStack sp 64) jal_8000a2ac_call.link 2#64 blk (blk + size) blk (BitVec.ofNat 64 Layout.sym_Caml_state) size
    (blk + size) blk ent n {
      pc := by rw [← jal_8000a2ac_call_target]; exact p6.pc
      regs := ⟨(keep6 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ D.regs rfl),
        gholds_lookup (n := 1) _ p6.regs rfl, gholds_lookup (n := 10) _ p6.regs rfl,
        gholds_lookup (n := 11) _ p6.regs rfl, gholds_lookup (n := 12) _ p6.regs rfl,
        gholds_lookup (n := 8) _ p6.regs rfl,
        (keep6 9 (by decide) (by decide) (by decide)).trans ((saved5 9 (by decide)).trans
          ((keep4 9 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ p3.regs rfl))),
        gholds_lookup (n := 18) _ p6.regs rfl, gholds_lookup (n := 19) _ p6.regs rfl, trivial⟩
      ready := ready6
      first := block_first blk blkAligned
      last := by rw [A.sizeAt]; exact block_last blk n A.pages blkAligned blkFits
      nonempty := A.pages
      fields := table6.fields fits64
      span := {
        frame := frame144
        aligned := blkAligned
        fits := blkFits
        small := by decide
        kindNonzero := by decide
        room := by rw [count6]; have := A.halfFull; omega
        windows := A.tableWindows
        tableLow := A.tableLow
        tableHigh := A.tableHigh
        tableOwned := List.mem_cons_of_mem _ A.tableOwned
        disjoint := fun i hi occupied => absurd (table6.slot_zero fits64 i hi) occupied } }
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  -- the domain record is untouched so far
  have domain7 (off : Nat) (h : off + 8 ≤ 928) :
      bytesT d7.σ.mem (domainField off) 8 = bytesT c.σ.mem (domainField off) 8 := by
    apply word_observed
    intro i hi
    have inDomain := InDomain.field h hi
    rw [PA.kept _ inDomain.below (inDomain.table A.tableDomain),
      tableKept _ (inDomain.not_foot A.domainOwned) inDomain.below]
  have outNat : (nativeStack sp 64 + 8#64).toNat = nativeFrameBase sp 64 + 8 := by
    rw [nativeStack, frame64.address _ (by decide)]; exact frame64.slot_nat (by decide)
  have rawSlot7 : bytesT d7.σ.mem (nativeFrameBase sp 64 + 8) 8 = raw := by
    rw [word_observed (m := d5.σ.mem) _ fun i hi => by
      rw [PA.caller _ (by rw [stackNat, base64] at *; omega), p6.memory]; rfl, ← outNat]
    exact D.stored
  -- no previous minor heap to remove
  obtain ⟨d8, run8, p8⟩ := (minor_check d7 jal_8000a2ac_call.link PA.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ PA.regs rfl, gholds_lookup (n := 9) _ PA.regs rfl, trivial⟩ PA.ready.domainWord
    (by rw [domain7 32 (by decide)]; exact A.noYoung)).run d7 ⟨PA.pc, rfl⟩
  have keep8 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15, 11]) : gprGet d8.σ r = gprGet d7.σ r :=
    p8.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready8 := PA.ready.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    ((keep8 2 (by decide) (by decide) (by decide)).trans PA.ready.stack)
    ((keep8 1 (by decide) (by decide) (by decide)).trans PA.ready.raReg) PA.ready.aligned frame64
    (by simp only [LogInW])
  -- raw, the trigger, the size in words
  obtain ⟨d9, run9, p9⟩ := (minor_fields d8 sp jal_8000a2ac_call.link blk size raw 0#64 ready8.toLeafInput frame64
    ⟨(keep8 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ PA.regs rfl),
      (keep8 18 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 18) _ PA.regs rfl),
      (keep8 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ PA.regs rfl),
      gholds_lookup (n := 10) _ p8.regs rfl, trivial⟩
    (by rw [p8.memory]; exact rawSlot7)).run d8 ⟨p8.pc, rfl⟩
  have keep9 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [13, 14, 18]) : gprGet d9.σ r = gprGet d8.σ r :=
    p9.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready9 := ready8.stack_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
    ((keep9 2 (by decide) (by decide) (by decide)).trans ready8.stack)
    ((keep9 1 (by decide) (by decide) (by decide)).trans ready8.raReg) ready8.aligned frame64
    (by simp only [LogInW])
  -- the young fields, then caml_memprof_renew_minor_sample
  obtain ⟨d10, run10, p10⟩ := (minor_stores_call d9 jal_8000a2ac_call.link blk (blk + size) (youngTrigger blk size)
    (size >>> 3) raw 0#64 ready9.toLeafInput
    ⟨gholds_lookup (n := 8) _ p9.regs rfl,
      (keep9 15 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 15) _ p8.regs rfl),
      (keep9 19 (by decide) (by decide) (by decide)).trans ((keep8 19 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 19) _ PA.regs rfl)),
      gholds_lookup (n := 14) _ p9.regs rfl, gholds_lookup (n := 18) _ p9.regs rfl,
      gholds_lookup (n := 13) _ p9.regs rfl, gholds_lookup (n := 10) _ p9.regs rfl, trivial⟩).run d9 ⟨p9.pc, rfl⟩
  have keep10 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [] ++ [1]) : gprGet d10.σ r = gprGet d9.σ r :=
    p10.toEffectPost.gpr_frame (by decide) r lo hi out
  have domainWindows : LogInW [⟨firstDomainPtr.toNat, firstDomainPtr.toNat + 928⟩]
      (minorFieldsLog blk (blk + size) (youngTrigger blk size) (size >>> 3) raw) := by
    simp only [LogInW, InsideW, minorFieldsLog, domainField, dom, and_true]
    omega
  have ready10 : RuntimeReady ((raw.toNat, (size + 4096#64).toNat) :: H) capacity (nativeStack sp 64)
      jal_8000a314_call.link d10 :=
    ready9.window_log p10 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep10 2 (by decide) (by decide) (by decide)).trans ready9.stack) (gholds_lookup (n := 1) _ p10.regs rfl)
      (by decide) domainWindows (fun pin member => arenaWindow_out_pins (by rw [hS, dom]; decide) pin member)
      (by simp only [OutWRange, dom, and_true]; decide) (by simp only [OutWRange, dom, and_true]; decide)
      (fun a foot => by
        have := block_foot_out (by rw [hS, dom]; decide) (List.mem_cons_of_mem _ A.domainOwned) foot
        simp only [OutW, and_true]; exact this)
  -- runtime globals below the arena are still the caller's
  have low10 (x : Nat) (hx : x < heapStart) (global : ¬ allocGlobal x) (occ : x < pageTable + 0x18 ∨ pageTable + 0x20 ≤ x) :
      (d10.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have hx' : x < firstDomainPtr.toNat := by rw [dom]; rw [hS] at hx; omega
    have below : x < heapEnd := by rw [hE]; rw [hS] at hx; omega
    rw [p10.memory, frameOn_writeLog _ _ _ domainWindows x ⟨Or.inl hx', trivial⟩, p9.memory,
      show writeLog d8.σ.mem [] = d8.σ.mem from rfl, p8.memory, show writeLog d7.σ.mem [] = d7.σ.mem from rfl,
      PA.kept x below (by simp only [OutW, and_true]; refine ⟨occ, Or.inl ?_⟩; have := A.tableHigh; omega),
      tableKept x (fun foot => by
        rcases foot with g | ⟨above, _, _⟩
        · exact global g
        · omega) below]
  have lowWord (a : Nat) (hx : a + 8 ≤ heapStart) (global : ∀ i, i < 8 → ¬ allocGlobal (a + i))
      (occ : a + 8 ≤ pageTable + 0x18 ∨ pageTable + 0x20 ≤ a) : read8 d10.σ.mem a = read8 c.σ.mem a :=
    read8_agree fun i hi => low10 _ (by omega) (global i hi) (by omega)
  have notGlobal (a : Nat) (lo : 0x8007ca38 ≤ a ∨ (0x80064d4c ≤ a ∧ a + 8 ≤ 0x8007c9e8) ∨
      (0x8006466c ≤ a ∧ a + 8 ≤ 0x800648e8) ∨ (0x80064938 ≤ a ∧ a + 8 ≤ 0x80064d20)) (i : Nat) (hi : i < 8) :
      ¬ allocGlobal (a + i) := by
    unfold allocGlobal InRange; omega
  have entry10 : jal_8000a314_call.target = 0x80029558#64 := jal_8000a314_call_target
  have slotEq : nativeStack sp 64 - 16#64 + 8#64 = nativeStack (nativeStack sp 64) 16 + BitVec.ofNat 64 8 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  have frame16 : NativeFrame (nativeStack sp 64) 16 := frameIn.resize (by unfold allocHeadroom; omega) (by decide)
  have fieldsAt (i : Nat) (off : Nat) (v : BitVec 64)
      (entry : (minorFieldsLog blk (blk + size) (youngTrigger blk size) (size >>> 3) raw)[i]? = some (domainField off, 8, v))
      (later : OutLRange ((minorFieldsLog blk (blk + size) (youngTrigger blk size) (size >>> 3) raw).drop (i + 1))
        (domainField off) 8) :
      bytesT d10.σ.mem (domainField off) 8 = v := by
    rw [p10.memory]; exact word_writeLog_at _ _ i _ _ entry later
  have slotHigh : heapEnd ≤ (nativeStack sp 64 - 16#64 + 8#64).toNat := by
    rw [slotEq]; exact frame16.slot_above (by decide)
  obtain ⟨d11, run11, R⟩ := OCaml.Vm.Primitives.Memprof.RenewMinorSample.renew_summary
    (ra := jal_8000a314_call.link) (sp := nativeStack sp 64) (dom := firstDomainPtr) (start := blk) (trig := blk)
    (c := d10) {
      leaf := ready10.toLeafInput
      pc := by rw [← entry10]; exact p10.pc
      stack := ready10.stack
      a0 := by rw [gholds_lookup (n := 10) _ p10.regs rfl]; rfl
      lambda := by
        rw [show (2147896560#64).toNat = 0x80064cf0 from rfl, lowWord _ (by decide)
          (notGlobal _ (Or.inr (Or.inr (Or.inr (by decide))))) (by decide), read8_value]
        exact A.lambdaOff
      domainWord := by rw [read8_value]; exact ready10.domainWord
      startWord := by
        rw [read8_value]
        exact fieldsAt 1 48 blk rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      triggerWord := by
        rw [read8_value]
        exact fieldsAt 2 72 blk rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      idle := by
        rw [show (2147896112#64).toNat = 0x80064b30 from rfl, lowWord _ (by decide)
          (notGlobal _ (Or.inr (Or.inr (Or.inr (by decide))))) (by decide)]
        exact A.memprofIdle
      slot := by rw [slotEq, nativeStack, frame16.address _ (by decide)]; exact frame16.word (by decide) (by decide)
      startWindow := by constructor <;> decide
      triggerWindow := by constructor <;> decide
      limitWindow := by constructor <;> decide
      image := renew_log_outside slotHigh
      slotApart := renew_slot_apart slotHigh
      triggerApart := by simp only [OutLRange]; decide }
  have frameR (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [1, 2, 10, 11, 12, 13, 14, 15, 16, 17]) :
      gprGet d11.σ r = gprGet d10.σ r := R.frame r lo hi out
  -- the ref tables and their pointers are still the caller's
  have kept11 (x : Nat) (notFoot : ¬ vsaFoot H x)
      (out : EarlierOut ent (minorFieldsLog blk (blk + size) (youngTrigger blk size) (size >>> 3) raw)
        (OCaml.Vm.Primitives.Memprof.RenewMinorSample.renewLog (nativeStack sp 64) jal_8000a314_call.link
          firstDomainPtr blk blk) x) :
      (d11.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [R.memory, writeLog_out _ _ _ out.renew, p10.memory, writeLog_out _ _ _ out.fields, p9.memory,
      show writeLog d8.σ.mem [] = d8.σ.mem from rfl, p8.memory, show writeLog d7.σ.mem [] = d7.σ.mem from rfl,
      PA.kept x out.below out.tables, tableKept x notFoot out.below]
  have refs := A.refs
  have tableWord {t : BitVec 64} (spot : RefTableSpot t) (owned : (t.toNat, 56) ∈ H)
      (domain : t.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t.toNat)
      (slots : t.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t.toNat) :
      bytesT d11.σ.mem t.toNat 8 = bytesT c.σ.mem t.toNat 8 :=
    word_observed _ fun i hi => kept11 _ (owned_not_foot' spot.low owned (by omega) (by have := spot.high; omega))
      (spot.byte_out (by omega) (by omega) domain slots slotHigh)
  have ptrWord (off : Nat) (lo : 104 ≤ off) (hi : off + 8 ≤ 128) :
      bytesT d11.σ.mem (domainField off) 8 = bytesT c.σ.mem (domainField off) 8 :=
    word_observed _ fun i hi8 => kept11 _ ((InDomain.field (by omega) hi8).not_foot A.domainOwned)
      (ptr_byte_out lo hi hi8 A.tableDomain slotHigh)
  have domain11 : bytesT d11.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr := by
    rw [R.memory, bytesT_writeLog_out _ (by
      simp only [OCaml.Vm.Primitives.Memprof.RenewMinorSample.renewLog, OutLRange, and_true]
      exact ⟨Or.inl (Nat.le_trans (by decide) slotHigh), by decide, by decide⟩)]
    exact ready10.domainWord
  -- ref_table
  obtain ⟨d12, run12, p12⟩ := (minor_ref_first d11 jal_8000a314_call.link t1 blk R.leaf
    ⟨(frameR 9 (by decide) (by decide) (by decide)).trans ((keep10 9 (by decide) (by decide) (by decide)).trans
      ((keep9 9 (by decide) (by decide) (by decide)).trans ((keep8 9 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 9) _ PA.regs rfl)))),
      (frameR 8 (by decide) (by decide) (by decide)).trans ((keep10 8 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 8) _ p9.regs rfl)), trivial⟩
    domain11 (by rw [ptrWord 104 (by decide) (by decide)]; exact refs.ptr1) refs.spot1
    (by rw [tableWord refs.spot1 refs.owned1 refs.domain1 refs.slots1]; exact refs.empty1)).run d11 ⟨R.pc, rfl⟩
  have leaf12 : LeafInput jal_8000a314_call.link d12 := ⟨p12.good, p12.image, p12.minstret,
    (p12.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans R.leaf.raReg,
    R.leaf.aligned, p12.tick⟩
  have stateLow : Layout.sym_Caml_state + 8 ≤ heapStart := by decide
  have mem12 : d12.σ.mem = writeLog d11.σ.mem (tableClearLog t1) := p12.memory
  -- ref_table's remaining fields; ephe_ref_table
  obtain ⟨d13, run13, p13⟩ := (minor_ref_second d12 jal_8000a314_call.link t1 t2 leaf12
    ⟨gholds_lookup (n := 8) _ p12.regs rfl, gholds_lookup (n := 9) _ p12.regs rfl, trivial⟩
    (by rw [mem12, bytesT_writeLog_out _ (refs.spot1.clear_miss (global_below_table refs.spot1 stateLow))]
        exact domain11)
    (by rw [mem12, bytesT_writeLog_out _ (refs.spot1.clear_miss (domain_field_apart (by decide) refs.domain1)),
          ptrWord 112 (by decide) (by decide)]
        exact refs.ptr2)
    refs.spot1 refs.spot2
    (by rw [mem12, bytesT_writeLog_out _ (refs.spot1.clear_miss (table_base_apart refs.apart12)),
          tableWord refs.spot2 refs.owned2 refs.domain2 refs.slots2]
        exact refs.empty2)
    refs.apart12 refs.domain1).run d12 ⟨p12.pc, rfl⟩
  have mem13 : d13.σ.mem = writeLog (writeLog (writeLog d11.σ.mem (tableClearLog t1)) (tableResetLog t1))
      (tableClearLog t2) := by rw [p13.memory, mem12, writeLog_append]
  have leaf13 : LeafInput jal_8000a314_call.link d13 := ⟨p13.good, p13.image, p13.minstret,
    (p13.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans leaf12.raReg,
    R.leaf.aligned, p13.tick⟩
  -- ephe_ref_table's remaining fields; custom_table
  obtain ⟨d14, run14, p14⟩ := (minor_ref_third d13 jal_8000a314_call.link t2 t3 leaf13
    ⟨gholds_lookup (n := 8) _ p13.regs rfl, gholds_lookup (n := 9) _ p13.regs rfl, trivial⟩
    (by rw [mem13, bytesT_writeLog_out _ (refs.spot2.clear_miss (global_below_table refs.spot2 stateLow)),
          bytesT_writeLog_out _ (refs.spot1.reset_miss (global_below_table refs.spot1 stateLow)),
          bytesT_writeLog_out _ (refs.spot1.clear_miss (global_below_table refs.spot1 stateLow))]
        exact domain11)
    (by rw [mem13, bytesT_writeLog_out _ (refs.spot2.clear_miss (domain_field_apart (by decide) refs.domain2)),
          bytesT_writeLog_out _ (refs.spot1.reset_miss (domain_field_apart (by decide) refs.domain1)),
          bytesT_writeLog_out _ (refs.spot1.clear_miss (domain_field_apart (by decide) refs.domain1)),
          ptrWord 120 (by decide) (by decide)]
        exact refs.ptr3)
    refs.spot2 refs.spot3
    (by rw [mem13, bytesT_writeLog_out _ (refs.spot2.clear_miss (table_base_apart refs.apart23)),
          bytesT_writeLog_out _ (refs.spot1.reset_miss (table_base_apart refs.apart13)),
          bytesT_writeLog_out _ (refs.spot1.clear_miss (table_base_apart refs.apart13)),
          tableWord refs.spot3 refs.owned3 refs.domain3 refs.slots3]
        exact refs.empty3)
    refs.apart23 refs.domain2).run d13 ⟨p13.pc, rfl⟩
  have leaf14 : LeafInput jal_8000a314_call.link d14 := ⟨p14.good, p14.image, p14.minstret,
    (p14.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans leaf13.raReg,
    R.leaf.aligned, p14.tick⟩
  -- custom_table's remaining fields
  obtain ⟨d15, run15, p15⟩ := (minor_ref_last d14 jal_8000a314_call.link t3 0#64 leaf14
    ⟨gholds_lookup (n := 8) _ p14.regs rfl, gholds_lookup (n := 10) _ p14.regs rfl, trivial⟩ refs.spot3).run d14
    ⟨p14.pc, rfl⟩
  -- the saved registers are where minor_save put them
  have MF : MinorFrame sp := MinorFrame.of A.frame
  have saved15 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ minorSlots ra s0 s1 s2 s3) :
      bytesT d15.σ.mem (nativeFrameBase sp 64 + off) 8 = value := by
    have bound := minorSlots_bound member
    have high := MF.slot_high off
    have miss := stack_word_out (sp := nativeStack sp 64) (ra := jal_8000a314_call.link) (start := blk) (trig := blk)
      (blk := blk) (top := blk + size) (tr := youngTrigger blk size) (wsize := size >>> 3) (raw := raw) high
      (MF.renew_slot off)
    rw [p15.memory, bytesT_writeLog_out _ (refs.spot3.tail_miss (stack_above_table refs.spot3 high)), p14.memory,
      writeLog_append, bytesT_writeLog_out _ (refs.spot3.clear_miss (stack_above_table refs.spot3 high)),
      bytesT_writeLog_out _ (refs.spot2.reset_miss (stack_above_table refs.spot2 high)), mem13,
      bytesT_writeLog_out _ (refs.spot2.clear_miss (stack_above_table refs.spot2 high)),
      bytesT_writeLog_out _ (refs.spot1.reset_miss (stack_above_table refs.spot1 high)),
      bytesT_writeLog_out _ (refs.spot1.clear_miss (stack_above_table refs.spot1 high)), R.memory,
      bytesT_writeLog_out _ miss.2, p10.memory, bytesT_writeLog_out _ miss.1, p9.memory,
      show writeLog d8.σ.mem [] = d8.σ.mem from rfl, p8.memory, show writeLog d7.σ.mem [] = d7.σ.mem from rfl]
    rw [word_observed (m := d2.σ.mem) _ fun i hi => by
      rw [PA.caller (nativeFrameBase sp 64 + off + i) (Nat.le_trans (MF.stack_le off) (Nat.le_add_right _ _)), p6.memory,
        show writeLog d5.σ.mem [] = d5.σ.mem from rfl,
        D.caller (nativeFrameBase sp 64 + off + i) (Nat.le_trans (MF.stack_le off) (Nat.le_add_right _ _)) (Or.inr (by rw [outNat]; exact MF.past_out bound.1)),
        p4.memory,
        show writeLog d3.σ.mem [] = d3.σ.mem from rfl, p3.memory]; rfl, p2.memory]
    exact frame64.word_log_read (fun o w h => (minorSlots_bound h).2) (by simp [minorSlots]) _ member
  have g12 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15, 8, 10]) : gprGet d12.σ r = gprGet d11.σ r :=
    p12.toEffectPost.gpr_frame (by decide) r lo hi out
  have g13 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [14, 8, 10]) : gprGet d13.σ r = gprGet d12.σ r :=
    p13.toEffectPost.gpr_frame (by decide) r lo hi out
  have g14 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [14, 8, 10]) : gprGet d14.σ r = gprGet d13.σ r :=
    p14.toEffectPost.gpr_frame (by decide) r lo hi out
  have g15 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ []) : gprGet d15.σ r = gprGet d14.σ r :=
    p15.toEffectPost.gpr_frame (by decide) r lo hi out
  have leaf15 : LeafInput jal_8000a314_call.link d15 :=
    ⟨p15.good, p15.image, p15.minstret, (g15 1 (by decide) (by decide) (by decide)).trans leaf14.raReg,
      R.leaf.aligned, p15.tick⟩
  have stack15 : gprGet d15.σ 2 = some (nativeStack sp 64) :=
    (g15 2 (by decide) (by decide) (by decide)).trans ((g14 2 (by decide) (by decide) (by decide)).trans
      ((g13 2 (by decide) (by decide) (by decide)).trans ((g12 2 (by decide) (by decide) (by decide)).trans R.stack)))
  -- restore and return
  obtain ⟨d16, run16, p16⟩ := (minor_return d15 sp ra s0 s1 s2 s3 0#64 jal_8000a314_call.link leaf15 frame64
    ⟨stack15, gholds_lookup (n := 10) _ p15.regs rfl, trivial⟩ saved15 A.ready.aligned).run d15 ⟨p15.pc, rfl⟩
  -- readiness through the renewal and the resets
  have ready11 : RuntimeReady ((raw.toNat, (size + 4096#64).toNat) :: H) capacity (nativeStack sp 64)
      jal_8000a314_call.link d11 :=
    have W := renewWindows_ok (H := (raw.toNat, (size + 4096#64).toNat) :: H) slotHigh
      (List.mem_cons_of_mem _ A.domainOwned)
    ready10.of_kept R.leaf R.stack R.kept R.htif R.memory renewLog_in W.pins W.domain W.pool W.heap
  have own (t : BitVec 64) (owned : (t.toNat, 56) ∈ H) : (t.toNat, 56) ∈ (raw.toNat, (size + 4096#64).toNat) :: H :=
    List.mem_cons_of_mem _ owned
  have W1 := tableWindows_ok (H := (raw.toNat, (size + 4096#64).toNat) :: H) [t1]
    (fun _ m => by rw [List.mem_singleton] at m; subst m; exact refs.spot1)
    (fun _ m => by rw [List.mem_singleton] at m; subst m; exact own _ refs.owned1)
  have W12 := tableWindows_ok (H := (raw.toNat, (size + 4096#64).toNat) :: H) [t1, t2]
    (fun _ m => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl <;> first | exact refs.spot1 | exact refs.spot2)
    (fun _ m => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl <;> first | exact own _ refs.owned1 | exact own _ refs.owned2)
  have W23 := tableWindows_ok (H := (raw.toNat, (size + 4096#64).toNat) :: H) [t2, t3]
    (fun _ m => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl <;> first | exact refs.spot2 | exact refs.spot3)
    (fun _ m => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl <;> first | exact own _ refs.owned2 | exact own _ refs.owned3)
  have W3 := tableWindows_ok (H := (raw.toNat, (size + 4096#64).toNat) :: H) [t3]
    (fun _ m => by rw [List.mem_singleton] at m; subst m; exact refs.spot3)
    (fun _ m => by rw [List.mem_singleton] at m; subst m; exact own _ refs.owned3)
  have ready12 := ready11.window_log p12 (by decide) (by simp only [keysG]; decide) (by decide)
    ((g12 2 (by decide) (by decide) (by decide)).trans ready11.stack)
    ((g12 1 (by decide) (by decide) (by decide)).trans ready11.raReg) ready11.aligned (refs.spot1.clear_in [])
    W1.pins W1.domain W1.pool W1.heap
  have ready13 := ready12.window_log p13 (by decide) (by simp only [keysG]; decide) (by decide)
    ((g13 2 (by decide) (by decide) (by decide)).trans ready12.stack)
    ((g13 1 (by decide) (by decide) (by decide)).trans ready12.raReg) ready12.aligned
    (refs.spot1.reset_clear_in refs.spot2) W12.pins W12.domain W12.pool W12.heap
  have ready14 := ready13.window_log p14 (by decide) (by simp only [keysG]; decide) (by decide)
    ((g14 2 (by decide) (by decide) (by decide)).trans ready13.stack)
    ((g14 1 (by decide) (by decide) (by decide)).trans ready13.raReg) ready13.aligned
    (refs.spot2.reset_clear_in refs.spot3) W23.pins W23.domain W23.pool W23.heap
  have ready15 := ready14.window_log p15 (by decide) (by simp only [keysG]; decide) (by decide)
    ((g15 2 (by decide) (by decide) (by decide)).trans ready14.stack)
    ((g15 1 (by decide) (by decide) (by decide)).trans ready14.raReg) ready14.aligned
    (refs.spot3.tail_in []) W3.pins W3.domain W3.pool W3.heap
  have ready16 := ready15.stack_log p16 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p16.regs rfl) (gholds_lookup (n := 1) _ p16.regs rfl) A.ready.aligned frame64
    (by simp only [LogInW])
  -- after the resets, the table is as caml_page_table_add left it
  have mem14 : d14.σ.mem = writeLog (writeLog d13.σ.mem (tableResetLog t2)) (tableClearLog t3) := by
    rw [p14.memory, writeLog_append]
  have late (x : Nat) (inT : InTable ent x) : (d16.σ.mem[x]?).getD 0 = (d7.σ.mem[x]?).getD 0 := by
    have o := inT.late_out (sp := nativeStack sp 64) (ra := jal_8000a314_call.link) (start := blk) (trig := blk)
      (blk := blk) (top := blk + size) (tr := youngTrigger blk size) (wsize := size >>> 3) (raw := raw)
      A.tableDomain A.tableLow A.tableHigh slotHigh
    have a1 := inT.apart refs.spot1 refs.slots1
    have a2 := inT.apart refs.spot2 refs.slots2
    have a3 := inT.apart refs.spot3 refs.slots3
    rw [p16.memory, show writeLog d15.σ.mem [] = d15.σ.mem from rfl, p15.memory,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot3.tail_miss a3)), mem14,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot3.clear_miss a3)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot2.reset_miss a2)), mem13,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot2.clear_miss a2)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot1.reset_miss a1)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot1.clear_miss a1)), R.memory, writeLog_out _ _ _ o.2, p10.memory,
      writeLog_out _ _ _ o.1, p9.memory, show writeLog d8.σ.mem [] = d8.σ.mem from rfl, p8.memory]
    rfl
  have slots16 (i : Nat) (hi : i < 2048) : slotWord d16.σ.mem ent i = slotWord d7.σ.mem ent i :=
    slotWord_window_agree fits64 late i hi
  -- the young fields
  have lateField (off : Nat) (lo : 8 ≤ off) (hi : off + 8 ≤ 928) :
      bytesT d16.σ.mem (domainField off) 8 = bytesT d10.σ.mem (domainField off) 8 := by
    rw [p16.memory, show writeLog d15.σ.mem [] = d15.σ.mem from rfl, p15.memory,
      bytesT_writeLog_out _ (refs.spot3.tail_miss (domain_field_apart hi refs.domain3)), mem14,
      bytesT_writeLog_out _ (refs.spot3.clear_miss (domain_field_apart hi refs.domain3)),
      bytesT_writeLog_out _ (refs.spot2.reset_miss (domain_field_apart hi refs.domain2)), mem13,
      bytesT_writeLog_out _ (refs.spot2.clear_miss (domain_field_apart hi refs.domain2)),
      bytesT_writeLog_out _ (refs.spot1.reset_miss (domain_field_apart hi refs.domain1)),
      bytesT_writeLog_out _ (refs.spot1.clear_miss (domain_field_apart hi refs.domain1)), R.memory,
      bytesT_writeLog_out _ (renew_field_miss lo hi slotHigh)]
  have field (i off : Nat) (v : BitVec 64) (lo : 8 ≤ off) (hi : off + 8 ≤ 928)
      (entry : (minorFieldsLog blk (blk + size) (youngTrigger blk size) (size >>> 3) raw)[i]? = some (domainField off, 8, v))
      (later : OutLRange ((minorFieldsLog blk (blk + size) (youngTrigger blk size) (size >>> 3) raw).drop (i + 1))
        (domainField off) 8) :
      bytesT d16.σ.mem (domainField off) 8 = v := by
    rw [lateField off lo hi]; exact fieldsAt i off v entry later
  have limit16 : bytesT d16.σ.mem (domainField 0) 8 = blk := by
    rw [p16.memory, show writeLog d15.σ.mem [] = d15.σ.mem from rfl, p15.memory,
      bytesT_writeLog_out _ (refs.spot3.tail_miss (domain_field_apart (by decide) refs.domain3)), mem14,
      bytesT_writeLog_out _ (refs.spot3.clear_miss (domain_field_apart (by decide) refs.domain3)),
      bytesT_writeLog_out _ (refs.spot2.reset_miss (domain_field_apart (by decide) refs.domain2)), mem13,
      bytesT_writeLog_out _ (refs.spot2.clear_miss (domain_field_apart (by decide) refs.domain2)),
      bytesT_writeLog_out _ (refs.spot1.reset_miss (domain_field_apart (by decide) refs.domain1)),
      bytesT_writeLog_out _ (refs.spot1.clear_miss (domain_field_apart (by decide) refs.domain1)), R.memory,
      show domainField 0 = firstDomainPtr.toNat from rfl,
      word_writeLog_at _ (OCaml.Vm.Primitives.Memprof.RenewMinorSample.renewLog (nativeStack sp 64)
        jal_8000a314_call.link firstDomainPtr blk blk) 2 _ _ rfl trivial]
    simp [OCaml.Vm.Primitives.Memprof.UpdateYoungLimit.limitValue]
  have pages16 : pageCount d16.σ.mem ent.toNat = n := by
    rw [pageCount_congr (m := d7.σ.mem) (m' := d16.σ.mem) fun i hi => by
      rw [← slotWord_pageSlot d16.σ.mem ent i hi fits64, ← slotWord_pageSlot d7.σ.mem ent i hi fits64]
      exact slots16 i hi, PA.count, count6]
    omega
  have domainHigh16 (off : Nat) (lo : 128 ≤ off) (hi : off + 8 ≤ 928) :
      bytesT d16.σ.mem (domainField off) 8 = bytesT c.σ.mem (domainField off) 8 := by
    rw [p16.memory, show writeLog d15.σ.mem [] = d15.σ.mem from rfl, p15.memory,
      bytesT_writeLog_out _ (refs.spot3.tail_miss (domain_field_apart hi refs.domain3)), mem14,
      bytesT_writeLog_out _ (refs.spot3.clear_miss (domain_field_apart hi refs.domain3)),
      bytesT_writeLog_out _ (refs.spot2.reset_miss (domain_field_apart hi refs.domain2)), mem13,
      bytesT_writeLog_out _ (refs.spot2.clear_miss (domain_field_apart hi refs.domain2)),
      bytesT_writeLog_out _ (refs.spot1.reset_miss (domain_field_apart hi refs.domain1)),
      bytesT_writeLog_out _ (refs.spot1.clear_miss (domain_field_apart hi refs.domain1))]
    exact word_observed _ fun i hi8 => kept11 _ ((InDomain.field hi hi8).not_foot A.domainOwned)
      (domain_byte_out (by omega) hi hi8 A.tableDomain slotHigh)
  have low16 (x : Nat) (low : x < heapStart) (global : ¬ allocGlobal x)
      (occ : x < pageTable + 0x18 ∨ pageTable + 0x20 ≤ x) (trig : x < 0x80064cc8 ∨ 0x80064cc8 + 8 ≤ x) :
      (d16.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have l1 := refs.spot1.low
    have l2 := refs.spot2.low
    have l3 := refs.spot3.low
    have a1 : x + 1 ≤ t1.toNat ∨ t1.toNat + 56 ≤ x := Or.inl (by omega)
    have a2 : x + 1 ≤ t2.toNat ∨ t2.toNat + 56 ≤ x := Or.inl (by omega)
    have a3 : x + 1 ≤ t3.toNat ∨ t3.toNat + 56 ≤ x := Or.inl (by omega)
    rw [p16.memory, show writeLog d15.σ.mem [] = d15.σ.mem from rfl, p15.memory,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot3.tail_miss a3)), mem14,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot3.clear_miss a3)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot2.reset_miss a2)), mem13,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot2.clear_miss a2)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot1.reset_miss a1)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot1.clear_miss a1))]
    have th := A.tableHigh
    have sh := slotHigh
    rw [hS] at low th
    rw [hE] at sh
    apply kept11 x (fun f => by rcases f with g | ⟨above, _, _⟩; exact global g; rw [hS] at above; omega)
    refine ⟨by rw [hE]; omega, by simp only [OutW, and_true]; exact ⟨occ, Or.inl (by omega)⟩, ?_, ?_⟩
    · simp only [OutL, minorFieldsLog, domainField, dom, and_true]; omega
    · simp only [OutL, OCaml.Vm.Primitives.Memprof.RenewMinorSample.renewLog, domainField, dom,
        show OCaml.Vm.Primitives.Memprof.RenewMinorSample.triggerAddr.toNat = 2147896520 from rfl, and_true]
      omega
  have caller16 (x : Nat) (hx : sp.toNat ≤ x) : (d16.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have spH := A.frame.lower
    unfold allocHeadroom at spH
    have h1 := refs.spot1.high
    have h2 := refs.spot2.high
    have h3 := refs.spot3.high
    have a1 : x + 1 ≤ t1.toNat ∨ t1.toNat + 56 ≤ x := Or.inr (by omega)
    have a2 : x + 1 ≤ t2.toNat ∨ t2.toNat + 56 ≤ x := Or.inr (by omega)
    have a3 : x + 1 ≤ t3.toNat ∨ t3.toNat + 56 ≤ x := Or.inr (by omega)
    have slotLe : (nativeStack sp 64 - 16#64 + 8#64).toNat + 8 ≤ sp.toNat := by
      rw [slotEq, nativeStack, frame16.address _ (by decide), frame16.slot_nat (by decide)]
      unfold nativeFrameBase
      rw [stackNat]
      omega
    have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
    have hE' : heapEnd = 0x86800000 := rfl
    rw [hE'] at spH
    have outNat8 : (nativeStack sp 64 + 8#64).toNat + 8 ≤ sp.toNat := by
      rw [outNat]; unfold nativeFrameBase; have := frame64.lower; omega
    rw [p16.memory, show writeLog d15.σ.mem [] = d15.σ.mem from rfl, p15.memory,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot3.tail_miss a3)), mem14,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot3.clear_miss a3)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot2.reset_miss a2)), mem13,
      writeLog_out _ _ _ (outL_of_range1 (refs.spot2.clear_miss a2)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot1.reset_miss a1)),
      writeLog_out _ _ _ (outL_of_range1 (refs.spot1.clear_miss a1)), R.memory,
      writeLog_out _ _ _ (by
        simp only [OutL, OCaml.Vm.Primitives.Memprof.RenewMinorSample.renewLog, domainField, dom,
          show OCaml.Vm.Primitives.Memprof.RenewMinorSample.triggerAddr.toNat = 2147896520 from rfl, and_true]
        omega),
      p10.memory, writeLog_out _ _ _ (by simp only [OutL, minorFieldsLog, domainField, dom, and_true]; omega),
      p9.memory, show writeLog d8.σ.mem [] = d8.σ.mem from rfl, p8.memory,
      show writeLog d7.σ.mem [] = d7.σ.mem from rfl, PA.caller x (by rw [stackNat]; omega), p6.memory,
      show writeLog d5.σ.mem [] = d5.σ.mem from rfl, D.caller x (by rw [stackNat]; omega) (Or.inr (by omega)),
      p4.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, p3.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl,
      p2.memory, frameOn_writeLog _ _ _ inside2 x ⟨Or.inr hx, trivial⟩, p1.memory]
    rfl
  subst hblk
  refine ⟨raw, d16, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans run16)))))))))))))), {
    pc := p16.pc
    regs := p16.regs
    ready := ready16
    fresh := fresh
    saved := fun k lo hi => by
      have out (L : List Nat) (low : ∀ m ∈ L, m < 20) : k ∉ L := fun mem => by have := low k mem; omega
      have r16 : gprGet d16.σ k = gprGet d15.σ k :=
        p16.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (out _ (by decide))
      have r2 : gprGet d2.σ k = gprGet d1.σ k :=
        p2.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (out _ (by decide))
      rw [r16, g15 k (by omega) (by omega) (out _ (by decide)), g14 k (by omega) (by omega) (out _ (by decide)),
        g13 k (by omega) (by omega) (out _ (by decide)), g12 k (by omega) (by omega) (out _ (by decide)),
        frameR k (by omega) (by omega) (out _ (by decide)), keep10 k (by omega) (by omega) (out _ (by decide)),
        keep9 k (by omega) (by omega) (out _ (by decide)), keep8 k (by omega) (by omega) (out _ (by decide)),
        PA.saved k lo hi, keep6 k (by omega) (by omega) (out _ (by decide)),
        saved5 k (by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false]; omega),
        keep4 k (by omega) (by omega) (out _ (by decide)), keep3 k (by omega) (by omega) (out _ (by decide)), r2,
        keep1 k (by omega) (by omega) (out _ (by decide))]
    young := {
      limit := limit16
      ptr := field 5 8 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      base := field 8 24 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, List.drop, OutLRange])
      start := field 0 32 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      stop := field 3 40 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      allocStart := field 1 48 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      allocEnd := field 4 56 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      allocMid := field 6 64 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      trigger := field 2 72 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide)
      wsize := field 7 80 _ (by decide) (by decide) rfl (by simp only [minorFieldsLog, domainField, List.drop, OutLRange, dom, and_true]; decide) }
    table := by
      have F := PA.fields
      rw [count6, Nat.zero_add] at F
      exact PageTableFields.window_agree late F
    count := pages16
    present := fun j hj => by
      obtain ⟨i, hi, eq⟩ := PA.present j hj
      exact ⟨i, hi, by rw [slots16 i hi]; exact eq⟩
    only := fun i hi occupied => by
      rw [slots16 i hi] at occupied ⊢
      rcases PA.known i hi occupied with old | found
      · exact absurd (old.trans (table6.slot_zero fits64 i hi)) occupied
      · exact found
    domainHigh := domainHigh16
    lowKept := low16
    caller := caller16 }⟩
end OCaml.Vm.Boot.Startup
