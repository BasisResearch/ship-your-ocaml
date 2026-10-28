import OCaml.Vm.Gc.NamedOwnership
import OCaml.Vm.Primitives.Channel.MlOpen
import OCaml.Vm.Gc.CustomMem

/-!
# What `caml_ml_open_descriptor_out` keeps

`OpenedOut.kept` is the primitive's frame. Here it is discharged for the
bytes the VM reads, by where they lie:
* `covered_kept`: a byte of a region F1 covers (`f1Covered`), other than
  `Caml_state`, and outside the custom block;
* `record_kept`: an open record outside its link words;
* `static_kept`, `domainField_kept`: the static words and `Caml_state` fields
  the payload and the C-call frame read.
-/

namespace OCaml.Vm.Primitives.Channel
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.VsaHeap
set_option autoImplicit false
variable {Customs : Vsa.Machine.Config → Nat → Prop}

/-- The covered regions lie in the allocator arena. -/
theorem f1Covered_arena : ∀ e ∈ Gc.f1Covered, heapStart ≤ e.1 ∧ e.1 + e.2 ≤ heapEnd := by decide

/-- The covered regions other than `Caml_state` miss it. -/
theorem f1Covered_domain : ∀ e ∈ Gc.f1Covered, e.1 ≠ Boot.WhileMinRuntime.domain →
    e.1 + e.2 ≤ Boot.WhileMinRuntime.domain ∨
      Boot.WhileMinRuntime.domain + Layout.domainStateBytes ≤ e.1 := by decide

/-- The covered regions other than the minor heap miss it. -/
theorem f1Covered_minor : ∀ e ∈ Gc.f1Covered, e.1 ≠ Gc.minorRegion.lo →
    e.1 + e.2 ≤ Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ e.1 := by decide

section Kept

variable {live : Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
  {H : List (Nat × Nat)} {cap cap' charge : Nat} {chs : List Nat} {sp ra s0 s1 s2 v head : BitVec 64}
  {c d : Config}

/-- `Caml_state` at the entry is the cut's domain record. -/
theorem OutInput.domain (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c) :
    (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
  unfold word; rw [h.ready.domainWord]; rfl

/-- **A covered byte is kept**: a byte of a region F1 covers, other than
`Caml_state`, outside the custom block. -/
theorem covered_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (heap : Gc.LibHeapAt H cap chs c) (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c)
    {e : Nat × Nat} {x : Nat} (he : e ∈ Gc.f1Covered) (ne : e.1 ≠ Boot.WhileMinRuntime.domain)
    (ix : InExt e x) (blk : x + 24 < (runtimeFields c).youngPtr ∨ (runtimeFields c).youngPtr ≤ x) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  obtain ⟨lo, hi⟩ := f1Covered_arena e he
  have dom := f1Covered_domain e he ne
  have cov := heap.extents e he
  obtain ⟨b, hb, blo, bhi⟩ := cov
  obtain ⟨xl, xh⟩ := ix
  have lower := h.frame.lower
  have hDB : Layout.domainStateBytes = 928 := rfl
  refine o.kept x (fun s => (custom.apart c x s).covered e he ne ⟨xl, xh⟩) ?_ ?_ (Or.inl (by omega)) blk ?_
  · rintro (g | ⟨_, _, no⟩)
    · rcases allocGlobal_off_arena _ g with y | y <;> omega
    · exact no b hb ⟨by omega, by omega⟩
  · refine outW_openWindows h.frame (by omega) (fun l => absurd l (by omega)) ?_ fun hz => ?_
    · have r := Gc.fresh_apart_covered o.opening.fresh ⟨b, hb, blo, bhi⟩ (by omega) (n := recordBytes)
        (by unfold recordBytes; decide) (Nat.le_refl _)
      omega
    · have r := heap.recordsApart _ (head_mem heap.channels h.headWord hz) e he
      unfold Gc.chanRecordBytes chanOffBuff ioBufferSize at r
      omega
  · unfold Gc.domainAddr; rw [h.domain]; unfold Layout.off_young_ptr; omega

/-- The named table is kept using the same selected ledger as the actual
malloc, including its dynamic nodes and its separate custom state. -/
theorem named_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (heap : Gc.LibHeapAt H cap chs c) (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c)
    (N : OutNursery H chs c) {x : Nat} (read : NamedRead c x) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  have cov := heap.named.read_covered read
  have lower := h.frame.lower
  have lowM := N.low
  have highM := N.high
  have bounds : 0x80064d4c ≤ x ∧ x < heapEnd := by
    rcases cov with ⟨lo, hi⟩ | ⟨e, he, lo, hi⟩
    · simp only [Layout.sym_named_value_table, heapEnd] at *; omega
    · have b := heap.ready.block_bounds he
      simp only [heapStart] at b; omega
  have noFoot := heap.named.read_not_foot heap.ready read
  have out (e : Nat × Nat) (member : e ∈ Gc.f1Covered) : x < e.1 ∨ e.1 + e.2 ≤ x := by
    have apart := heap.named_fixed read member
    by_cases lo : x < e.1
    · exact Or.inl lo
    · exact Or.inr (by apply Classical.byContradiction; intro hi; exact apart ⟨by omega, by omega⟩)
  have dom := out (Boot.WhileMinRuntime.domain, Layout.domainStateBytes) (by decide)
  have minor := out (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo) (by decide)
  have recOut : x < o.opening.record.toNat ∨ o.opening.record.toNat + recordBytes ≤ x := by
    by_cases lo : x < o.opening.record.toNat
    · exact Or.inl lo
    · apply Or.inr
      apply Classical.byContradiction; intro hi
      rcases cov with bucket | ⟨e, he, elo, ehi⟩
      · have low := o.opening.low
        simp only [Layout.sym_named_value_table, heapStart] at *; omega
      · exact o.opening.fresh e he x ⟨by omega, by omega⟩ ⟨elo, by omega⟩
  have headOut : head ≠ 0#64 → x < head.toNat + 56 ∨ head.toNat + 64 ≤ x := by
    intro nonzero
    have member := head_mem heap.channels h.headWord nonzero
    have apart := heap.named_record read member
    have recordSize : 64 ≤ Gc.chanRecordBytes := by decide
    by_cases lo : x < head.toNat + 56
    · exact Or.inl lo
    · exact Or.inr (by apply Classical.byContradiction; intro hi; apply apart; constructor <;> dsimp only <;> omega)
  refine o.kept x (fun stateX => heap.customSpace.named x (custom.footprint c x stateX) read) noFoot
    (outW_openWindows_static h.frame bounds.2 (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) recOut headOut) (Or.inl (by omega)) ?_ ?_
  · dsimp only at minor
    have band : Gc.minorRegion.lo ≤ Gc.minorRegion.hi := by decide
    omega
  · unfold Gc.domainAddr
    rw [h.domain]
    dsimp only at dom
    simp only [Layout.off_young_ptr, Layout.domainStateBytes] at *
    omega

/-- Actual opening returns complete custom ownership, retained named roots
and spatial separation from the new record and every old live runtime region,
all with the same returned allocator ledger. -/
theorem OpenedOut.spatial_heap (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (heap : Gc.LibHeapAt H cap chs c) (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c)
    (N : OutNursery H chs c) :
    ∃ H' capacity, Boot.Startup.HeapReady H' capacity d ∧ Gc.CustomOwned Gc.CustomFoot H' d ∧
      Gc.CustomSpace ((o.opening.record.toNat, recordBytes) :: Gc.namedBlocked chs c) d ∧
      Gc.NamedLedger H' (Gc.namedBlocked chs c) d ∧ Gc.CustomLedger H' d ∧
      (∀ e ∈ (o.opening.record.toNat, recordBytes) :: H, e ∈ H') ∧
      cap' + Gc.customTableReserve d ≤ capacity + Gc.customTableReserve c := by
  let H1 := (o.opening.record.toNat, recordBytes) :: H
  have sub : ∀ e ∈ H, e ∈ H1 := fun e he => List.mem_cons_of_mem _ he
  have fresh : FreshBlock vsaLayoutP H o.opening.record.toNat recordBytes :=
    ⟨by have lo := o.opening.low; unfold heapStart at lo; omega,
      o.opening.low, o.opening.high, o.opening.fresh⟩
  have space := heap.customSpace.allocate heap.custom.owned fresh (Nat.le_refl recordBytes)
  have coverage : ∀ e ∈ (o.opening.record.toNat, recordBytes) :: Gc.namedBlocked chs c,
      Gc.Covered H1 e := by
    intro e he
    rcases List.mem_cons.mp he with rfl | old
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨owner, member, lo, hi⟩ := heap.blocked_covered e old
      exact ⟨owner, sub owner member, lo, hi⟩
  have keepNamed : ∀ a, NamedRead c a → byte d a = byte c a := by
    intro a read
    rw [byte_total, byte_total]
    exact named_kept custom o heap h N read
  have namedProtected : ∀ a, NamedRead c a → ¬ vsaFoot H1 a := by
    intro a read
    rcases heap.named.read_covered read with bucket | ⟨owner, member, lo, hi⟩
    · rintro (global | ⟨low, _, _⟩)
      · unfold allocGlobal InRange at global
        simp only [Layout.sym_named_value_table] at bucket
        omega
      · simp only [Layout.sym_named_value_table, heapStart] at *
        omega
    · exact Gc.Covered.notFoot (e := (a, 1)) ⟨owner, sub owner member, lo, hi⟩
        (fun _ member => o.opening.heap.block_bounds member) ⟨Nat.le_refl _, by dsimp only; omega⟩
  have spaceD := space.grow heap.named keepNamed o.allocIn
    (fun e he _ inside => (coverage e he).notFoot (fun _ member => o.opening.heap.block_bounds member) inside)
    namedProtected
  obtain ⟨H', capacity, ready, owned, ledger, old, spend⟩ := o.heap
  exact ⟨H', capacity, ready, custom.owned_physical owned o.ready, spaceD,
    (heap.named.frame keepNamed).mono (fun e he => old e (sub e he)), ledger, old, spend⟩

/-- **An open record is kept**, except the old head's `prev` word (bytes
56–63), which the opening rewrites. -/
theorem record_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (heap : Gc.LibHeapAt H cap chs c) (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c)
    (N : OutNursery H chs c) {r x : Nat} (hr : r ∈ chs) (lo : r ≤ x) (hi : x < r + Gc.chanRecordBytes)
    (link : r = head.toNat → x < r + 56 ∨ r + 64 ≤ x) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  obtain ⟨b, hb, blo, bhi⟩ := heap.records r hr
  dsimp only at blo bhi
  obtain ⟨bl, bh⟩ := h.ready.heap.block_bounds hb
  have lower := h.frame.lower
  have dom := heap.recordsApart r hr _ (by simp [Gc.f1Covered] : (Boot.WhileMinRuntime.domain, Layout.domainStateBytes) ∈ Gc.f1Covered)
  have minor := heap.recordsApart r hr _ (by simp [Gc.f1Covered] :
    (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo) ∈ Gc.f1Covered)
  have lowM := N.low
  have highM := N.high
  have hDB : Layout.domainStateBytes = 928 := rfl
  have hR : Gc.chanRecordBytes = 65608 := rfl
  simp only [Gc.minorRegion] at minor lowM highM
  dsimp only at dom minor
  refine o.kept x (fun s => ?_) ?_ ?_ (Or.inl (by omega)) ?_ ?_
  · have a := heap.custom_apart_record (custom.footprint c x s) hr
    unfold Gc.chanRecordBytes chanOffBuff ioBufferSize at a; omega
  · rintro (g | ⟨_, _, no⟩)
    · rcases allocGlobal_off_arena _ g with y | y <;> omega
    · exact no b hb ⟨by omega, by omega⟩
  · refine outW_openWindows h.frame (by omega) (fun l => absurd l (by omega)) ?_ fun hz => ?_
    · have f := Gc.fresh_apart_covered o.opening.fresh (x := (r, Gc.chanRecordBytes)) ⟨b, hb, blo, bhi⟩
        (by show 0 < Gc.chanRecordBytes; decide)
        (n := recordBytes)
        (by unfold recordBytes; decide) (Nat.le_refl _)
      dsimp only at f; unfold recordBytes at f ⊢; omega
    · have mh := head_mem heap.channels h.headWord hz
      by_cases same : r = head.toNat
      · have := link same; omega
      · have a := heap.recordsDisjoint r hr _ mh same
        omega
  · omega
  · unfold Gc.domainAddr; rw [h.domain]; unfold Layout.off_young_ptr; omega

/-- **A `Caml_state` field is kept** unless it is `young_ptr` or the
custom allocation's `extra_heap_resources_minor`. -/
theorem domainField_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c)
    (N : OutNursery H chs c) {off x : Nat} (fits : off + 8 ≤ Layout.domainStateBytes)
    (young : Layout.off_young_ptr + 8 ≤ off)
    (extra : off + 8 ≤ Layout.off_extra_heap_resources_minor ∨ Layout.off_extra_heap_resources_minor + 8 ≤ off)
    (lo : Boot.WhileMinRuntime.domain + off ≤ x) (hi : x < Boot.WhileMinRuntime.domain + off + 8) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  have inDom : InExt (Gc.domainAddr c 0, Layout.domainStateBytes) x := by
    unfold Gc.domainAddr; rw [h.domain]; constructor <;> dsimp only <;> omega
  obtain ⟨b, hb, blo, bhi⟩ := N.domain
  dsimp only at blo bhi
  have lower := h.frame.lower
  have lowM := N.low
  have hDB : Layout.domainStateBytes = 928 := rfl
  have hE : Boot.WhileMinRuntime.domain + 928 ≤ heapEnd := by decide
  have hSD : heapStart ≤ Boot.WhileMinRuntime.domain := by decide
  have hDM : Boot.WhileMinRuntime.domain + 928 ≤ 0x80082000 := by decide
  have hY : Layout.off_young_ptr = 8 := rfl
  have hX : Layout.off_extra_heap_resources_minor = 96 := rfl
  simp only [Gc.minorRegion] at lowM
  refine o.kept x (fun s => ?_) ?_ ?_ (Or.inl (by omega)) (Or.inl (by omega)) ?_
  · have a := (custom.apart c x s).domainField inDom
    unfold Gc.domainAddr at a; rw [h.domain] at a
    obtain ⟨al, ah⟩ := a
    omega
  · rintro (g | ⟨_, _, no⟩)
    · rcases allocGlobal_off_arena _ g with y | y <;> omega
    · exact no b hb ⟨by omega, by omega⟩
  · refine outW_openWindows h.frame (by omega) (fun l => absurd l (by omega)) ?_ fun hz => ?_
    · have f := Gc.fresh_apart_covered o.opening.fresh N.domain (by decide) (n := recordBytes)
        (by unfold recordBytes; decide) (Nat.le_refl _)
      dsimp only at f; unfold recordBytes at f ⊢; omega
    · have a := N.recordsApart _ (head_mem N.channels h.headWord hz)
      unfold Gc.chanRecordBytes chanOffBuff ioBufferSize at a
      omega
  · unfold Gc.domainAddr; rw [h.domain]; omega

/-- The static words the represented state and the C-call frame read. -/
def openStatics : List Nat :=
  [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
   Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_main_argv,
   Layout.sym_caml_prim_table + Layout.off_prim_contents]

/-- The statics are below the arena, apart from newlib's globals, from the
opening's static stores and from the custom allocation's counter. -/
theorem openStatics_apart : ∀ a ∈ openStatics, ∀ j < 8,
    a + j < heapStart ∧ ¬ allocGlobal (a + j) ∧
    (a + j < 0x80064aa0 ∨ 0x80064aa8 ≤ a + j) ∧ (a + j < 0x80064b40 ∨ 0x80064b48 ≤ a + j) := by
  unfold allocGlobal InRange
  decide

/-- **A static word the VM reads is kept.** -/
theorem static_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c) (N : OutNursery H chs c)
    {a j : Nat} (mem : a ∈ openStatics) (hj : j < 8) :
    (d.σ.mem[a + j]?).getD 0 = (c.σ.mem[a + j]?).getD 0 := by
  obtain ⟨below, notGlobal, notExtra, notHead⟩ := openStatics_apart a mem j hj
  have lower := h.frame.lower
  have lowM := N.low
  have hSE : heapStart ≤ heapEnd := by decide
  have hSM : heapStart ≤ 0x80082000 := by decide
  have hSD : heapStart ≤ Boot.WhileMinRuntime.domain := by decide
  simp only [Gc.minorRegion] at lowM
  refine o.kept _ (fun s => ?_) ?_ ?_ (Or.inl (by omega)) (Or.inl (by omega)) ?_
  · have e := (custom.apart c _ s).static below
    simp only [InExt, Layout.sym_caml_extra_heap_resources] at e
    omega
  · rintro (g | ⟨l, _, _⟩)
    · exact notGlobal g
    · omega
  · apply OCaml.Vm.Gc.outW_all
    intro w hw
    unfold openWindows at hw
    rcases List.mem_append.mp hw with hw | hw
    · have g1 : ¬ InRange 0x80064668 0x8006466c (a + j) := fun h => notGlobal (Or.inr (Or.inl h))
      have g2 : ¬ InRange 0x80064d48 0x80064d4c (a + j) :=
        fun h => notGlobal (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      unfold InRange at g1 g2
      have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
        have e := outFrame_slot (h.frame.resize (small := 16) (by decide) (by decide)) (off := 0) (by decide)
        rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e; rw [e]; omega
      have pl := o.opening.low
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · left; dsimp only; rw [sp16]; omega
      all_goals (dsimp only; omega)
    · by_cases hz : head = 0#64
      · simp [hz] at hw
      · simp only [hz, ite_false, List.mem_singleton] at hw
        subst hw
        obtain ⟨⟨e, he, hl, _⟩, _⟩ := h.headLive hz
        have bounds := h.ready.heap.block_bounds (q := e.1) (n := e.2) he
        left; dsimp only; omega
  · unfold Gc.domainAddr; rw [h.domain]; unfold Layout.off_young_ptr; omega

end Kept

end OCaml.Vm.Primitives.Channel
