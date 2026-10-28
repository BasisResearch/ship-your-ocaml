import OCaml.Vm.Primitives.Channel.OpenPhases

/-! `caml_ml_open_descriptor_{out,in}` composed from its phases (`OpenPhases`,
generated) over either direction (`OpenCode`). -/

namespace OCaml.Vm.Primitives.Channel
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap LeanRV64DExecutable
open OCaml.Vm.Boot.Startup
open OCaml.Vm.Sim (FrameOnD)
open ExitPath (LogWithin)
set_option autoImplicit false
variable {Customs : Config → Nat → Prop}
variable {live : Nat → Prop}

/-- **One direction of `caml_ml_open_descriptor_{out,in}`**: its entry, the
return addresses of its two calls (`caml_open_descriptor_in`,
`caml_alloc_custom_mem`), and the three phase summaries around them, each from
that direction's generated blocks (`OpenOut`, `OpenIn`). The output direction
also stores `max := NULL` (`chanFlagsLog`). -/
structure OpenCode where
  out : Bool
  entry : BitVec 64
  proLink : BitVec 64
  doneEntry : BitVec 64
  proAligned : proLink.toNat % 4 = 0
  doneAligned : doneEntry.toNat % 4 = 0
  enter : ∀ {live : Nat → Prop} [LibraryLive live] (c : Config) {H : List (Nat × Nat)} {capacity charge : Nat}
    {sp ra s0 s1 s2 v head : BitVec 64}, OutInput live H capacity charge sp ra s0 s1 s2 v head c →
    FnSummary entry (fun d => d = c) (OutEntered proLink live H capacity charge sp ra s0 s1 s2 v head c)
  flags : ∀ (o : Config) {sp p : BitVec 64}, LeafInput proLink o → gprGet o.σ 2 = some sp →
    gprGet o.σ 10 = some p → heapStart ≤ p.toNat → p.toNat + recordBytes ≤ heapEnd → p.toNat % 16 = 0 →
    bytesT o.σ.mem (p.toNat + 64) 8 = 0#64 →
    FnSummary proLink (fun d => d = o) (OutFlagged doneEntry out sp p o)
  done : ∀ (a : Config) {sp ra s0 p v : BitVec 64} {f : Config} {state : Config → Nat → Prop}
    {H : List (Nat × Nat)}, Gc.CustomMemReturned state H (outSite doneEntry (sp - 16#64) p) v f a →
    heapStart ≤ v.toNat → v.toNat + 16 ≤ heapEnd → v.toNat % 8 = 0 → NativeFrame sp 592 →
    bytesT a.σ.mem (sp.toNat - 8) 8 = ra → bytesT a.σ.mem (sp.toNat - 16) 8 = s0 → ra.toNat % 4 = 0 →
    FnSummary doneEntry (fun d => d = a) (OutDone sp ra s0 p v a)

/-- **`caml_ml_open_descriptor_out`'s phases.** -/
def openOutCode : OpenCode where
  out := true
  entry := 0x80015f50#64
  proLink := OpenOut.pro_call.link
  doneEntry := OpenOut.flags_call.link
  proAligned := by decide
  doneAligned := by decide
  enter := fun c => out_enter c
  flags := fun o => out_flags o
  done := fun a => out_done a

/-- **`caml_ml_open_descriptor_in`'s phases.** -/
def openInCode : OpenCode where
  out := false
  entry := 0x80015ef0#64
  proLink := OpenIn.pro_call.link
  doneEntry := OpenIn.flags_call.link
  proAligned := by decide
  doneAligned := by decide
  enter := fun c => in_enter c
  flags := fun o => in_flags o
  done := fun a => in_done a

/-- The record stores of either direction. -/
theorem OpenedRecord.flagsDir {out : Bool} {m : Std.ExtHashMap Nat (BitVec 8)} {p fd head : BitVec 64}
    (h : OpenedRecord m p fd head) : OpenRecord out (writeLog m (chanFlagsLog out p)) p fd head := by
  cases out
  · exact h.flags_in
  · exact h.flags

/-- **A byte outside the opening's windows**: below the arena's end, outside
the statics the opening writes, apart from the record and from the old head's
`prev` word. -/
theorem outW_openWindows_static {sp p head : BitVec 64} {y : Nat} (frame : NativeFrame sp 592) (below : y < heapEnd)
    (errno₁ : y < 0x80064668 ∨ 0x8006466c ≤ y)
    (errno₂ : y < 0x80064d48 ∨ 0x80064d4c ≤ y)
    (headWord : y < 0x80064b40 ∨ 0x80064b48 ≤ y)
    (recApart : y < p.toNat ∨ p.toNat + recordBytes ≤ y)
    (hd : head ≠ 0#64 → y < head.toNat + 56 ∨ head.toNat + 64 ≤ y) :
    OutW (openWindows (sp - 16#64) p head) y := by
  have lower := frame.lower
  have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
    have e := outFrame_slot (frame.resize (small := 16) (by decide) (by decide)) (off := 0) (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e; rw [e]; omega
  have hS : heapStart = 0x8007d140 := rfl
  apply OCaml.Vm.Gc.outW_all
  intro w hw
  unfold openWindows at hw
  rcases List.mem_append.mp hw with hw | hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · left; dsimp only; rw [sp16]; arena_omega
    · exact errno₁
    · exact errno₂
    · exact recApart
    · exact headWord
  · by_cases hz : head = 0#64
    · simp [hz] at hw
    · simp only [hz, ite_false, List.mem_singleton] at hw
      subst hw
      exact hd hz

/-- The original static-band instance of the general opening-window frame. -/
theorem outW_openWindows {sp p head : BitVec 64} {y : Nat} (frame : NativeFrame sp 592) (below : y < heapEnd)
    (stat : y < heapStart → 0x80064aa0 ≤ y ∧ y < 0x80064aa8)
    (recApart : y < p.toNat ∨ p.toNat + recordBytes ≤ y)
    (hd : head ≠ 0#64 → y < head.toNat + 56 ∨ head.toNat + 64 ≤ y) :
    OutW (openWindows (sp - 16#64) p head) y := by
  apply outW_openWindows_static frame below ?_ ?_ ?_ recApart hd
  all_goals
    rcases Nat.lt_or_ge y heapStart with low | high
    · have := stat low; omega
    · simp only [heapStart] at high; omega

/-! ### The whole primitive -/

/-- The collector's side at the primitive's entry: `Caml_state` and the minor
heap are live blocks of `H`, the open records `chs` lie apart from
`Caml_state`, and the nursery has room for the custom block. -/
structure OutNursery (H : List (Nat × Nat)) (chs : List Nat) (c : Config) : Prop where
  context : Gc.CustomCallPins c
  custom : Gc.CustomLedger H c
  space : Gc.CustomSpace (chs.map (fun r => (r, Gc.chanRecordBytes))) c
  records : ∀ r ∈ chs, Gc.Covered H (r, Gc.chanRecordBytes)
  domain : Gc.Covered H (Boot.WhileMinRuntime.domain, Layout.domainStateBytes)
  minor : Gc.Covered H (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo)
  channels : Gc.OpenChannelList c.σ.mem chs
  recordsApart : ∀ r ∈ chs, r + Gc.chanRecordBytes ≤ Boot.WhileMinRuntime.domain ∨
    Boot.WhileMinRuntime.domain + Layout.domainStateBytes ≤ r
  room : (runtimeFields c).youngLimit + 24 ≤ (runtimeFields c).youngPtr
  aligned : (runtimeFields c).youngPtr % 8 = 0
  low : Gc.minorRegion.lo + 24 ≤ (runtimeFields c).youngPtr
  high : (runtimeFields c).youngPtr ≤ Gc.minorRegion.hi

/-- The owned selected record extents and local custom space supply the
opening's refcount/prev-store separation. -/
theorem OutNursery.record_apart {H : List (Nat × Nat)} {chs : List Nat} {c : Config}
    {cap a r : Nat} (h : OutNursery H chs c) (heap : HeapReady H cap c)
    (foot : Gc.CustomFoot c a) (member : r ∈ chs) :
    a < r ∨ r + chanOffBuff + ioBufferSize ≤ a := by
  obtain ⟨e, he, elo, _⟩ := h.records r member
  have low := (heap.block_bounds he).1
  have sep := h.space.record_apart foot (by dsimp only at elo; omega)
    (h.recordsApart r member) (List.mem_map.mpr ⟨r, member, rfl⟩)
  simpa only [Gc.chanRecordBytes, Nat.add_assoc] using sep

/-- A nonzero list head is an open record. -/
theorem head_mem {m : Std.ExtHashMap Nat (BitVec 8)} {chs : List Nat} {head : BitVec 64}
    (channels : Gc.OpenChannelList m chs) (headWord : bytesVal .ld (read8 m (2147896128#64).toNat) = head)
    (hz : head ≠ 0#64) : head.toNat ∈ chs := by
  unfold Gc.OpenChannelList at channels
  rw [show Layout.sym_caml_all_opened_channels = (2147896128#64).toNat from rfl, ← read8_value, headWord]
    at channels
  generalize hx : head.toNat = x at channels ⊢
  cases channels with
  | nil => exact absurd (BitVec.eq_of_toNat_eq (by rw [hx]; rfl)) hz
  | cons => exact List.mem_cons_self

/-- `caml_ml_open_descriptor_out(v)` returned the custom block `value` holding
the new output channel `record`, linked at the head of
`caml_all_opened_channels`, with `k` custom allocations still safe. -/
structure OpenedOut (code : OpenCode) (live : Nat → Prop) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (Customs : Config → Nat → Prop) (k : Nat)
    (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra s0 s1 s2 v head : BitVec 64) (c d : Config) where
  entered : Config
  opened : Config
  flagged : Config
  allocated : Config
  value : BitVec 64
  enter : OutEntered code.proLink live H capacity charge sp ra s0 s1 s2 v head c entered
  opening : OpenedIn live H capacity (sp - 16#64) code.proLink s0 s1 s2 (fdOf v) head entered opened
  flags : OutFlagged code.doneEntry code.out (sp - 16#64) opening.record opened flagged
  custom : Gc.CustomMemCountedReturned state Customs ((opening.record.toNat, recordBytes) :: H) capacity
    (outSite code.doneEntry (sp - 16#64) opening.record) value flagged allocated
  done : OutDone sp ra s0 opening.record value allocated d
  record : OpenRecord code.out d.σ.mem opening.record (fdOf v) head
  linked : OCaml.Vm.Gc.OpenChannelsLinked c.σ.mem d.σ.mem opening.record.toNat
  /-- `Channel(res) = chan` -/
  channel : bytesT d.σ.mem (value.toNat + 8) 8 = opening.record
  ops : bytesT d.σ.mem value.toNat 8 = 2147891728#64
  /-- the custom block's header (wosize 2, `Custom_tag`) -/
  header : bytesT d.σ.mem (value.toNat - 8) 8 = Gc.customHeader
  ready : Ready k d
  counted : Gc.CustomCountStep Customs c d 1
  /-- Heap readiness and state ownership use the same returned ledger. -/
  heap : ∃ H' cap', HeapReady H' cap' d ∧ Gc.CustomOwned state H' d ∧ Gc.CustomLedger H' d ∧
    (∀ e ∈ (opening.record.toNat, recordBytes) :: H, e ∈ H') ∧
    capacity + Gc.customTableReserve d ≤ cap' + Gc.customTableReserve c
  /-- the custom block lies just below the entry's young pointer, which drops by 24 -/
  block : value.toNat + 16 = (runtimeFields c).youngPtr
  youngPtr : (runtimeFields d).youngPtr = (runtimeFields c).youngPtr - 24
  youngLimit : (runtimeFields d).youngLimit = (runtimeFields c).youngLimit
  domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state
  /-- Physical allocated-table growth at this actual opening, relative to the
  ledger that already contains the freshly allocated channel record. -/
  allocIn : ∀ a, Gc.CustomAllocFoot d a → Gc.CustomAllocFoot c a ∨
    vsaFoot ((opening.record.toNat, recordBytes) :: H) a
  /-- **The primitive's memory frame**: every byte outside the runtime's
  custom state, newlib's free space, the opening's windows, the primitive's
  frame, the 24-byte block and the `young_ptr` word reads as at the entry. -/
  kept : ∀ a, ¬ state c a → ¬ vsaFoot H a → OutW (openWindows (sp - 16#64) opening.record head) a →
    (a < sp.toNat - 16 ∨ sp.toNat ≤ a) →
    (a + 24 < (runtimeFields c).youngPtr ∨ (runtimeFields c).youngPtr ≤ a) →
    (a + 8 ≤ Gc.domainAddr c Layout.off_young_ptr ∨ Gc.domainAddr c Layout.off_young_ptr + 8 ≤ a) →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

theorem ml_open_descriptor [LibraryLive live] (code : OpenCode) (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 v head : BitVec 64) {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (k : Nat) (ready : Ready (k + 1) c) {chs : List Nat}
    (N : OutNursery H chs c) (h : OutInput live H capacity charge sp ra s0 s1 s2 v head c) :
    FnSummary code.entry (fun d => d = c)
      (fun d => Nonempty (OpenedOut code live Ready state Customs k H capacity charge sp ra s0 s1 s2 v head c d)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have lower := h.frame.lower
  have hSE : heapStart ≤ heapEnd := by decide
  have hS : heapStart = 0x8007d140 := rfl
  have hD : Boot.WhileMinRuntime.domain = 0x8007d150 := rfl
  have hDB : Layout.domainStateBytes = 928 := rfl
  have lowM := N.low
  have highM := N.high
  simp only [Gc.minorRegion] at lowM highM
  obtain ⟨entered, run1, E⟩ := (code.enter c h).run c ⟨pc, rfl⟩
  obtain ⟨opened, run2, ⟨O⟩⟩ := (open_descriptor_in entered H capacity charge (sp - 16#64) _ s0 s1 s2
    (fdOf v) head E.input).run entered ⟨E.pc, rfl⟩
  obtain ⟨rec, headW⟩ := OpenedIn.record_words E.input O
  have pLow := O.low
  have pHigh : O.record.toNat + 65616 ≤ heapEnd := O.high
  have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
    have e := outFrame_slot (h.frame.resize (small := 16) (by decide) (by decide)) (off := 0) (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e; rw [e]; omega
  have leaf : LeafInput code.proLink opened :=
    ⟨O.link.good, O.link.image, O.link.minstret, O.link.raReg, code.proAligned, O.link.tick⟩
  obtain ⟨flagged, run3, F⟩ := (code.flags opened leaf O.link.stack O.link.result O.low O.high O.align
    rec.zero).run opened ⟨O.link.pc, rfl⟩
  have flagsIn : LogInW [⟨O.record.toNat, O.record.toNat + 72⟩] (chanFlagsLog code.out O.record) :=
    OCaml.Vm.Primitives.Channel.LogWithin.inW chanFlagsLog_within
  have flagsOut (a : Nat) (out : a < O.record.toNat ∨ O.record.toNat + 72 ≤ a) :
      (flagged.σ.mem[a]?).getD 0 = (opened.σ.mem[a]?).getD 0 := by
    rw [F.memory, frameOn_writeLog _ _ _ flagsIn a ⟨out, trivial⟩]
  have saveIn := outSaveLog_inside (ra := ra) (s0 := s0) (h.frame.resize (small := 16) (by decide) (by decide))
  -- runtime globals and the bytes outside the opening's stores, at the custom call
  have staticE : StaticKept c entered :=
    StaticKept.of_log saveIn (fun a ⟨below, _, _⟩ => ⟨Or.inl (by show a < sp.toNat - 16; arena_omega), trivial⟩)
      entered E.memory
  have staticF : StaticKept opened flagged := fun a ⟨below, _, _⟩ => flagsOut a (Or.inl (by arena_omega))
  have openOut (a : Nat) (o : OutW (openWindows (sp - 16#64) O.record head) a) :
      a < O.record.toNat ∨ O.record.toNat + 72 ≤ a := by
    have base := ((outW_append _ _ a).mp o).1
    simp only [OutW, and_true] at base
    obtain ⟨_, _, _, o4, _⟩ := base
    unfold recordBytes at o4
    omega
  have keptF (a : Nat) (o : OutW (openWindows (sp - 16#64) O.record head) a) (notFoot : ¬ vsaFoot H a)
      (frame : a < sp.toNat - 16 ∨ sp.toNat ≤ a) : (flagged.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    rw [flagsOut a (openOut a o), O.frame a o notFoot, E.memory, frameOn_writeLog _ _ _ saveIn a ⟨frame, trivial⟩]
  -- where the record, `Caml_state` and the minor heap lie
  have owned : Gc.CustomOwned state H c :=
    ⟨fun a ha => N.custom.owned.bytes a (custom.footprint c a ha)⟩
  have freshRecord : FreshBlock vsaLayoutP H O.record.toNat recordBytes :=
    ⟨by arena_omega, O.low, O.high, O.fresh⟩
  have recMinor := Gc.fresh_apart_covered O.fresh N.minor (by decide) (n := recordBytes)
    (by unfold recordBytes; decide) (Nat.le_refl _)
  have recDomain := Gc.fresh_apart_covered O.fresh N.domain (by decide) (n := recordBytes)
    (by unfold recordBytes; decide) (Nat.le_refl _)
  simp only [Gc.minorRegion] at recMinor recDomain
  unfold recordBytes at recMinor recDomain
  have headApart (y : Nat) (hz : head ≠ 0#64)
      (apart : y < head.toNat ∨ head.toNat + chanOffBuff + ioBufferSize ≤ y) :
      y < head.toNat + 56 ∨ head.toNat + 64 ≤ y := by
    unfold chanOffBuff ioBufferSize at apart; omega
  have outOpen (y : Nat) := outW_openWindows (head := head) (p := O.record) (y := y) h.frame
  have notFootHigh (L : List (Nat × Nat)) (y : Nat) (high : heapEnd ≤ y) : ¬ vsaFoot L y := by
    rintro (g | ⟨_, l, _⟩)
    · unfold allocGlobal InRange at g; unfold heapEnd at high; omega
    · omega
  -- the runtime's custom-allocation state is apart from the opening's stores
  have stateOut (a : Nat) (s : state c a) : (flagged.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    have ap := custom.apart c a s
    have below := ap.belowStack
    have free := custom.notFoot owned s
    refine keptF a (outOpen a below (fun l => ?_) ?_ fun hz => headApart a hz
      (N.record_apart h.ready.heap (custom.footprint c a s)
        (head_mem N.channels h.headWord hz))) free (Or.inl (by arena_omega))
    · have e := ap.static l
      simp only [VsaIris.InExt, Layout.sym_caml_extra_heap_resources] at e
      omega
    · rcases Nat.lt_or_ge a O.record.toNat with l | g
      · exact Or.inl l
      · exact Or.inr (Nat.le_of_not_lt fun hi => owned.fresh freshRecord s ⟨g, hi⟩)
  have staticC : StaticKept c flagged := staticE.trans (O.static.trans staticF)
  have domF : word flagged Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    unfold word
    apply bytesT_keep
    intro j hj
    exact staticC _ ⟨by unfold Layout.sym_Caml_state; omega,
      by unfold allocGlobal InRange Layout.sym_Caml_state; omega,
      Or.inr (by unfold Layout.sym_Caml_state Layout.sym_caml_all_opened_channels; omega)⟩
  have domC : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
    unfold word; rw [h.ready.domainWord]; rfl
  have framedF := custom.frame_counted (k + 1) c flagged ready stateOut domF
  have readyF := framedF.ready
  have stateEq := framedF.state
  have fieldKept (off : Nat) (b : off + 8 ≤ Layout.domainStateBytes) :
      word flagged (Boot.WhileMinRuntime.domain + off) = word c (Boot.WhileMinRuntime.domain + off) := by
    unfold word
    apply bytesT_keep
    intro j hj
    obtain ⟨e, he, elo, ehi⟩ := N.domain
    dsimp only at elo ehi
    refine keptF _ (outOpen _ (by arena_omega) (fun l => by omega) (by omega) fun hz => ?_) ?_
      (Or.inl (by arena_omega))
    · have r := N.recordsApart _ (head_mem N.channels h.headWord hz)
      unfold Gc.chanRecordBytes chanOffBuff ioBufferSize at r
      omega
    · rintro (g | ⟨_, _, no⟩)
      · unfold allocGlobal InRange at g; omega
      · exact no e he ⟨by omega, by omega⟩
  have ptrF : (runtimeFields flagged).youngPtr = (runtimeFields c).youngPtr := by
    simp only [runtimeFields, domainWord]
    rw [domF, domC, fieldKept Layout.off_young_ptr (by decide)]
  have limF : (runtimeFields flagged).youngLimit = (runtimeFields c).youngLimit := by
    simp only [runtimeFields, domainWord]
    rw [domF, domC, fieldKept Layout.off_young_limit (by decide)]
  have domainF : (word flagged Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
    rw [domF, domC]
  have input : Gc.CustomMemInput ((O.record.toNat, recordBytes) :: H) capacity
      (outSite code.doneEntry (sp - 16#64) O.record) flagged := {
    leaf := ⟨F.good, F.image, F.minstret, F.link, code.doneAligned, F.tick⟩
    heap := OCaml.Vm.Gc.HeapReady.keep_windows O.heap (ws := [⟨O.record.toNat, O.record.toNat + 72⟩])
      (fun w hw => by
        simp only [List.mem_singleton] at hw
        subst hw
        exact Or.inl ⟨_, List.mem_cons_self, Nat.le_refl _, by dsimp only; unfold recordBytes; omega⟩)
      (fun a out => flagsOut a (out _ List.mem_cons_self))
    context := N.context.frame (fun a read => by
      rw [byte_total, byte_total]
      have bounds := read.bounds
      have low := bounds.below
      have free := read.notFoot h.ready.heap N.domain
      apply keptF a (outW_openWindows_static h.frame low bounds.errno1 bounds.errno2 bounds.opened ?_ (fun hz => ?_))
        free (Or.inl (by arena_omega))
      · exact read.outside_record (size := recordBytes) O.low (by simpa only [recordBytes] using recDomain)
      · have member := head_mem N.channels h.headWord hz
        have headLow : heapStart ≤ head.toNat := by
          obtain ⟨e, he, elo, _⟩ := N.records head.toNat member
          have bound := h.ready.heap.block_bounds he
          exact Nat.le_trans bound.1 elo
        have apart := read.outside_record (size := Gc.chanRecordBytes) headLow (N.recordsApart _ member)
        exact headApart a hz (by simpa only [Gc.chanRecordBytes, Nat.add_assoc] using apart))
    pc := F.pc
    regs := F.regs
    frame := E.input.frame
    room := by rw [ptrF, limF]; exact N.room
    youngAligned := by rw [ptrF]; exact N.aligned }
  obtain ⟨allocated, run4, ⟨value, C, readyA⟩⟩ :=
    (custom.call _ capacity (outSite code.doneEntry (sp - 16#64) O.record) k flagged readyF input
      (by simpa only [Gc.customTableReserve, framedF.addresses.1] using h.credit)
      ((owned.frame stateEq).mono (fun e he => List.mem_cons_of_mem _ he))).run flagged ⟨F.pc, rfl⟩
  have block := C.block
  rw [ptrF] at block
  have vLow : heapStart ≤ value.toNat := by arena_omega
  have vHigh : value.toNat + 16 ≤ heapEnd := by arena_omega
  have vAlign : value.toNat % 8 = 0 := by have := N.aligned; omega
  have youngWord (a : Nat) (apart : a + 8 ≤ Boot.WhileMinRuntime.domain + 8 ∨ Boot.WhileMinRuntime.domain + 16 ≤ a) :
      a + 8 ≤ Gc.domainAddr flagged Layout.off_young_ptr ∨ Gc.domainAddr flagged Layout.off_young_ptr + 8 ≤ a := by
    unfold Gc.domainAddr; rw [domainF]; unfold Layout.off_young_ptr; omega
  -- the primitive's saves survive the opening, the flags and the custom block
  have slotKept (x : Nat) (lo : sp.toNat - 16 ≤ x) (hi : x + 8 ≤ sp.toNat) :
      bytesT allocated.σ.mem x 8 = bytesT entered.σ.mem x 8 := by
    apply bytesT_keep
    intro j hj
    have aboveHeap : heapEnd ≤ x + j := by arena_omega
    have o : OutW (openWindows (sp - 16#64) O.record head) (x + j) := by
      apply OCaml.Vm.Gc.outW_all
      intro w hw
      unfold openWindows at hw
      rcases List.mem_append.mp hw with hw | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · right; dsimp only; rw [sp16]; omega
        all_goals (right; dsimp only; try unfold recordBytes
                   arena_omega)
      · by_cases hz : head = 0#64
        · simp [hz] at hw
        · simp only [hz, ite_false, List.mem_singleton] at hw
          subst hw
          obtain ⟨⟨e, he, _, hi'⟩, _⟩ := h.headLive hz
          have bounds := h.ready.heap.block_bounds (q := e.1) (n := e.2) he
          right; dsimp only; arena_omega
    rw [C.kept _ (fun s => by have := (custom.apart flagged _ s).belowStack; omega) (notFootHigh _ _ aboveHeap)
        (Or.inr (by show (sp - 16#64).toNat ≤ x + j; rw [sp16]; omega)) (Or.inr (by unfold heapEnd at aboveHeap; omega))
        (youngWord _ (Or.inr (by arena_omega))),
      flagsOut _ (Or.inr (by arena_omega)), O.frame _ o (notFootHigh _ _ aboveHeap)]
  have s8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    have e := outFrame_slot (h.frame.resize (small := 16) (by decide) (by decide)) (off := 8) (by decide)
    rw [e]; omega
  have savedRa : bytesT allocated.σ.mem (sp.toNat - 8) 8 = ra := by
    rw [slotKept _ (by omega) (by omega), E.memory, ← s8]
    exact OCaml.Vm.Gc.word_writeLog_at _ (outSaveLog sp ra s0) 0 _ _ rfl (by
      simp only [outSaveLog, List.drop, OutLRange, and_true, s8, sp16]; omega)
  have savedS0 : bytesT allocated.σ.mem (sp.toNat - 16) 8 = s0 := by
    rw [slotKept _ (by omega) (by omega), E.memory, ← sp16]
    exact OCaml.Vm.Gc.word_writeLog_at _ (outSaveLog sp ra s0) 1 _ _ rfl trivial
  obtain ⟨d, run5, D⟩ := (code.done allocated C.toCustomMemReturned vLow vHigh vAlign h.frame savedRa savedS0
    h.ready.aligned).run allocated ⟨C.pc, rfl⟩
  -- the record, the list head and the block at the return
  have v8 : (value + 8#64).toNat = value.toNat + 8 := record_toNat (off := 8) (by omega)
  have doneOut (a : Nat) (out : a < value.toNat + 8 ∨ value.toNat + 16 ≤ a) :
      (d.σ.mem[a]?).getD 0 = (allocated.σ.mem[a]?).getD 0 := by
    have inside : LogInW [⟨value.toNat + 8, value.toNat + 16⟩] [((value + 8#64).toNat, 8, O.record)] :=
      ⟨Or.inl ⟨by dsimp only; rw [v8]; exact Nat.le_refl _, by dsimp only; rw [v8]; omega⟩, trivial⟩
    rw [D.memory, frameOn_writeLog _ _ _ inside a ⟨out, trivial⟩]
  have recordKept (a : Nat) (lo : O.record.toNat ≤ a) (hi : a < O.record.toNat + recordBytes) :
      (allocated.σ.mem[a]?).getD 0 = (flagged.σ.mem[a]?).getD 0 := by
    have hi' : a < O.record.toNat + 65616 := hi
    refine C.kept a (fun s => owned.fresh freshRecord ((stateEq a).mp s) ⟨lo, hi⟩)
      ?_ (Or.inl ?_) ?_ (youngWord a (by omega))
    · rintro (g | ⟨_, _, no⟩)
      · rcases allocGlobal_off_arena _ g with y | y <;> omega
      · exact no _ List.mem_cons_self ⟨lo, hi⟩
    · show a < (sp - 16#64).toNat - 576; rw [sp16]; arena_omega
    · rw [ptrF]; omega
  have recordD : OpenRecord code.out d.σ.mem O.record (fdOf v) head := by
    have r := rec.flagsDir (out := code.out)
    rw [← F.memory] at r
    exact (r.keep fun a lo hi => recordKept a lo (by unfold recordBytes; omega)).keep
      fun a lo hi => doneOut a (by omega)
  have headC : bytesT c.σ.mem 2147896128 8 = head := by
    have e := h.headWord
    rwa [read8_value] at e
  have headD : bytesT d.σ.mem 2147896128 8 = O.record := by
    rw [← headW]
    apply bytesT_keep
    intro j hj
    have notState (s : state flagged (2147896128 + j)) : False := by
      have e := (custom.apart flagged _ s).static (by omega)
      simp only [VsaIris.InExt, Layout.sym_caml_extra_heap_resources] at e
      omega
    rw [doneOut _ (Or.inl (by omega)), C.kept _ notState
        (by
          rintro (g | ⟨l, _, _⟩)
          · unfold allocGlobal InRange at g; omega
          · omega)
        (Or.inl (by show 2147896128 + j < (sp - 16#64).toNat - 576; rw [sp16]; arena_omega))
        (Or.inl (by rw [ptrF]; omega)) (youngWord _ (Or.inl (by omega))),
      flagsOut _ (Or.inl (by arena_omega))]
  have domD : word d Layout.sym_Caml_state = word allocated Layout.sym_Caml_state := by
    unfold word
    apply bytesT_keep
    intro j hj
    exact doneOut _ (Or.inl (by unfold Layout.sym_Caml_state; omega))
  have domainD : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    rw [domD, C.domain, domF]
  have fieldD (off : Nat) (b : off + 8 ≤ Layout.domainStateBytes) :
      word d ((word d Layout.sym_Caml_state).toNat + off) = word allocated ((word allocated Layout.sym_Caml_state).toNat + off) := by
    have dc : (word allocated Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
      rw [C.domain, domF, domC]
    rw [domD, dc]
    unfold word
    apply bytesT_keep
    intro j hj
    have hE : Boot.WhileMinRuntime.domain + 928 ≤ 0x80082000 := by decide
    exact doneOut _ (Or.inl (by unfold Layout.domainStateBytes at b; omega))
  have ptrD : (runtimeFields d).youngPtr = (runtimeFields c).youngPtr - 24 := by
    have e : (runtimeFields d).youngPtr = (runtimeFields allocated).youngPtr := by
      simp only [runtimeFields, domainWord]; rw [fieldD Layout.off_young_ptr (by decide)]
    rw [e, C.youngPtr, ptrF]
  have limD : (runtimeFields d).youngLimit = (runtimeFields c).youngLimit := by
    have e : (runtimeFields d).youngLimit = (runtimeFields allocated).youngLimit := by
      simp only [runtimeFields, domainWord]; rw [fieldD Layout.off_young_limit (by decide)]
    rw [e, C.youngLimit, limF]
  have framedD := custom.frame_counted k allocated d readyA (fun a s => doneOut a (by
    have m := (custom.apart allocated a s).minor
    simp only [Gc.minorRegion] at m
    omega)) domD
  have readyD := framedD.ready
  obtain ⟨baseF, endF⟩ := custom.addresses_frame ready stateOut
  obtain ⟨baseD, endD⟩ := custom.addresses_frame readyA (fun a s => doneOut a (by
    have m := (custom.apart allocated a s).minor
    simp only [Gc.minorRegion] at m
    omega))
  have allocIn : ∀ a, Gc.CustomAllocFoot d a → Gc.CustomAllocFoot c a ∨
      vsaFoot ((O.record.toNat, recordBytes) :: H) a := by
    intro a ha
    have atA := ((Gc.customFoot_congr baseD endD).2 a).mp ha
    rcases C.allocGrows a atA with old | free
    · exact Or.inl (((Gc.customFoot_congr baseF endF).2 a).mp old)
    · exact Or.inr free
  have heapD : ∃ H' cap', HeapReady H' cap' d ∧ Gc.CustomOwned state H' d ∧ Gc.CustomLedger H' d ∧
      (∀ e ∈ (O.record.toNat, recordBytes) :: H, e ∈ H') ∧
      capacity + Gc.customTableReserve d ≤ cap' + Gc.customTableReserve c := by
    obtain ⟨H', cap', spent, ownedA⟩ := C.credited
    have heapA := spent.heap
    have ledgerA := spent.ledger
    have sub := spent.retained
    refine ⟨H', cap', Gc.HeapReady.keep_windows heapA
      (ws := [⟨value.toNat + 8, value.toNat + 16⟩]) ?_
      (fun a ha => doneOut a (ha _ List.mem_cons_self)), ownedA.frame framedD.state, ledgerA.congr baseD endD, sub, by simpa only [Gc.customTableReserve, baseD, baseF] using spent.spend⟩
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    obtain ⟨e, he, elo, ehi⟩ := N.minor
    simp only [Gc.minorRegion] at elo ehi
    exact Or.inl ⟨e, sub e (List.mem_cons_of_mem _ he), by dsimp only; omega,
      by dsimp only; omega⟩

  refine ⟨d, run1.trans (run2.trans (run3.trans (run4.trans run5))), ⟨{
    entered := entered, opened := opened, flagged := flagged, allocated := allocated, value := value
    enter := E, opening := O, flags := F, custom := C, done := D
    record := recordD
    linked := {
      head := by rw [Layout.sym_caml_all_opened_channels, headD]; simp
      next := by rw [Layout.sym_caml_all_opened_channels, headC]; exact recordD.next
      nonzero := by arena_omega }
    channel := by
      rw [D.memory, ← v8]
      exact OCaml.Vm.Gc.word_writeLog_at _ [((value + 8#64).toNat, 8, O.record)] 0 _ _ rfl trivial
    ops := by
      rw [D.memory, bytesT_writeLog_out _ (by simp only [OutLRange, and_true, v8]; omega)]
      exact C.ops
    ready := readyD
    heap := heapD
    counted := by
      have step := (framedF.counts.trans (Gc.CustomCountStep.mk C.count)).trans framedD.counts
      simpa using step
    header := by
      rw [bytesT_keep (m := allocated.σ.mem) fun j hj => doneOut _ (Or.inl (by omega))]
      exact C.header
    block := block
    youngPtr := ptrD
    youngLimit := limD
    domain := domainD
    allocIn := allocIn
    kept := fun a notState notFoot o frame blk yw => by
      have youngW : a + 8 ≤ Gc.domainAddr flagged Layout.off_young_ptr ∨
          Gc.domainAddr flagged Layout.off_young_ptr + 8 ≤ a := by
        unfold Gc.domainAddr at yw ⊢; rw [domF]; exact yw
      have recOut := openOut a o
      rw [doneOut a (by omega), C.kept a (fun s => notState ((stateEq a).mp s)) ?_ ?_ (by rw [ptrF]; exact blk) youngW,
        keptF a o notFoot frame]
      · rintro (g | ⟨lo, hi, no⟩)
        · exact notFoot (Or.inl g)
        · exact notFoot (Or.inr ⟨lo, hi, fun e he => no e (List.mem_cons_of_mem _ he)⟩)
      · have base := ((outW_append _ _ a).mp o).1
        simp only [OutW, and_true] at base
        obtain ⟨st, _⟩ := base
        show a < (sp - 16#64).toNat - 576 ∨ (sp - 16#64).toNat ≤ a
        rw [sp16]; rw [sp16] at st; omega }⟩⟩

theorem ml_open_descriptor_out [LibraryLive live] (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 v head : BitVec 64) {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (k : Nat) (ready : Ready (k + 1) c) {chs : List Nat}
    (N : OutNursery H chs c) (h : OutInput live H capacity charge sp ra s0 s1 s2 v head c) :
    FnSummary 0x80015f50#64 (fun d => d = c)
      (fun d => Nonempty (OpenedOut openOutCode live Ready state Customs k H capacity charge sp ra s0 s1 s2 v head c d)) :=
  ml_open_descriptor openOutCode c H capacity charge sp ra s0 s1 s2 v head custom k ready N h

/-- `caml_ml_open_descriptor_out` keeps x20–x27 (among them `caml_interprete`'s
`env`, accumulator and dispatch registers). -/
theorem OpenedOut.keep_upper {code : OpenCode} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {left : Nat}
    {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
    (o : OpenedOut code live Ready state Customs left H capacity charge sp ra s0 s1 s2 v head c d) {k : Nat} {x : BitVec 64}
    (lo : 19 ≤ k) (hi : k ≤ 27) (h : gprGet c.σ k = some x) : gprGet d.σ k = some x := by
  have a := (o.enter.kept k (by omega) (by omega) (by simp; omega)).trans h
  have b := o.opening.keep_upper lo hi a
  have e := (o.flags.kept k (by omega) (by omega) (by simp; omega)).trans b
  have f := (o.custom.saved k (by simp; omega)).trans e
  exact (o.done.kept k (by omega) (by omega) (by simp; omega)).trans f

/-- Library readiness pins `gp`. -/
theorem _root_.OCaml.Vm.Boot.Startup.RuntimeReadyL.gp {H : List (Nat × Nat)} {capacity : Nat}
    {sp ra : BitVec 64} {c : Config} (r : RuntimeReadyL live H capacity sp ra c) :
    gprGet c.σ 3 = some VsaIris.MallocFast.gpV := by
  have v := r.readOnly.1 (3, VsaIris.MallocFast.gpV) (by simp [VsaIris.MallocFast.roR, VsaIris.gp])
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (r.platform.gpr 3 (by decide) (by decide))
  change (gprGet c.σ 3).getD 0 = _ at v
  rw [hx] at v ⊢
  exact congrArg some v

/-- `caml_open_descriptor_in` keeps register presence and `gp`. -/
theorem OpenedIn.gprs {H : List (Nat × Nat)} {capacity : Nat} {sp ra s0 s1 s2 fd head : BitVec 64}
    {c d : Config} (o : OpenedIn live H capacity sp ra s0 s1 s2 fd head c d)
    (gp : gprGet c.σ 3 = some VsaIris.MallocFast.gpV) : GprsKept c d where
  present n lo hi _ := o.link.gprs.present n lo hi (o.seek.gprs.present n lo hi
    (o.allocation.allocation.ready.platform.gpr n lo hi))
  gp := by
    show gprGet d.σ 3 = gprGet c.σ 3
    rw [gp]
    exact o.link.gprs.gp.trans (o.seek.gprs.gp.trans o.allocation.allocation.ready.gp)

/-- **`caml_ml_open_descriptor_out` keeps register presence and `gp`.** -/
theorem OpenedOut.gprs {code : OpenCode} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {left : Nat}
    {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
    (o : OpenedOut code live Ready state Customs left H capacity charge sp ra s0 s1 s2 v head c d) : GprsKept c d :=
  o.enter.gprs.trans ((o.opening.gprs o.enter.input.ready.gp).trans
    (o.flags.gprs.trans (o.custom.gprs.trans o.done.gprs)))

/-- **`caml_ml_open_descriptor_out` restores `s0`, `s1`, `s2`.** -/
theorem OpenedOut.keep_saved {code : OpenCode} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {left : Nat}
    {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
    (o : OpenedOut code live Ready state Customs left H capacity charge sp ra s0 s1 s2 v head c d) :
    gprGet d.σ 8 = some s0 ∧ gprGet d.σ 9 = some s1 ∧ gprGet d.σ 18 = some s2 := by
  refine ⟨o.done.s0Reg, ?_, ?_⟩
  · have e := (o.flags.kept 9 (by decide) (by decide) (by decide)).trans o.opening.link.s1Reg
    have f := (o.custom.saved 9 (by simp)).trans e
    exact (o.done.kept 9 (by decide) (by decide) (by decide)).trans f
  · have e := (o.flags.kept 18 (by decide) (by decide) (by decide)).trans o.opening.link.s2Reg
    have f := (o.custom.saved 18 (by simp)).trans e
    exact (o.done.kept 18 (by decide) (by decide) (by decide)).trans f

/-- `caml_ml_open_descriptor_out` keeps the console output. -/
theorem OpenedOut.output {code : OpenCode} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {left : Nat}
    {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
    (o : OpenedOut code live Ready state Customs left H capacity charge sp ra s0 s1 s2 v head c d) :
    Vsa.Machine.output d.σ = Vsa.Machine.output c.σ := by
  have i := o.opening.output
  simp only [Vsa.Machine.output] at i ⊢
  rw [o.done.output, o.custom.output, o.flags.output, i, o.enter.output]

/-- The output console descriptors' `lseek` slots. -/
theorem console_seekFd {c : Config} {v : BitVec 64} (runtime : ConsoleWrite.ConsoleRuntime c)
    (console : v = 3#64 ∨ v = 5#64) : SeekFd (fdOf v) c := by
  rcases console with rfl | rfl
  · rw [fdOf_stdout]; exact runtime.stdout.seekFd
  · rw [fdOf_stderr]; exact runtime.stderr.seekFd

/-! ### The premises from the F1 heap invariant -/

/-- **`caml_ml_open_descriptor_out(v)`'s premises from newlib's heap
invariant** (`Gc.LibHeapAt`), for a console descriptor while fewer than
`maxChannels` channels are open. The record's charge (65616) is within one
record's reservation, and the old list head is an open record. -/
theorem out_input {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    {sp ra s0 s1 s2 v : BitVec 64}
    (heap : Gc.LibHeapAt H cap chs c) (bound : chs.length < Gc.maxChannels)
    (leaf : LeafInput ra c) (platform : VsaOk live c)
    (gp : ∀ p ∈ VsaIris.MallocFast.roR, (vsaModel live).reg c p.1 = p.2)
    (stack : gprGet c.σ 2 = some sp) (frame : NativeFrame sp 592)
    (saved0 : gprGet c.σ 8 = some s0) (saved1 : gprGet c.σ 9 = some s1)
    (saved2 : gprGet c.σ 18 = some s2) (value : gprGet c.σ 10 = some v)
    (runtime : ConsoleWrite.ConsoleRuntime c) (descriptor : SeekFd (fdOf v) c) :
    OutInput live H (cap - 65616) 65616 sp ra s0 s1 s2 v
      (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)) c := by
  have room := heap.room
  have capEq : cap - 65616 + 65616 = cap := by
    unfold Gc.reserved Gc.recordCharge Gc.maxChannels Gc.tableCharge at room
    unfold Gc.maxChannels at bound
    split at room <;> omega
  refine {
    credit := by
      have credit := heap.open_credit bound
      omega
    ready := by rw [capEq]; exact RuntimeReadyL.of_heap heap.ready leaf platform gp stack
    frame := frame
    saved0 := saved0
    saved1 := saved1
    saved2 := saved2
    value := value
    charged := by unfold vsaChg recordBytes Vsa.Sim.roundUp16; decide
    runtime := runtime
    descriptor := descriptor
    headWord := rfl
    headLive := fun hz => ?_ }
  have mem := head_mem heap.channels rfl hz
  obtain ⟨e, he, lo, hi⟩ := heap.records _ mem
  have aligned := heap.recordsAligned _ mem
  dsimp only at lo hi
  unfold Gc.chanRecordBytes chanOffBuff ioBufferSize at hi
  exact ⟨⟨e, he, lo, by omega⟩, by omega⟩

/-- **The collector's side from the F1 heap invariant**: `Caml_state` and the
minor heap are covered regions, and every open record lies apart from them. -/
theorem out_nursery {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (heap : Gc.LibHeapAt H cap chs c)
    (context : Gc.CustomCallPins c)
    (room : (runtimeFields c).youngLimit + 24 ≤ (runtimeFields c).youngPtr)
    (aligned : (runtimeFields c).youngPtr % 8 = 0)
    (low : Gc.minorRegion.lo + 24 ≤ (runtimeFields c).youngPtr)
    (high : (runtimeFields c).youngPtr ≤ Gc.minorRegion.hi) : OutNursery H chs c where
  context := context
  custom := heap.custom
  space := heap.customSpace.restrict (fun e he => by
    simp only [Gc.namedBlocked, List.mem_append]
    exact Or.inl (Or.inr he))
  records := heap.records
  domain := heap.extents _ (by simp [Gc.f1Covered])
  minor := heap.extents _ (by simp [Gc.f1Covered])
  channels := heap.channels
  recordsApart r hr := heap.recordsApart r hr (Boot.WhileMinRuntime.domain, Layout.domainStateBytes)
    (by simp [Gc.f1Covered])
  room := room
  aligned := aligned
  low := low
  high := high

/-- Actual opening effects retain the independent native-call observations,
without a whole returned-runtime premise. -/
theorem OpenedOut.context {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {H : List (Nat × Nat)} {cap' charge : Nat}
    {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config} {chs : List Nat}
    (custom : Gc.CustomMemCall Ready state Customs)
    {code : OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c) (N : OutNursery H chs c) :
    Gc.CustomCallPins d := by
  have lower := h.frame.lower
  have lowM := N.low
  have recDomain := Gc.fresh_apart_covered o.opening.fresh N.domain (by decide) (n := recordBytes)
    (by unfold recordBytes; decide) (Nat.le_refl _)
  apply N.context.frame
  intro a read
  rw [byte_total, byte_total]
  have bounds := read.bounds
  have below := bounds.below
  have minor := bounds.minor
  simp only [Gc.minorRegion] at minor
  have domain : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
    rw [N.context.domain]; rfl
  apply o.kept a (read.not_state custom N.context) (read.notFoot h.ready.heap N.domain)
    (outW_openWindows_static h.frame below bounds.errno1 bounds.errno2 bounds.opened
      (read.outside_record (size := recordBytes) o.opening.low recDomain) ?_)
    (Or.inl (by arena_omega)) (Or.inl (by simp only [Gc.minorRegion] at lowM; omega)) ?_
  · intro nonzero
    have member := head_mem N.channels h.headWord nonzero
    have low : heapStart ≤ head.toNat := by
      obtain ⟨e, he, lo, _⟩ := N.records _ member
      have bound := h.ready.heap.block_bounds he
      exact Nat.le_trans bound.1 lo
    have apart := read.outside_record (size := Gc.chanRecordBytes) low (N.recordsApart _ member)
    unfold Gc.chanRecordBytes chanOffBuff ioBufferSize at apart
    omega
  · unfold Gc.domainAddr
    rw [domain]
    have apart := bounds.young
    simp only [Layout.off_young_ptr]
    omega

end OCaml.Vm.Primitives.Channel
