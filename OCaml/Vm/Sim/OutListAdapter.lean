import OCaml.Vm.Sim.OutListRun
import OCaml.Vm.Sim.OutListModel
import OCaml.Vm.Sim.CcallFootprint
import OCaml.Vm.Sim.StringAllocEntry
import OCaml.Vm.Sim.HeapWords
import OCaml.Vm.Sim.PayloadWindows
import OCaml.Vm.Primitives.Named.NamedHash
import OCaml.Vm.Sim.CcallNames

/-!
# `caml_ml_out_channels_list` at every C_CALL site

The machine summary (`out_list_machine`) runs at the callee entry; the
model's objects are represented from the nursery words (`listObjs_objAt`)
and the C_CALL return is framed by the walk's footprint predicate
(`ccall_observed_summary_on`). What the runtime supplies is the named
obligation `OutListRuntime L Ready state`: a6-gc's `CustomMemCall`, the custom
allocations' readiness for every listed channel, newlib's heap covering the
records, the nursery and the domain record, the runtime's state and newlib's
free space apart from the VM payload, and the layout's invariant across the
walk's writes.
-/

namespace OCaml.Vm.Sim.OutListWalk
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel.OutList
open LeanRV64DExecutable

/-- **A byte the VM payload reads** at `c`: the domain pointer and the
domain's `stack_high`/`trapsp`, the static roots, the code, the stack, the
live objects, the channel records (except their refcounts) and the primitive
table. The stack's range includes the C_CALL's saved env and return slots
below `sp`. -/
def VmPoint (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (sp : Nat) (a : Nat) : Prop :=
  (Layout.sym_Caml_state ≤ a ∧ a < Layout.sym_Caml_state + 8) ∨
  ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high ≤ a ∧
    a < (word c Layout.sym_Caml_state).toNat + Layout.off_stack_high + 8) ∨
  ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp ≤ a ∧
    a < (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8) ∨
  (∃ x ∈ [Layout.sym_caml_start_code, Layout.sym_caml_atom_table, Layout.sym_caml_global_data,
      Layout.sym_main_argv, Layout.sym_oo_last_id, Layout.sym_caml_prim_table + Layout.off_prim_contents],
    x ≤ a ∧ a < x + 8) ∨
  (∃ i w, P.code[i]? = some w ∧ pl.codeBase + 4 * i ≤ a ∧ a < pl.codeBase + 4 * i + 4) ∨
  (sp - 16 ≤ a ∧ a < sp + 8 * s.stack.length) ∨
  (∃ l b o, Live s.heap (roots P s) l ∧ pl.φ l = some b ∧ s.heap.get? l = some o ∧
    (b - 8 ≤ a ∧ a < b - 8 + 8 ∨ b ≤ a ∧ a < b + 8 * o.wosize)) ∨
  (∃ id ch b, s.world.chans[id]? = some ch ∧ cp id = some b ∧ b ≤ a ∧ a < b + chanOffBuff + ioBufferSize ∧
    (a < b + 64 ∨ b + 68 ≤ a)) ∨
  (∃ i name, P.prims[i]? = some name ∧
    (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i ≤ a ∧
    a < (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i + 8)

/-- A footprint missing every payload point misses the payload's words. -/
theorem PayloadMisses.of_points {W : Nat → Prop} {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp : Nat} (h : ∀ a, VmPoint P s c pl cp sp a → ¬ W a) : PayloadMisses W P s c pl cp sp where
  domain := fun i hi => h _ (Or.inl ⟨by omega, by omega⟩)
  stackHigh := fun i hi => h _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
  trapsp := fun i hi => h _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  codeBase := fun i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Layout.sym_caml_start_code, by simp, by omega, by omega⟩))))
  atomBase := fun i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Layout.sym_caml_atom_table, by simp, by omega, by omega⟩))))
  globals := fun i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Layout.sym_caml_global_data, by simp, by omega, by omega⟩))))
  argv := fun i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Layout.sym_main_argv, by simp, by omega, by omega⟩))))
  ooId := fun i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Layout.sym_oo_last_id, by simp, by omega, by omega⟩))))
  code := fun j w hj i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, w, hj, by omega, by omega⟩)))))
  stack := fun j v hj i hi => by
    have := (List.getElem?_eq_some_iff.1 hj).1
    exact h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
  header := fun l b o hl hp hg i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨l, b, o, hl, hp, hg, Or.inl ⟨by omega, by omega⟩⟩)))))))
  payload := fun l b o hl hp hg i hi => h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨l, b, o, hl, hp, hg, Or.inr ⟨by omega, by omega⟩⟩)))))))
  channels := fun id ch b hc hp j hj hn => h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨id, ch, b, hc, hp, by omega, by omega, by omega⟩))))))))

/-- The placed channel records at a C_CALL entry: newlib blocks of `H`,
apart from the minor heap, the domain record `D` and each other. -/
structure RecordsPlaced (H : List (Nat × Nat)) (D : Nat) (chs : List Nat) : Prop where
  low : ∀ r ∈ chs, Vsa.Sim.DlHeap.heapStart ≤ r
  high : ∀ r ∈ chs, r + recBytes ≤ Vsa.Sim.DlHeap.heapEnd
  minor : ∀ r ∈ chs, r + recBytes ≤ Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ r
  domain : ∀ r ∈ chs, r + recBytes ≤ D ∨ D + Layout.domainStateBytes ≤ r
  apart : ∀ r ∈ chs, ∀ r' ∈ chs, r ≠ r' → r + recBytes ≤ r' ∨ r' + recBytes ≤ r
  covered : ∀ r ∈ chs, ∃ x ∈ H, x.1 ≤ r ∧ r + recBytes ≤ x.1 + x.2

/-- What `caml_ml_out_channels_list` may write, at its entry `c`: the native
stack, the free nursery, records' refcounts, the domain's nursery words and
`local_roots`, the runtime's custom-allocation state and newlib's own bytes. -/
def OutListWrites (state : Config → Nat → Prop) (H : List (Nat × Nat)) (chs : List Nat) (c : Config) (a : Nat) :
    Prop :=
  Vsa.Sim.DlHeap.heapEnd ≤ a ∨ ((runtimeFields c).youngLimit ≤ a ∧ a < (runtimeFields c).youngPtr) ∨
    (∃ r ∈ chs, r + 64 ≤ a ∧ a < r + 68) ∨
    ((word c Layout.sym_Caml_state).toNat ≤ a ∧ a < (word c Layout.sym_Caml_state).toNat + 16) ∨
    ((word c Layout.sym_Caml_state).toNat + Layout.off_local_roots ≤ a ∧
      a < (word c Layout.sym_Caml_state).toNat + Layout.off_local_roots + 8) ∨
    state c a ∨ VsaIris.VsaHeap.vsaFoot H a

/-- **The runtime's side of `caml_ml_out_channels_list`** (named obligation;
F1: a6-gc's `CustomMemCall` instance with a0-boot's newlib heap). At a C_CALL
entry of the layout:
* the custom allocations are ready for every listed channel;
* newlib's heap `H` covers the minor heap, the domain record and the channel
  records, which lie apart (`RecordsPlaced`);
* the VM payload lies below the arena's end, in live blocks of `H`, apart from
  the runtime's state;
* the layout's invariant survives the primitive's writes (`OutListWrites`)
  when `young_ptr` stays in the nursery. -/
structure OutListRuntime (L : OCaml.Layout) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) :
    Prop where
  custom : Gc.CustomMemCall Ready state
  entry : ∀ (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (sp high : Nat),
    L.runtimeOk c → OCaml.LoopGeometry L P s c pl cp high →
    ∃ k H cap, Ready (k + (outChannelIds s.world).length) c ∧ OCaml.Vm.Boot.Startup.HeapReady H cap c ∧
      RecordsPlaced H (word c Layout.sym_Caml_state).toNat (Gc.placedChannels cp s.world.chans.length) ∧
      (∃ x ∈ H, x.1 ≤ Gc.minorRegion.lo ∧ Gc.minorRegion.hi ≤ x.1 + x.2) ∧
      (∃ x ∈ H, x.1 ≤ (word c Layout.sym_Caml_state).toNat ∧
        (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ x.1 + x.2) ∧
      ((word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ Gc.minorRegion.lo ∨
        Gc.minorRegion.hi ≤ (word c Layout.sym_Caml_state).toNat) ∧
      ∀ a, VmPoint P s c pl cp sp a → a < Vsa.Sim.DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧
        ¬ state c a
  runtime : ∀ (P : Prog) (s : St) (c after : Config) (pl : Place) (cp : ChanPlace) (high : Nat)
    (H : List (Nat × Nat)), L.runtimeOk c → OCaml.LoopGeometry L P s c pl cp high →
    (∀ a, ¬ OutListWrites state H (Gc.placedChannels cp s.world.chans.length) c a → byte after a = byte c a) →
    (runtimeFields c).youngLimit ≤ (runtimeFields after).youngPtr →
    (runtimeFields after).youngPtr ≤ (runtimeFields c).youngPtr →
    (runtimeFields after).youngPtr % 8 = 0 → L.runtimeOk after

theorem words_allocAll (os : List Obj) : ∀ h : Heap, (allocAll h os).words = h.words + blockWords os := by
  induction os with
  | nil => intro h; rfl
  | cons o os ih => intro h; simp only [allocAll, blockWords, ih, Heap.words_alloc]; omega

/-- The walk at a C_CALL entry `c`: the native `sp` is `N`, the domain words
read at `c`, the placed channel records, newlib's blocks `H`. -/
def entryWalk (c : Config) (N : Nat) (cp : ChanPlace) (len : Nat) (H : List (Nat × Nat))
    (state : Config → Nat → Prop) : Walk where
  sp := BitVec.ofNat 64 (N - 128)
  roots := bytesT c.σ.mem (BitVec.ofNat 64 (word c Layout.sym_Caml_state).toNat + 288#64).toNat 8
  D := (word c Layout.sym_Caml_state).toNat
  Y := (runtimeFields c).youngPtr
  Lm := (runtimeFields c).youngLimit
  chs := Gc.placedChannels cp len
  H0 := H
  S := state c

/-- **What the C_CALL entry gives the walk.** -/
structure OutListEntry (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (ra : BitVec 64) (P : Prog)
    (s : St) (pl : Place) (cp : ChanPlace) (sp : Nat) (c : Config) (w : Walk) (k cap : Nat) (s0 : BitVec 64) :
    Prop where
  geometry : WalkGeometry w (outChannelIds s.world).length
  input : OutListInput w Ready k cap ra s0 c
  listed : listedRecs c.σ.mem w.chs = (outChannelIds s.world).map fun id => (cp id).getD 0
  payload : ∀ a, VmPoint P s c pl cp sp a → a < Vsa.Sim.DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot w.H0 a ∧
    ¬ state c a
  /-- the walk's entry state is the runtime's at `c` -/
  stateS : ∀ a, w.S a ↔ state c a
  chs : w.chs = Gc.placedChannels cp s.world.chans.length
  domain : w.D = (word c Layout.sym_Caml_state).toNat
  young : w.Y = (runtimeFields c).youngPtr
  limit : w.Lm = (runtimeFields c).youngLimit

/-- **The walk's inputs at the callee entry** of a C_CALL. -/
theorem out_list_entry {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env : BitVec 64} {c : Config} {Ready : Nat → Config → Prop}
    {state : Config → Nat → Prop} (rt : OutListRuntime L Ready state)
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (hentry : entry = Layout.sym_caml_ml_out_channels_list)
    (fits : s.heap.words + 6 * (outChannelIds s.world).length ≤ L.budget.heapWords) :
    ∃ w k cap s0, OutListEntry Ready state ra P s pl cp sp c w k cap s0 := by
  have input := setup.input
  have g := setup.geometry
  have ng := g.nursery
  obtain ⟨N, e⟩ := StringAllocEntry.of_setup setup fits
  obtain ⟨k, H, cap, ready, heap, recs, ⟨xm, xmIn, xml, xmh⟩, ⟨xd, xdIn, xdl, xdh⟩, dap, pay⟩ :=
    rt.entry P s c pl cp sp high input.runtime g
  have xdb := heap.block_bounds (q := xd.1) (n := xd.2) xdIn
  have nl := e.nativeLow; have nh := e.nativeHigh; have na := e.nativeAligned
  have dh := e.domainHigh; have da := e.domainAligned; have rm := e.room
  have yh := ng.nurseryHigh; have ll := ng.nurseryLow; have ya := ng.aligned
  have hr : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have hs : Layout.sym_stack_top = 0x88000000 := rfl
  have hn : nativeHeadroom = 4096 := rfl
  have N128 : (BitVec.ofNat 64 (N - 128)).toNat = N - 128 := toNat_ofNat_small (by omega)
  -- the records are 8-aligned and nonzero (`ChanAt`)
  have chanAt : ∀ id, id < s.world.chans.length → ∃ a ch, s.world.chans[id]? = some ch ∧ cp id = some a ∧
      ChanAt c a ch ∧ 0 < a ∧ a + 80 < 2 ^ 64 := fun id hid => by
    obtain ⟨a, ha, at_⟩ := input.data.world.chans id _ (List.getElem?_eq_getElem hid)
    have mem : a ∈ Gc.placedChannels cp s.world.chans.length := Gc.mem_placedChannels.2 ⟨id, hid, ha⟩
    have := recs.low a mem; have := recs.high a mem
    exact ⟨a, _, List.getElem?_eq_getElem hid, ha, at_, by walk_omega, by walk_omega⟩
  have aligned : ∀ r ∈ Gc.placedChannels cp s.world.chans.length, r % 8 = 0 := fun r hr' => by
    obtain ⟨id, hid, hp⟩ := Gc.mem_placedChannels.1 hr'
    obtain ⟨a, ch, hc, ha, at_, _⟩ := chanAt id hid
    rw [hp, Option.some.injEq] at ha; subst ha
    exact at_.aligned
  have listed := listedRecs_placed chanAt
  obtain ⟨s0, h8⟩ : ∃ s0, gpr c 8 = some s0 :=
    Option.isSome_iff_exists.mp (setup.calleeSaved 8 (by simp))
  let w := entryWalk c N cp s.world.chans.length H state
  have nN : (outChannelIds s.world).length = (listedRecs c.σ.mem w.chs).length := by
    show _ = (listedRecs c.σ.mem (Gc.placedChannels cp s.world.chans.length)).length
    rw [listed, List.length_map]
  obtain ⟨wY, wL⟩ := words_of_fields (c := c) (D := (word c Layout.sym_Caml_state).toNat)
    (Y := (runtimeFields c).youngPtr) (Lm := (runtimeFields c).youngLimit) (by walk_omega) (by walk_omega)
    (by walk_omega) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl rfl
  have pcE : pcOf c = some entryPc := by rw [setup.target, hentry]; rfl
  refine ⟨w, k, cap, s0, {
    geometry := {
      spLow := by show _ ≤ (BitVec.ofNat 64 (N - 128)).toNat; rw [N128]; walk_omega
      spHigh := by show (BitVec.ofNat 64 (N - 128)).toNat + 128 ≤ _; rw [N128]; walk_omega
      spAligned := by show (BitVec.ofNat 64 (N - 128)).toNat % 16 = 0; rw [N128]; omega
      domainLow := by show _ ≤ (word c Layout.sym_Caml_state).toNat; walk_omega
      domainHigh := by show (word c Layout.sym_Caml_state).toNat + _ ≤ _; walk_omega
      domainAligned := da
      nurseryLow := ll
      nurseryHigh := yh
      youngAligned := ya
      room := by show (runtimeFields c).youngLimit + _ ≤ (runtimeFields c).youngPtr; omega
      domainApart := dap
      records := fun r hr' => ⟨recs.low r hr', recs.high r hr', aligned r hr', recs.minor r hr', recs.domain r hr'⟩
      recordsApart := recs.apart
      coverMinor := ⟨xm, xmIn, xml, xmh⟩
      coverRecords := recs.covered
      coverDomain := ⟨xd, xdIn, xdl, xdh⟩
      stateApart := fun a hs => ⟨c, rt.custom.apart c a hs, ng.channelsListed, rfl⟩ }
    input := {
      leaf := input.toLeafInput
      pc := pcE
      stack := by
        have eqN : BitVec.ofNat 64 (N - 128) + 128#64 = BitVec.ofNat 64 N := BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_add, N128, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
        show gpr c 2 = some (BitVec.ofNat 64 (N - 128) + 128#64)
        rw [eqN]; exact e.stack
      s0 := h8
      idle := input.loop.htifIdle
      domain := by
        show bytesT c.σ.mem (2147896584#64).toNat 8 = BitVec.ofNat 64 (bytesT c.σ.mem Layout.sym_Caml_state 8).toNat
        exact BitVec.eq_of_toNat_eq (toNat_ofNat_small (BitVec.isLt _)).symm
      roots := rfl
      young := wY
      limit := wL
      opened := ng.channelsListed
      ready := by rw [← nN]; exact ready
      heap := heap }
    listed := listed
    payload := pay
    stateS := fun _ => Iff.rfl
    chs := rfl
    domain := rfl
    young := rfl
    limit := rfl }⟩

/-- **A log missing the payload misses every payload point.** -/
theorem VmPoint.outL {log : List WEntry} {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp a : Nat} (out : PayloadOutside log P s c pl cp sp) (bind : BindingsOutside log P c)
    (stackBytes : ∀ a, sp - 16 ≤ a → a < sp + 8 * s.stack.length → OutL log a)
    (h : VmPoint P s c pl cp sp a) : OutL log a := by
  rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨x, hx, lo, hi⟩ | ⟨i, w, hw, lo, hi⟩ | ⟨lo, hi⟩ |
      ⟨l, b, o, hl, hp, hg, ⟨lo, hi⟩ | ⟨lo, hi⟩⟩ | ⟨id, ch, b, hc, hp, lo, hi, _⟩ | ⟨i, name, hn, lo, hi⟩
  · exact outL_of_range out.domain lo hi
  · exact outL_of_range out.stackHigh lo hi
  · exact outL_of_range out.trapsp lo hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact outL_of_range out.codeBase lo hi
    · exact outL_of_range out.atomBase lo hi
    · exact outL_of_range out.globals lo hi
    · exact outL_of_range out.argv lo hi
    · exact outL_of_range out.ooId lo hi
    · exact outL_of_range bind.contents lo hi
  · exact outL_of_range (out.code i w hw) lo hi
  · exact stackBytes a lo hi
  · exact outL_of_range (out.heap l b o hl hp hg).header lo hi
  · exact outL_of_range (out.heap l b o hl hp hg).payload lo hi
  · exact outL_of_range (out.channels id ch b hc hp) lo (by omega)
  · exact outL_of_range (bind.entries i name hn) lo hi

/-- **No payload point is a record's refcount byte.** -/
theorem VmPoint.not_refcount {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high a : Nat}
    (g : OCaml.Vm.Sim.StackGeometry P s c pl cp high) (stackLow : high - Layout.stackBytes ≤ sp - 16)
    (stack : sp + 8 * s.stack.length = high) (h : VmPoint P s c pl cp sp a)
    {id : Nat} {ch : Chan} {r : Nat} (hc : s.world.chans[id]? = some ch) (hp : cp id = some r)
    (lo : r + 64 ≤ a) (hi : a < r + 68) : False := by
  have rl := g.channelLow id ch r hc hp
  have rb : chanOffBuff + ioBufferSize = 65608 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  rcases h with ⟨lo', hi'⟩ | ⟨lo', hi'⟩ | ⟨lo', hi'⟩ | ⟨x, hx, lo', hi'⟩ | ⟨i, w, hw, lo', hi'⟩ |
      ⟨lo', hi'⟩ | ⟨l, b, o, hl, hp', hg, ⟨lo', hi'⟩ | ⟨lo', hi'⟩⟩ |
      ⟨id', ch', b, hc', hp'', lo', hi', ex⟩ | ⟨i, name, hn, lo', hi'⟩
  · simp only [Layout.sym_Caml_state] at lo' hi'; omega
  · have := (g.domainChannels id ch r hc hp).1; simp only [Layout.domainStateBytes, Layout.off_stack_high] at this hi' lo'
    omega
  · have := (g.domainChannels id ch r hc hp).1; simp only [Layout.domainStateBytes, Layout.off_trapsp] at this hi' lo'
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (simp only [Layout.sym_caml_start_code, Layout.sym_caml_atom_table, Layout.sym_caml_global_data,
          Layout.sym_main_argv, Layout.sym_oo_last_id] at lo' hi'; omega)
      | (have := (g.channelPrims id ch r hc hp); simp only [Layout.sym_caml_prim_table, Layout.off_prim_contents] at lo' hi'; omega)
  · have cc := (g.channelCode id ch r hc hp).1
    have ib := (Array.getElem?_eq_some_iff.1 hw).1
    dsimp only at cc; omega
  · have cs := (g.channels id ch r hc hp).1
    simp only [stackWindow] at cs; omega
  · have hc' := (g.heapChannels l b o hp' hg id ch r hc hp).1; dsimp only at hc'; omega
  · have hc' := (g.heapChannels l b o hp' hg id ch r hc hp).1; dsimp only at hc'; omega
  · by_cases same : id' = id
    · subst same
      rw [hp] at hp''; cases hp''
      omega
    · have := g.channelsApart id' id ch' ch b r same hc' hc hp'' hp; omega
  · have cpr := (g.channelPrims id ch r hc hp i name hn).1; dsimp only at cpr; omega

/-- The walk's own windows as a footprint log: the native frames, the free
nursery, `young_limit`, `young_ptr` and `local_roots`. -/
def synLog (w : Walk) : List WEntry :=
  [(w.sp.toNat - 576, 704, 0#64), (w.Lm, w.Y - w.Lm, 0#64), (w.D, 8, 0#64), (w.D + 8, 8, 0#64), (w.D + 288, 8, 0#64)]

/-- **Everything `caml_ml_out_channels_list` writes**: its own windows, the
records' refcounts, the runtime's state and newlib's own bytes. -/
def outW (w : Walk) (state : Config → Nat → Prop) (a : Nat) : Prop :=
  ¬ OutL (synLog w) a ∨ (∃ r ∈ w.chs, r + 64 ≤ a ∧ a < r + 68) ∨ StateAt w state a ∨
    VsaIris.VsaHeap.vsaFoot w.H0 a

/-- The walk's windows are payload windows of the entry's geometry. -/
theorem synLog_windows {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {ra : BitVec 64} {L : OCaml.Layout}
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {c : Config} {w : Walk} {k cap : Nat}
    {s0 : BitVec 64} (g : OCaml.LoopGeometry L P s c pl cp high) (ent : OutListEntry Ready state ra P s pl cp sp c w k cap s0)
    {top : Nat} (htop : top ≤ high) :
    LogWindows (synLog w) P s c pl cp top high [Layout.off_young_limit, Layout.off_young_ptr, Layout.off_local_roots] := by
  have wg := ent.geometry
  have spl := wg.spLow; have nl := wg.nurseryLow; have rm := wg.room
  have c576 : Gc.customStackBytes = 576 := rfl
  have hD := ent.domain; have hY := ent.young; have hL := ent.limit
  refine ⟨g.toStackGeometry, ⟨[⟨w.sp.toNat - 576, w.sp.toNat + 128⟩, Gc.nurseryFree c,
    ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_young_limit, (word c Layout.sym_Caml_state).toNat + Layout.off_young_limit + 8⟩,
    ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr, (word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr + 8⟩,
    ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_local_roots, (word c Layout.sym_Caml_state).toNat + Layout.off_local_roots + 8⟩],
    ?_, ?_⟩, htop, by decide⟩
  · simp only [synLog, LogInW, InsideW, Gc.nurseryFree, Layout.off_young_limit, Layout.off_young_ptr,
      Layout.off_local_roots, hD, hY, hL, and_true]
    refine ⟨Or.inl ⟨by omega, by omega⟩, Or.inr (Or.inl ⟨by omega, by omega⟩),
      Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)), Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact .separated (Gc.WindowSeparated.of_above g.toStackGeometry (by simp only; walk_omega))
    · exact .separated g.nursery.toWindowSeparated
    · exact .field (by simp)
    · exact .field (by simp)
    · exact .field (by simp)

/-- **The payload misses everything the primitive writes.** -/
theorem outW_payload {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {ra : BitVec 64} {L : OCaml.Layout}
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {c : Config} {w : Walk} {k cap : Nat}
    {s0 : BitVec 64} (g : OCaml.LoopGeometry L P s c pl cp high) (ent : OutListEntry Ready state ra P s pl cp sp c w k cap s0)
    (stack : sp + 8 * s.stack.length = high) (low : high - Layout.stackBytes ≤ sp - 16) (sp16 : 16 ≤ sp) :
    PayloadMisses (outW w state) P s c pl cp sp ∧ ∀ a, VmPoint P s c pl cp sp a → ¬ outW w state a := by
  have lw := synLog_windows g ent (top := sp - 16) (by omega)
  have out : PayloadOutside (synLog w) P s c pl cp sp :=
    lw.payload stack (by omega) (by omega) (by decide) (by decide)
  have bind := lw.bindings
  have gd := g.domain
  have stackBytes : ∀ a, sp - 16 ≤ a → a < sp + 8 * s.stack.length → OutL (synLog w) a := fun a lo hi =>
    outL_of_range (n := 1) (lw.out (fun v sep => Gc.outW_sub sep.stack (by omega)
      (by have := g.statics; omega)) (.inr lo) fun off member => by
        have := lw.fits off member
        obtain ⟨gd, -⟩ := gd
        simp only [stackWindow] at gd
        omega) (Nat.le_refl _) (by omega)
  have pts : ∀ a, VmPoint P s c pl cp sp a → ¬ outW w state a := by
    intro a hp hw
    rcases hw with o | ⟨r, hr, lo, hi⟩ | hs | foot
    · exact o (VmPoint.outL out bind stackBytes hp)
    · rw [ent.chs] at hr
      obtain ⟨id, hid, hcp⟩ := Gc.mem_placedChannels.1 hr
      exact VmPoint.not_refcount g.toStackGeometry low stack hp (List.getElem?_eq_getElem hid) hcp lo hi
    · exact (ent.payload a hp).2.2 ((ent.stateS a).mp hs)
    · exact (ent.payload a hp).2.1 foot
  exact ⟨PayloadMisses.of_points pts, pts⟩

theorem synLog_out {w : Walk} {a : Nat} (h : OutL (synLog w) a) :
    (a < w.sp.toNat - 576 ∨ w.sp.toNat - 576 + 704 ≤ a) ∧ (a < w.Lm ∨ w.Lm + (w.Y - w.Lm) ≤ a) ∧
    (a < w.D ∨ w.D + 8 ≤ a) ∧ (a < w.D + 8 ∨ w.D + 8 + 8 ≤ a) ∧ (a < w.D + 288 ∨ w.D + 288 + 8 ≤ a) := by
  simp only [synLog, OutL, and_true] at h; exact h

/-- **The return's byte frame** over everything the primitive writes. -/
theorem outW_frame {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {ra s0 : BitVec 64} {c f : Config} (g : WalkGeometry w n) (ret : OutListReturned w Ready state k ra s0 c f)
    (x : Nat) (hx : ¬ outW w state x) : byte f x = byte c x := by
  have spl := g.spLow; have rm := g.room
  have c576 : Gc.customStackBytes = 576 := rfl
  have o : OutL (synLog w) x := Classical.byContradiction fun h => hx (Or.inl h)
  obtain ⟨e0, e1, e2, e3, e4⟩ := synLog_out o
  refine ret.frame x (fun hw => hx ?_) (by omega) (by omega)
  rcases hw with ⟨lo, hi⟩ | ⟨lo, hi⟩ | rf | ⟨lo, hi⟩ | hs | foot
  · exact absurd o (fun _ => by omega)
  · exact absurd o (fun _ => by omega)
  · exact Or.inr (Or.inl rf)
  · exact absurd o (fun _ => by omega)
  · exact Or.inr (Or.inr (Or.inl hs))
  · exact Or.inr (Or.inr (Or.inr foot))

/-- What the primitive writes is what the runtime's frame allows. -/
theorem outW_writes {w : Walk} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {ra : BitVec 64}
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp : Nat} {c : Config} {k cap : Nat} {s0 : BitVec 64}
    (ent : OutListEntry Ready state ra P s pl cp sp c w k cap s0) {a : Nat} (h : outW w state a) :
    OutListWrites state w.H0 (Gc.placedChannels cp s.world.chans.length) c a := by
  have g := ent.geometry
  have spl := g.spLow; have rm := g.room
  have c576 : Gc.customStackBytes = 576 := rfl
  have hD := ent.domain; have hY := ent.young; have hL := ent.limit
  rcases h with o | ⟨r, hr, lo, hi⟩ | sc | foot
  · simp only [synLog, OutL, and_true] at o
    by_cases h0 : w.sp.toNat - 576 ≤ a ∧ a < w.sp.toNat + 128
    · exact Or.inl (by walk_omega)
    by_cases h1 : w.Lm ≤ a ∧ a < w.Y
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    by_cases h2 : w.D ≤ a ∧ a < w.D + 16
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    by_cases h4 : w.D + 288 ≤ a ∧ a < w.D + 296
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only [Layout.off_local_roots]; omega,
        by simp only [Layout.off_local_roots]; omega⟩))))
    exact absurd (⟨by omega, by omega, by omega, by omega, by omega⟩ :
      (a < w.sp.toNat - 576 ∨ w.sp.toNat - 576 + 704 ≤ a) ∧ (a < w.Lm ∨ w.Lm + (w.Y - w.Lm) ≤ a) ∧
      (a < w.D ∨ w.D + 8 ≤ a) ∧ (a < w.D + 8 ∨ w.D + 8 + 8 ≤ a) ∧ (a < w.D + 288 ∨ w.D + 288 + 8 ≤ a)) o
  · rw [ent.chs] at hr; exact Or.inr (Or.inr (Or.inl ⟨r, hr, lo, hi⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((ent.stateS a).mp sc))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr foot)))))

/-- **The primitive bindings across a footprint predicate.** -/
theorem bindings_frame_on {P : Prog} {s : St} {c c' : Config} {pl : Place} {cp : ChanPlace} {sp : Nat}
    {W : Nat → Prop} (h : PrimitiveBindings P c) (pts : ∀ a, VmPoint P s c pl cp sp a → ¬ W a)
    (memory : ∀ x, ¬ W x → byte c' x = byte c x) : PrimitiveBindings P c' := by
  have contents : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) :=
    Misses.word (fun i hi => pts _ (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Layout.sym_caml_prim_table + Layout.off_prim_contents, by simp, by omega, by omega⟩))))) memory
  constructor
  intro i name hi
  obtain ⟨entry, he, target⟩ := h.targets i name hi
  refine ⟨entry, he, ?_⟩
  unfold primitiveTarget at target ⊢
  rw [contents, Misses.word (fun j hj => pts _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨i, name, hi, by omega, by omega⟩))))))))) memory]
  exact target

theorem listObjs_length (ids : List Nat) : ∀ (size : Nat) (acc : Val), (listObjs size acc ids).length = 2 * ids.length := by
  induction ids with
  | nil => intro _ _; rfl
  | cons id ids ih => intro size acc; simp only [listObjs, List.length_cons, ih]; omega

theorem listObjs_wosize (ids : List Nat) : ∀ (size : Nat) (acc : Val) (i : Nat) (o : Obj),
    (listObjs size acc ids)[i]? = some o → o.wosize = 2 := by
  induction ids with
  | nil => intro _ _ i _ h; simp [listObjs] at h
  | cons id ids ih =>
    intro size acc i o h
    match i, h with
    | 0, h => simp only [listObjs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
    | 1, h =>
      simp only [listObjs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
    | i + 2, h => simp only [listObjs, List.getElem?_cons_succ] at h; exact ih _ _ i o h

/-- The new objects point only at new objects (or at the initial accumulator). -/
theorem listObjs_fields (ids : List Nat) : ∀ (size : Nat) (acc : Val) (i t : Nat) (fs : List Val),
    (listObjs size acc ids)[i]? = some (Obj.block t fs) → ∀ u ∈ fs, ∀ l, Val.loc? u = some l →
      (size ≤ l ∧ l < size + 2 * ids.length) ∨ Val.loc? acc = some l := by
  induction ids with
  | nil => intro _ _ i _ _ h; simp [listObjs] at h
  | cons id ids ih =>
    intro size acc i t fs h u hu l hl
    match i, h with
    | 0, h => simp [listObjs] at h
    | 1, h =>
      simp only [listObjs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq, Obj.block.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · simp only [Val.loc?, Option.some.injEq] at hl; subst hl; left; simp only [List.length_cons]; omega
      · exact Or.inr hl
    | i + 2, h =>
      simp only [listObjs, List.getElem?_cons_succ] at h
      rcases ih (size + 2) (.ptr (size + 1) 0) i t fs h u hu l hl with ⟨lo, hi⟩ | old
      · left; simp only [List.length_cons]; omega
      · simp only [Val.loc?, Option.some.injEq] at old; subst old; left; simp only [List.length_cons]; omega

theorem listVal_loc (ids : List Nat) : ∀ (size : Nat) (acc : Val) (l : Nat), Val.loc? (listVal size acc ids) = some l →
    (size ≤ l ∧ l < size + 2 * ids.length) ∨ Val.loc? acc = some l := by
  induction ids with
  | nil => intro _ _ _ h; exact Or.inr h
  | cons id ids ih =>
    intro size acc l h
    rcases ih (size + 2) (.ptr (size + 1) 0) l h with ⟨lo, hi⟩ | old
    · left; simp only [List.length_cons]; omega
    · simp only [Val.loc?, Option.some.injEq] at old; subst old; left; simp only [List.length_cons]; omega

/-- The state after `caml_ml_out_channels_list`'s model, before the C_CALL return. -/
def listState (s : St) : St :=
  let ids := outChannelIds s.world
  { s with heap := allocAll s.heap (listObjs s.heap.size (Val.int 0) ids), accu := listVal s.heap.size (Val.int 0) ids,
           world := s.world }

/-- **The payload after the primitive**: the entry's payload framed to the
return, extended with the listed ids' channel objects and cons cells, the
list in the accumulator. -/
theorem out_list_payload {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {ra : BitVec 64}
    {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {c f : Config}
    {w : Walk} {k cap : Nat} {s0 : BitVec 64} (g : OCaml.LoopGeometry L P s c pl cp high)
    (ent : OutListEntry Ready state ra P s pl cp sp c w k cap s0)
    (data : VmPayload P s c pl cp sp high) (stack : sp + 8 * s.stack.length = high)
    (low : high - Layout.stackBytes ≤ sp - 16) (sp16 : 16 ≤ sp) (ret : OutListReturned w Ready state k ra s0 c f)
    (placed : ∀ i, i < 2 * (outChannelIds s.world).length →
      pl.φ (s.heap.size + i) = some (w.Y - 24 * i - 16))
    (chanAt : ∀ id ∈ outChannelIds s.world, cp id = some ((cp id).getD 0) ∧ (cp id).getD 0 < 2 ^ 64)
    (outputEq : output f.σ = output c.σ) :
    VmPayload P (listState s) f pl cp sp high := by
  have wg := ent.geometry
  have rm := wg.room; have nh := wg.nurseryHigh; have nl := wg.nurseryLow
  obtain ⟨misses, _⟩ := outW_payload g ent stack low sp16
  have h0 := OCaml.Vm.Sim.VmPayload.frame_on data misses (outW_frame wg ret) outputEq
  have len := listObjs_length (outChannelIds s.world) s.heap.size (.int 0)
  have nurs := ret.nursery
  rw [ent.listed] at nurs
  have hr : HeapRepr f pl cp P (listState s) := by
    apply heap_allocate_all h0.heap (fun i => w.Y - 24 * i - 16)
    · intro i t fs hi u hu l hl
      rcases listObjs_fields (outChannelIds s.world) s.heap.size (.int 0) i t fs hi u hu l hl with h | h
      · exact Or.inl (by rw [len]; exact h)
      · simp [Val.loc?] at h
    · intro l hl
      rcases listVal_loc (outChannelIds s.world) s.heap.size (.int 0) l hl with h | h
      · exact Or.inl (by rw [len]; exact h)
      · simp [Val.loc?] at h
    · intro i hi; rw [len] at hi; exact placed i hi
    · intro i o hio
      have := listObjs_objAt (c := f) (pl := pl) (cp := cp) (R := fun id => (cp id).getD 0) (Y := w.Y)
        (by walk_omega) (outChannelIds s.world) 0 s.heap.size (.int 0) chanAt (ListWords.of_nursery nurs) rfl
        (fun i hi => by simpa using placed i hi) (by simp only [Nat.zero_add]; walk_omega) i o hio
      simpa using this
    · intro i o hio l b old hl hp hg
      have hi := (List.getElem?_eq_some_iff.1 hio).1
      rw [len] at hi
      have ow := listObjs_wosize (outChannelIds s.world) s.heap.size (.int 0) i o hio
      have sep := (g.nursery.toWindowSeparated.heap l b old hp hg).1
      simp only [Gc.nurseryFree, ← ent.young, ← ent.limit] at sep
      rw [ow]; omega
    · intro i j o o' ne hi hj
      have hi' := (List.getElem?_eq_some_iff.1 hi).1
      have hj' := (List.getElem?_eq_some_iff.1 hj).1
      rw [len] at hi' hj'
      rw [listObjs_wosize (outChannelIds s.world) s.heap.size (.int 0) i o hi, listObjs_wosize (outChannelIds s.world) s.heap.size (.int 0) j o' hj]
      omega
  exact { h0 with heap := hr }

theorem listVal_eq (ids : List Nat) : ∀ (size : Nat) (acc : Val),
    listVal size acc ids = if ids = [] then acc else .ptr (size + 2 * ids.length - 1) 0 := by
  induction ids with
  | nil => intro _ _; rfl
  | cons id ids ih =>
    intro size acc
    simp only [listVal, ih, List.length_cons, reduceCtorEq, ↓reduceIte]
    by_cases e : ids = []
    · subst e; simp
    · simp only [e, ↓reduceIte, Val.ptr.injEq, and_true]; omega

/-- The list's word is `res`. -/
theorem listVal_word {pl : Place} {size Y : Nat} {ids : List Nat} (yFit : Y < 2 ^ 64)
    (placed : ∀ i, i < 2 * ids.length → pl.φ (size + i) = some (Y - 24 * i - 16)) (room : 48 * ids.length ≤ Y) :
    valWord pl (listVal size (.int 0) ids) = some (resWord Y ids.length) := by
  rw [listVal_eq]
  by_cases e : ids = []
  · subst e; simp only [↓reduceIte, valWord, resWord, List.length_nil]; rfl
  · have pos : 0 < ids.length := (by cases ids with | nil => exact absurd rfl e | cons _ _ => simp)
    simp only [e, ↓reduceIte, valWord, resWord, Nat.ne_of_gt pos, Nat.mul_zero, Nat.add_zero]
    rw [show size + 2 * ids.length - 1 = size + (2 * ids.length - 1) by omega, placed _ (by omega), Option.map_some]
    congr 2; omega

/-- **The loop registers at the return.** -/
theorem out_list_loop {w : Walk} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {ra s0 : BitVec 64} {c f : Config} (loop : LoopRegisters c) (ret : OutListReturned w Ready state k ra s0 c f) :
    LoopRegisters f :=
  ⟨(ret.saved 22 (by decide)).trans loop.dispatchTable, (ret.saved 24 (by decide)).trans loop.opcodeBound,
    (ret.saved 20 (by decide)).trans loop.pending, (ret.saved 19 (by decide)).trans loop.domain, ret.idle,
    ⟨fun n lo hi => ret.gprs.present n lo (by omega) (loop.gprs.get n lo hi)⟩, ret.gprs.gp.trans loop.gp⟩

/-- The list head's word is not written. -/
theorem head_not_outW {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state) (g : WalkGeometry w n) {i : Nat} (hi : i < 8) :
    ¬ outW w state (Layout.sym_caml_all_opened_channels + i) := by
  have spl := g.spLow; have nl := g.nurseryLow; have dl := g.domainLow
  rintro (o | ⟨r, hr, lo, _⟩ | hs | foot)
  · apply o
    simp only [synLog, OutL, and_true]
    refine ⟨Or.inl (by walk_omega), Or.inl (by walk_omega), Or.inl (by walk_omega), Or.inl (by walk_omega),
      Or.inl (by walk_omega)⟩
  · have := (g.records r hr).low; walk_omega
  · obtain ⟨c', ap, _, _⟩ := g.stateApart _ hs
    have := state_misses_head ap; omega
  · rcases foot with gl | ⟨lo, _, _⟩
    · simp only [VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange, Layout.sym_caml_all_opened_channels] at gl
      omega
    · walk_omega

/-- The listing's refcount bumps keep the world's representation: `ChanAt`
does not read `refs`. -/
theorem worldRepr_listRefs {c : Config} {cp : ChanPlace} {w : World} (h : WorldRepr c cp w) :
    WorldRepr c cp (listRefs w) := by
  refine ⟨h.output, fun id ch hc => ?_, h.ooId⟩
  cases e : w.chans[id]? with
  | none => simp only [listRefs, List.getElem?_map, e, Option.map_none] at hc; cases hc
  | some ch0 =>
    simp only [listRefs, List.getElem?_map, e, Option.map_some, Option.some.injEq] at hc
    subst hc
    obtain ⟨a, hp, at_⟩ := h.chans id ch0 e
    exact ⟨a, hp, by split <;> exact at_⟩

theorem _root_.OCaml.Vm.Primitives.VmPayload.listRefs {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (h : VmPayload P s c pl cp sp high) : VmPayload P {s with world := listRefs s.world} c pl cp sp high :=
  ⟨h.stackHigh, h.trapsp, h.codeBase, h.code, h.globals, h.stack, h.heap, worldRepr_listRefs h.world,
    h.atomBase, h.argv⟩

theorem listRefs_ids (w : World) (id : Nat) : ((listRefs w).chans[id]?).isSome = (w.chans[id]?).isSome := by
  simp only [listRefs, List.getElem?_map, Option.isSome_map]

/-- The state after `caml_ml_out_channels_list`: the list, its blocks, and
one more refcount on each listed channel. -/
def listPost (s : St) : St := { listState s with world := listRefs s.world }

theorem primF1Impl_outList (s : St) :
    primF1Impl "caml_ml_out_channels_list" [s.accu] s.heap s.world =
      .ok (listVal s.heap.size (.int 0) (outChannelIds s.world))
        (allocAll s.heap (listObjs s.heap.size (.int 0) (outChannelIds s.world))) (listRefs s.world) := by
  simp only [primF1Impl, outChannelsList_alloc]

/-- **The represented return** of `caml_ml_out_channels_list`, and the loop
geometry of its post-state. -/
theorem out_list_post {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env : BitVec 64} {c f : Config} {Ready : Nat → Config → Prop}
    {state : Config → Nat → Prop} {w : Walk} {k cap : Nat} {s0 : BitVec 64}
    (rt : OutListRuntime L Ready state) (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (ent : OutListEntry Ready state ra P s pl cp sp c w k cap s0) (ret : OutListReturned w Ready state k ra s0 c f)
    (placed : ∀ i, i < 2 * (outChannelIds s.world).length → pl.φ (s.heap.size + i) = some (w.Y - 24 * i - 16))
    (fits : s.heap.words + 6 * (outChannelIds s.world).length ≤ L.budget.heapWords)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    FramedPrimitivePostOn L.runtimeOk P s pl cp sp high "caml_ml_out_channels_list" [s.accu]
        (listVal s.heap.size (.int 0) (outChannelIds s.world)) (resWord w.Y (outChannelIds s.world).length)
        (allocAll s.heap (listObjs s.heap.size (.int 0) (outChannelIds s.world))) (listRefs s.world)
        (outW w state) c ra f ∧
      OCaml.LoopGeometry L P (listPost s) f pl cp high := by
  have input := setup.input
  have g := setup.geometry
  have wg := ent.geometry
  have rm := wg.room; have nh := wg.nurseryHigh; have nl := wg.nurseryLow
  have stk := input.data.stack.1
  have sg := g.statics
  have sb : Layout.stackBytes = 32768 := rfl
  obtain ⟨_, pts⟩ := outW_payload g ent stk (by omega) (by omega)
  have frame := outW_frame wg ret
  have nEq : (listedRecs c.σ.mem w.chs).length = (outChannelIds s.world).length := by
    rw [ent.listed, List.length_map]
  have chanAt : ∀ id ∈ outChannelIds s.world, cp id = some ((cp id).getD 0) ∧ (cp id).getD 0 < 2 ^ 64 := by
    intro id hid
    have lt : id < s.world.chans.length := by
      unfold outChannelIds at hid
      simp only [List.mem_reverse, List.mem_filter, List.mem_range] at hid; exact hid.1
    obtain ⟨a, ha, _⟩ := input.data.world.chans id _ (List.getElem?_eq_getElem lt)
    have mem : a ∈ w.chs := by rw [ent.chs]; exact Gc.mem_placedChannels.2 ⟨id, lt, ha⟩
    have := (wg.records a mem).high
    rw [ha]; exact ⟨rfl, by simp only [Option.getD_some]; walk_omega⟩
  have outputEq : output f.σ = output c.σ := by unfold output; rw [ret.output]
  have payload := out_list_payload g ent input.data stk (by omega) (by omega) ret placed chanAt outputEq
  have hw := fun a (h : VmPoint P s c pl cp sp a) => pts a h
  -- words the geometry reads
  have wDom : word f Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    Misses.word (fun i hi => hw _ (Or.inl ⟨by omega, by omega⟩)) frame
  have wPrims : word f (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) :=
    Misses.word (fun i hi => hw _ (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Layout.sym_caml_prim_table + Layout.off_prim_contents, by simp, by omega, by omega⟩))))) frame
  have wHead : word f Layout.sym_caml_all_opened_channels = word c Layout.sym_caml_all_opened_channels :=
    Misses.word (fun i hi => head_not_outW rt.custom wg hi) frame
  have wLinks : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
      word f (a + Gc.chanOffNext) = word c (a + Gc.chanOffNext) := fun id ch a hc hp =>
    Misses.word (fun i hi => hw _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨id, ch, a, hc, hp, by simp only [Gc.chanOffNext]; omega,
        by simp only [Gc.chanOffNext, chanOffBuff, OCaml.Bytecode.ioBufferSize]; omega,
        by simp only [Gc.chanOffNext]; omega⟩))))))))) frame
  have dN : (BitVec.ofNat 64 w.D).toNat = w.D := toNat_ofNat_small (by have := wg.domainHigh; walk_omega)
  obtain ⟨fy, fl⟩ := fields_of_words (c := f) (by have := wg.domainHigh; walk_omega) (by walk_omega) (by walk_omega)
    ret.domain ret.young ret.limit
  rw [nEq] at fy
  have young : (runtimeFields f).youngPtr = (runtimeFields c).youngPtr -
      8 * blockWords (listObjs s.heap.size (.int 0) (outChannelIds s.world)) := by
    rw [fy, blockWords_listObjs, ← ent.young]; omega
  have limit : (runtimeFields f).youngLimit = (runtimeFields c).youngLimit := by rw [fl, ent.limit]
  have geo := g.reserveN (os := listObjs s.heap.size (.int 0) (outChannelIds s.world))
    (by rw [blockWords_listObjs]; exact fits)
    (listObjs_placed pl _ s.heap (.int 0) _ fun i hi => by rw [← ent.young]; exact placed i hi)
    wDom wPrims limit young wHead wLinks
  refine ⟨{
    call := {
      good := ret.good, image := ret.image, minstret := ret.minstret, tick := ret.tick, pc := ret.pc
      result := by rw [ret.result, nEq]
      memory := frame
      saved := by
        intro r hr
        simp only [callSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ret.saved 25 (by decide)
        · exact (ret.s0.trans ent.input.s0.symm : gprGet f.σ 8 = gprGet c.σ 8)
        · exact ret.saved 18 (by decide)
        · exact (ret.stack.trans ent.input.stack.symm : gprGet f.σ 2 = gprGet c.σ 2) }
    data := payload.listRefs
    primitives := bindings_frame_on input.primitives hw frame
    platform := ⟨ret.good, ret.image, rt.runtime P s c f pl cp high w.H0 input.runtime g
      (fun a ha => frame a fun o => ha (outW_writes ent o))
      (by rw [young]; have := g.nursery.nurseryLow; rw [blockWords_listObjs, ← ent.young]; omega)
      (by rw [young]; omega) (by rw [young, blockWords_listObjs, ← ent.young]; have := wg.youngAligned; omega)⟩
    loop := out_list_loop input.loop ret
    resultRepr := listVal_word (by walk_omega) placed (by omega)
    semantics := primF1Impl_outList s
    gprs := ret.gprs }, ?_⟩
  exact geo.transport_ids (s' := listPost s) (fun l o h => ⟨o, h, rfl⟩) (listRefs_ids s.world) rfl rfl rfl rfl rfl
    (fun _ _ _ _ _ => rfl) rfl

/-- A domain field outside the nursery words, `local_roots` and
`extra_heap_resources_minor` is not written. -/
theorem domainField_not_outW {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state) (g : WalkGeometry w n) {off i : Nat} (hi : i < 8)
    (fits : off + 8 ≤ Layout.domainStateBytes) (young : 16 ≤ off) (roots : off + 8 ≤ 288 ∨ 296 ≤ off)
    (extra : off + 8 ≤ Layout.off_extra_heap_resources_minor ∨ Layout.off_extra_heap_resources_minor + 8 ≤ off) :
    ¬ outW w state (w.D + off + i) := by
  have spl := g.spLow; have nl := g.nurseryLow; have dl := g.domainLow; have dh := g.domainHigh
  have dap := g.domainApart; have rm := g.room; have nh := g.nurseryHigh
  rintro (o | ⟨r, hr, lo, hi'⟩ | hs | foot)
  · apply o
    simp only [synLog, OutL, and_true]
    refine ⟨Or.inl (by walk_omega), ?_, Or.inr (by omega), Or.inr (by omega), ?_⟩
    · rcases dap with d | d
      · exact Or.inl (by walk_omega)
      · exact Or.inr (by walk_omega)
    · rcases roots with r | r
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · have := (g.records r hr).domain; walk_omega
  · obtain ⟨c', ap, _, dom⟩ := g.stateApart _ hs
    have df := ap.domainField
    simp only [VsaIris.InExt, Gc.domainAddr, dom, Nat.add_zero] at df
    have := df ⟨by omega, by omega⟩
    simp only [Layout.off_extra_heap_resources_minor] at this extra; omega
  · obtain ⟨x, xIn, xl, xh⟩ := g.coverDomain
    exact not_vsaFoot_in xIn (by walk_omega) ⟨by omega, by walk_omega⟩ foot

/-- Everything written lies below the caller's native stack pointer. -/
theorem outW_below {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state) (g : WalkGeometry w n) {a : Nat} (h : outW w state a) :
    a < w.sp.toNat + 128 := by
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh
  rcases h with o | ⟨r, hr, lo, hi⟩ | hs | foot
  · simp only [synLog, OutL, and_true] at o
    refine Classical.byContradiction fun ge => o ⟨Or.inr (by walk_omega), Or.inr (by walk_omega), Or.inr (by walk_omega), Or.inr (by walk_omega),
      Or.inr (by walk_omega)⟩
  · have := (g.records r hr).high; walk_omega
  · obtain ⟨c', ap, _, _⟩ := g.stateApart _ hs
    have := ap.belowStack; walk_omega
  · have := vsaFoot_low foot; walk_omega

/-- The runtime's side of `caml_ml_out_channels_list` for some readiness
and custom-allocation state (named obligation; F1: lanes a6-gc and a0-boot). -/
def OutListRuntimeL (L : OCaml.Layout) : Prop :=
  ∃ (Ready : Nat → Config → Prop) (state : Config → Nat → Prop), OutListRuntime L Ready state


end OCaml.Vm.Sim.OutListWalk

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel.OutList
open LeanRV64DExecutable OutListWalk

/-- **`caml_ml_out_channels_list` at every C_CALL site**, given the runtime's
side (`OutListRuntime`; F1: lane a6-gc's `CustomMemCall` with a0-boot's
newlib heap). -/
theorem prim_caml_ml_out_channels_list_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (outList : OutListRuntimeL L) :
    PrimReturnsAt L P op ra k "caml_ml_out_channels_list" := by
  obtain ⟨Ready, state, rt⟩ := outList
  intro s c0 pl cp sp high table entry value env index v heap world _reach ready sem words
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  rw [primF1Impl_outList] at sem
  cases sem
  have hentry : entry = Layout.sym_caml_ml_out_channels_list :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_ml_out_channels_list)
  subst hentry
  have fits : s.heap.words + 6 * (outChannelIds s.world).length ≤ L.budget.heapWords := by
    rw [words_allocAll, blockWords_listObjs] at words; exact words
  refine ⟨(valWord pl (listVal s.heap.size (.int 0) (outChannelIds s.world))).getD 0,
    ⟨by decide, primF1Impl_outList s, fun c setup placedAt => ?_⟩⟩
  obtain ⟨w, kk, cap, s0, ent⟩ := out_list_entry rt setup rfl fits
  have wg := ent.geometry
  have rm := wg.room
  have yFit : w.Y < 2 ^ 64 := by have := wg.nurseryHigh; walk_omega
  have placed : ∀ i, i < 2 * (outChannelIds s.world).length →
      pl.φ (s.heap.size + i) = some (w.Y - 24 * i - 16) := by
    intro i hi
    have mem : (s.heap.size + i, (BitVec.ofNat 64 (runtimeFields c).youngPtr - BitVec.ofNat 64 (24 * i + 16)).toNat) ∈
        allocPlaces "caml_ml_out_channels_list" s (BitVec.ofNat 64 (runtimeFields c).youngPtr) := by
      show _ ∈ outListPlaces s _
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    rw [placedAt _ mem, ← ent.young]
    congr 1
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have vw := listVal_word yFit placed (by omega)
  rw [vw, Option.getD_some]
  have input := setup.input
  have g := setup.geometry
  have stk := input.data.stack.1
  have sg := g.statics
  have stackFits := ready.stackFits
  have sb : Layout.stackBytes = 32768 := rfl
  obtain ⟨_, pts⟩ := outW_payload g ent stk (by omega) (by omega)
  have dWord : BitVec.ofNat 64 (word c Layout.sym_Caml_state).toNat = word c Layout.sym_Caml_state :=
    BitVec.eq_of_toNat_eq (toNat_ofNat_small (BitVec.isLt _))
  have dom : (BitVec.ofNat 64 (domainAt c0)).toNat = w.D := by
    rw [setup.saved.domainWord, ent.domain]
  have dh := wg.domainHigh
  have S : FnSummary (BitVec.ofNat 64 Layout.sym_caml_ml_out_channels_list) (fun x => x = c) (fun after =>
      FramedPrimitivePostOn L.runtimeOk P s pl cp sp high "caml_ml_out_channels_list" [s.accu]
        (listVal s.heap.size (.int 0) (outChannelIds s.world)) (resWord w.Y (outChannelIds s.world).length)
        (allocAll s.heap (listObjs s.heap.size (.int 0) (outChannelIds s.world))) (listRefs s.world)
        (outW w state) c ra after ∧
      OCaml.LoopGeometry L P (listPost s) after pl cp high) := by
    constructor
    intro c' ⟨_, e⟩
    subst e
    obtain ⟨f, run, ret⟩ := out_list_machine rt.custom wg customMemGrows ent.input (by rw [ent.listed, List.length_map]; exact Nat.le_refl _)
      fun a h => (ent.stateS a).mpr h
    exact ⟨f, run, out_list_post rt setup ent ret placed fits stackFits⟩
  have outside : CcallSavedMisses (outW w state) (BitVec.ofNat 64 (domainAt c0)) (BitVec.ofNat 64 (sp - 16)) := by
    refine ⟨fun i hi => pts _ (Or.inl ⟨by omega, by omega⟩), ?_, ?_, ?_⟩
    · intro i hi
      have e : (BitVec.ofNat 64 (domainAt c0) + BitVec.ofNat 64 Layout.off_extern_sp).toNat =
          w.D + Layout.off_extern_sp := by
        rw [BitVec.toNat_add, dom, BitVec.toNat_ofNat]; simp only [Layout.off_extern_sp]; walk_omega
      rw [e]
      exact domainField_not_outW rt.custom wg hi (by decide) (by decide) (by decide) (by decide)
    · intro i hi
      have e : (BitVec.ofNat 64 (sp - 16)).toNat = sp - 16 := toNat_ofNat_small (by have := g.arena; walk_omega)
      rw [e]
      exact pts _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    · intro i hi
      rw [dom]
      exact domainField_not_outW rt.custom wg hi (by decide) (by decide) (by decide) (by decide)
  have below : ∀ n, gpr c 2 = some (BitVec.ofNat 64 n) → ∀ x, outW w state x → x < n := by
    intro n hn x hx
    have bl := outW_below rt.custom wg hx
    have st := ent.input.stack
    rw [hn, Option.some.injEq] at st
    have e := congrArg BitVec.toNat st
    have sp128 : w.sp.toNat + 128 < 2 ^ 64 := by have := wg.spHigh; walk_omega
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := Nat.mod_le n (2 ^ 64)
    omega
  exact ccall_observed_summary_on S setup.saved outside below setup.native

end OCaml.Vm.Sim
