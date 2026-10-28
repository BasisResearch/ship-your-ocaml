import OCaml.Vm.Gc.BestFitMissing
import OCaml.Vm.Gc.BestFitPreservation

/-! Actual bf_allocate entry, empty exact-size slot and a nonempty larger
small list, through allocation and the original native caller return. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup BestFitNext

/-- Observations only at the original allocator entry. Native callers must
supply the representation, code, register and source/stack window facts. -/
structure EntryInput (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (c : Config) : Prop extends Input R c where
  ffsCode : Code.FfsLoaded c.σ.mem
  remnantCode : Code.Bf_insert_remnant_smallLoaded c.σ.mem
  representation : BfShape.SmallRepresentation c.σ.mem lists
  requestPositive : 1 ≤ (R 10).toNat
  stackHeap : Vsa.Sim.DlHeap.heapStart ≤ (frameSp R).toNat
  sources : ∀ s, 1 ≤ s → s ≤ 16 → ∀ b ∈ lists s, SearchSource (frameSp R) b
  aligned : (R 1).toNat % 4 = 0

/-- The existing search route specializes the shared original-entry interface. -/
structure EntryNextInput (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (c : Config) : Prop extends EntryInput R lists c where
  empty : lists (R 10).toNat = []
  existsLarger : ∃ s, (R 10).toNat < s ∧ s ≤ 16 ∧ lists s ≠ []

/-- Derive the exact-size native input from the original represented list
and the same entry registers used by the next-size probe. -/
theorem EntryInput.exact_input {R lists c} (input : EntryInput R lists c)
    (small : (R 10).toNat ≤ Layout.bf_small_count) (nonempty : lists (R 10).toNat ≠ []) :
    BestFitExact.Input (R 1) (R 10) c := by
  have conditions : BestFitExact.Conditions (R 10) c := by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      BfShape.exact_of_nonempty input.representation.shape rfl input.requestPositive small nonempty
  exact { conditions with
    good := input.good
    tick := input.tick
    minstret := input.minstret
    code := input.code
    registers := ⟨gholds_lookup _ input.registers rfl,gholds_lookup _ input.registers rfl,True.intro⟩
    aligned := input.aligned }

/-- A larger small list bounds the original request's decoded size test. -/
theorem EntryNextInput.request_small {R lists c} (input : EntryNextInput R lists c) :
    (R 10).toNat ≤ Layout.bf_small_count := by
  obtain ⟨s,larger,small,_⟩ := input.existsLarger
  change (R 10).toNat ≤ 16
  omega

/-- The empty represented family supplies the real slot read; neither the
slot observation nor a fallback configuration is an entry premise. -/
theorem EntryInput.missing_input {R lists c} (input : EntryInput R lists c)
    (small : (R 10).toNat ≤ Layout.bf_small_count) (empty : lists (R 10).toNat = []) :
    MissingInput R c := by
  have linked := input.representation.shape.linked (R 10).toNat
    input.requestPositive small
  rw [empty] at linked
  have slot : BfShape.slot (R 10).toNat = BestFitSmall.slot (R 10) := by
    simp only [BfShape.slot,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine { input.toInput with
    small := small
    slotRead := ?_
    empty := ?_ }
  · rw [← slot]
    exact (BfShape.slot_write _ small).read
  · change bytesT c.σ.mem (BestFitSmall.slot (R 10)).toNat 8 = 0#64
    rw [← slot]
    exact linked

/-- The larger-list route uses the same representation-derived slot proof. -/
theorem EntryNextInput.missing_input {R lists c} (input : EntryNextInput R lists c) :
    MissingInput R c :=
  input.toEntryInput.missing_input input.request_small input.empty

/-- Every fallback input observation is derived at the actual returned
configuration of the read-only entry probe. -/
theorem EntryNextInput.search_input {R lists before middle}
    (input : EntryNextInput R lists before) (probe : Missing R before middle) :
    SearchInput R lists middle :=
  { toStackConditions := input.toStackConditions
    good := probe.machine.good
    tick := probe.machine.tick
    minstret := probe.machine.minstret
    code := probe.memory ▸ input.code
    registers := probe.registers
    ffsCode := probe.memory ▸ input.ffsCode
    remnantCode := probe.memory ▸ input.remnantCode
    shape := probe.memory ▸ input.representation.shape
    headers := probe.memory ▸ input.representation.headers
    map := probe.memory ▸ input.representation.map
    requestPositive := input.requestPositive
    existsLarger := input.existsLarger
    stackHeap := input.stackHeap
    sources := input.sources
    aligned := input.aligned }

/-- Both real stages, retaining the actual fallback configuration and the
search/allocation summary with its own checked internal stage witnesses. -/
structure EntryNextPath (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64))
    (before after middle : Config) : Prop where
  probe : Missing R before middle
  search : SearchReturned R lists s b bs middle after

/-- All observations refer back to the original bf_allocate entry, including
the final selected family and separation of the actual allocated extent. -/
structure EntryNextReturned (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64)) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt (R 1) after
  result : gprGet after.σ 10 = some (resultHeader b (R 10) (sourceHeader b before.σ.mem))
  stack : gprGet after.σ 2 = some (R 2)
  header : sourceHeader b after.σ.mem = smallHeader (R 10) (sourceHeader b before.σ.mem)
  remnantSize : (BestFitRemnant.size b after.σ.mem).toNat = s-(R 10).toNat-1
  counter : bytesT after.σ.mem Layout.sym_caml_fl_cur_wsz 8 =
    if BestFitRemnant.Inserts b (searchSplitMemory R s b before) then
      removedCount (bytesT before.σ.mem Layout.sym_caml_fl_cur_wsz 8) (sourceHeader b before.σ.mem) +
        1#64 + BestFitRemnant.size b (searchSplitMemory R s b before)
    else removedCount (bytesT before.σ.mem Layout.sym_caml_fl_cur_wsz 8) (sourceHeader b before.σ.mem)
  memory : after.σ.mem = writeLog before.σ.mem (searchRouteLog R s b before)
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : GprsSame before after [1,2,10,11,12,13,14,15,16,17]
  representation : BfShape.SmallRepresentation after.σ.mem (searchLists R s b lists bs before)
  allocated : AllocatedApart (resultHeader b (R 10) (sourceHeader b before.σ.mem)).toNat
    (R 10) (searchLists R s b lists bs before)
  path : ∃ middle, EntryNextPath R lists s b bs before after middle

theorem EntryNextReturned.path_spec {R lists s b bs before after}
    (post : EntryNextReturned R lists s b bs before after) :
    ∃ middle, EntryNextPath R lists s b bs before after middle := post.path

/-- Bounded snapshot transport preserves the actual selected branch without
normalizing any nested pick/pop/split memories. -/
theorem EntryNextReturned.of_stages {R lists s b bs before middle after}
    (input : EntryNextInput R lists before) (probe : Missing R before middle)
    (post : SearchReturned R lists s b bs middle after) :
    EntryNextReturned R lists s b bs before after := by
  have searchInput := input.search_input probe
  have bits : bitmap middle = bitmap before := by simp only [bitmap,probe.memory]
  have snapshot : searchMemory R middle = searchMemory R before := by
    simp only [searchMemory,probe.memory,bits]
  have cut : searchSplitMemory R s b middle = searchSplitMemory R s b before :=
    congrArg (fun m => splitMemory (frameSp R) b (R 10)
      (poppedMemory (frameSp R) (BitVec.ofNat 64 s) b m)) snapshot
  have log : searchRouteLog R s b middle = searchRouteLog R s b before := by
    simp only [searchRouteLog,bits,snapshot]
  have family : searchLists R s b lists bs middle = searchLists R s b lists bs before :=
    congrArg (routeLists (frameSp R) (BitVec.ofNat 64 s) b (R 10) lists bs) snapshot
  refine ⟨post.good,post.tick,post.minstret,post.pc,?_,post.stack,?_,post.remnantSize,?_,?_,
    post.code,post.output.trans probe.machine.output,?_,?_,?_,⟨middle,probe,post⟩⟩
  · simpa only [probe.memory] using post.result
  · simpa only [probe.memory] using post.header
  · have counter := post.counter
    rw [probe.memory,cut] at counter
    exact counter
  · rw [post.memory,probe.memory,log]
  · exact (probe.native.trans post.native).mono (by decide)
  · rw [← family]
    exact post.smallRepresentation searchInput input.representation.physical
  · rw [← family]
    simpa only [probe.memory] using
      post.allocated_apart searchInput input.representation.physical

structure EntryNextPost (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (before after : Config) : Prop where
  selected : ∃ s b bs, EntryNextReturned R lists s b bs before after

theorem EntryNextPost.selected_spec {R lists before after}
    (post : EntryNextPost R lists before after) :
    ∃ s b bs, EntryNextReturned R lists s b bs before after := post.selected

/-- Complete successful next-size path from actual bf_allocate entry
0x800073ac: classify the empty exact slot, search, allocate and return. -/
theorem allocate_entry_next {R lists c} (input : EntryNextInput R lists c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (EntryNextPost R lists c) := by
  have fallback : FnSummary pc (Missing R c) (EntryNextPost R lists c) := by
    constructor
    rintro middle ⟨atFallback,probe⟩
    obtain ⟨after,run,post⟩ := (search_allocate (input.search_input probe)).run middle ⟨atFallback,rfl⟩
    obtain ⟨s,b,bs,returned⟩ := post.selected_spec
    exact ⟨after,run,⟨s,b,bs,EntryNextReturned.of_stages input probe returned⟩⟩
  exact (missing input.missing_input).seq fallback (fun _ probe => ⟨probe.pc,probe⟩)

/-- Original selected owned blocks use the existing search log frame and
the memory-free probe's LiveFrame, composed by the shared law. -/
theorem EntryNextReturned.live {R lists s b bs before after H}
    (post : EntryNextReturned R lists s b bs before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (searchRouteLog R s b before) x) : LiveFrame H before after := by
  obtain ⟨middle,path⟩ := post.path_spec
  apply (LiveFrame.of_memory path.probe.memory).trans
  apply path.search.live bounds
  intro x high owned
  simpa only [searchRouteLog,searchMemory,bitmap,path.probe.memory] using outside x high owned

end OCaml.Vm.Gc.BestFitFallback
