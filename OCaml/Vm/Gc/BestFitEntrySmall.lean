import OCaml.Vm.Gc.BestFitEntryNext

/-! Original-entry dispatch across the checked exact and next-size small
successes. Caller invariant production and natural free-word credit are separate. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup BestFitNext

/-- One original-entry interface; a suitable represented small list may be
the exact class or a larger class. No intermediate native state is supplied. -/
structure EntrySmallInput (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (c : Config) : Prop extends EntryInput R lists c where
  suitable : ∃ s, (R 10).toNat ≤ s ∧ s ≤ 16 ∧ lists s ≠ []

theorem EntrySmallInput.request_small {R lists c} (input : EntrySmallInput R lists c) :
    (R 10).toNat ≤ Layout.bf_small_count := by
  obtain ⟨s,larger,small,_⟩ := input.suitable
  change (R 10).toNat ≤ 16
  omega

theorem EntrySmallInput.next_input {R lists c} (input : EntrySmallInput R lists c)
    (empty : lists (R 10).toNat = []) : EntryNextInput R lists c := by
  refine { input.toEntryInput with empty := empty, existsLarger := ?_ }
  obtain ⟨s,larger,small,nonempty⟩ := input.suitable
  refine ⟨s,?_,small,nonempty⟩
  have different : s ≠ (R 10).toNat := by intro eq; subst s; exact nonempty empty
  omega

/-- Exact-size native return with original selected header/size, the full
popped representation and separation for the actual returned header. -/
structure EntryExactReturned (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (b : BitVec 64) (bs : List (BitVec 64)) (before after : Config) : Prop where
  execution : BestFitExact.Post (R 1) (R 10) before after
  selected : lists (R 10).toNat = b :: bs
  first : BestFitSmall.first (R 10) before = b
  result : gprGet after.σ 10 = some (b-8#64)
  stack : gprGet after.σ 2 = some (R 2)
  header : sourceHeader b after.σ.mem = sourceHeader b before.σ.mem
  size : sourceSize (sourceHeader b before.σ.mem) = R 10
  native : GprsSame before after [10,11,12,13,14,15]
  representation : BfShape.SmallRepresentation after.σ.mem (BfShape.popped lists (R 10).toNat bs)
  allocated : AllocatedApart (b-8#64).toNat (R 10) (BfShape.popped lists (R 10).toNat bs)

theorem EntryExactReturned.of_post {R lists b bs before after}
    (input : EntryInput R lists before) (small : (R 10).toNat ≤ Layout.bf_small_count)
    (selected : lists (R 10).toNat = b :: bs)
    (post : BestFitExact.Post (R 1) (R 10) before after) :
    EntryExactReturned R lists b bs before after := by
  have first : BestFitSmall.first (R 10) before = b := by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      BestFitExact.selected_first input.representation.shape input.requestPositive small selected
  have canonical : BestFitExact.Post (R 1) (BitVec.ofNat 64 (R 10).toNat) before after := by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using post
  refine ⟨post,selected,first,?_,?_,?_,?_,post.gprs,?_,?_⟩
  · simpa only [first,Layout.header_bytes] using post.result
  · exact post.gprs.get (by decide) (by decide) (by decide) (gholds_lookup _ input.registers rfl)
  · exact canonical.selected_header input.representation.physical input.requestPositive small selected
  · have member : b ∈ lists (R 10).toNat := by rw [selected]; exact List.mem_cons_self ..
    simpa only [sourceSize,sourceHeader,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.representation.headers.sizes _ input.requestPositive small b member
  · exact canonical.smallRepresentation input.representation input.requestPositive small selected
  · simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      canonical.allocated_apart input.representation.physical input.requestPositive small selected

structure EntryExactPost (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (before after : Config) : Prop where
  selected : ∃ b bs, EntryExactReturned R lists b bs before after

theorem EntryExactPost.selected_spec {R lists before after} (post : EntryExactPost R lists before after) :
    ∃ b bs, EntryExactReturned R lists b bs before after := post.selected

/-- All four existing exact-size branches, enriched without reproving their run. -/
theorem allocate_entry_exact {R lists c} (input : EntryInput R lists c)
    (small : (R 10).toNat ≤ Layout.bf_small_count) (nonempty : lists (R 10).toNat ≠ []) :
    FnSummary BestFitSmall.pc (fun d => d = c) (EntryExactPost R lists c) := by
  obtain ⟨b,bs,selected⟩ : ∃ b bs, lists (R 10).toNat = b :: bs := by
    cases h : lists (R 10).toNat with
    | nil => exact (nonempty h).elim
    | cons b bs => exact ⟨b,bs,rfl⟩
  apply (BestFitExact.allocate (input.exact_input small nonempty)).weaken (fun _ h => h)
  intro after post
  exact ⟨b,bs,EntryExactReturned.of_post input small selected post⟩

/-- The branch witness retains its exact effect and native contract. -/
inductive EntrySmallPath (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) :
    Nat → BitVec 64 → List (BitVec 64) → (Nat → List (BitVec 64)) → BitVec 64 →
      List WEntry → Config → Config → Prop
  | exactSize {b bs before after} (post : EntryExactReturned R lists b bs before after) :
      EntrySmallPath R lists (R 10).toNat b bs (BfShape.popped lists (R 10).toNat bs)
        (b-8#64) (BestFitExact.effect (R 10) before) before after
  | nextSize {s b bs before after} (empty : lists (R 10).toNat = [])
      (post : EntryNextReturned R lists s b bs before after) :
      EntrySmallPath R lists s b bs (searchLists R s b lists bs before)
        (resultHeader b (R 10) (sourceHeader b before.σ.mem)) (searchRouteLog R s b before) before after

/-- Uniform native success with the selected returned representation in both
branches. The branch witness exposes its original header and accounting laws. -/
structure EntrySmallReturned (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64)) (family : Nat → List (BitVec 64))
    (a : BitVec 64) (writes : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt (R 1) after
  result : gprGet after.σ 10 = some a
  stack : gprGet after.σ 2 = some (R 2)
  selected : lists s = b :: bs
  originalSize : sourceSize (sourceHeader b before.σ.mem) = BitVec.ofNat 64 s
  memory : after.σ.mem = writeLog before.σ.mem writes
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : GprsSame before after [1,2,10,11,12,13,14,15,16,17]
  representation : BfShape.SmallRepresentation after.σ.mem family
  allocated : AllocatedApart a.toNat (R 10) family
  path : EntrySmallPath R lists s b bs family a writes before after

theorem EntrySmallReturned.of_exact {R lists b bs before after}
    (post : EntryExactReturned R lists b bs before after) :
    EntrySmallReturned R lists (R 10).toNat b bs (BfShape.popped lists (R 10).toNat bs)
      (b-8#64) (BestFitExact.effect (R 10) before) before after := by
  refine ⟨post.execution.good,post.execution.tick,post.execution.minstret,post.execution.pc,
    post.result,post.stack,post.selected,?_,post.execution.memory,post.execution.code,
    post.execution.output,post.native.mono (by decide),post.representation,post.allocated,.exactSize post⟩
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using post.size

theorem EntrySmallReturned.of_next {R lists s b bs before after}
    (input : EntryInput R lists before) (empty : lists (R 10).toNat = [])
    (post : EntryNextReturned R lists s b bs before after) :
    EntrySmallReturned R lists s b bs (searchLists R s b lists bs before)
      (resultHeader b (R 10) (sourceHeader b before.σ.mem)) (searchRouteLog R s b before) before after := by
  obtain ⟨middle,path⟩ := post.path_spec
  obtain ⟨searched,search⟩ := path.search.path_spec
  have positive : 1 ≤ s := by have := search.choice.larger; omega
  have member : b ∈ lists s := by rw [search.choice.selected]; exact List.mem_cons_self ..
  exact ⟨post.good,post.tick,post.minstret,post.pc,post.result,post.stack,search.choice.selected,
    input.representation.headers.sizes s positive search.choice.small b member,
    post.memory,post.code,post.output,post.native,post.representation,post.allocated,.nextSize empty post⟩

structure EntrySmallPost (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (before after : Config) : Prop where
  selected : ∃ s b bs family a writes, EntrySmallReturned R lists s b bs family a writes before after

theorem EntrySmallPost.selected_spec {R lists before after} (post : EntrySmallPost R lists before after) :
    ∃ s b bs family a writes, EntrySmallReturned R lists s b bs family a writes before after := post.selected

/-- Actual original-entry small success: use the exact native run whenever
the represented request class is nonempty, otherwise the checked search route. -/
theorem allocate_entry_small {R lists c} (input : EntrySmallInput R lists c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (EntrySmallPost R lists c) := by
  by_cases empty : lists (R 10).toNat = []
  · apply (allocate_entry_next (input.next_input empty)).weaken (fun _ h => h)
    intro after post
    obtain ⟨s,b,bs,returned⟩ := post.selected_spec
    exact ⟨s,b,bs,_,_,_,EntrySmallReturned.of_next input.toEntryInput empty returned⟩
  · apply (allocate_entry_exact input.toEntryInput input.request_small empty).weaken (fun _ h => h)
    intro after post
    obtain ⟨b,bs,returned⟩ := post.selected_spec
    exact ⟨_,b,bs,_,_,_,EntrySmallReturned.of_exact returned⟩

/-- The selected actual log supplies the shared owned-block frame. -/
theorem EntrySmallReturned.live {R lists s b bs family a writes before after H}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x → OutL writes x) :
    LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x high owned
  rw [post.memory,writeLog_out _ _ _ (outside x high owned)]

end OCaml.Vm.Gc.BestFitFallback
