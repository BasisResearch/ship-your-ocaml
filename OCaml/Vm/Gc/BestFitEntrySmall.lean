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

/-- Every checked small-success dispatch preserves the bounded refinement. -/
theorem EntrySmallReturned.boundedBitmap {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (input : EntrySmallInput R lists before) (bounded : BfShape.BoundedBitmap before.σ.mem) :
    BfShape.BoundedBitmap after.σ.mem := by
  cases post.path with
  | exactSize exact =>
    have run : BestFitExact.Post (R 1) (BitVec.ofNat 64 (R 10).toNat) before after := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using exact.execution
    exact run.boundedBitmap bounded input.requestPositive input.request_small
  | nextSize empty next =>
    exact (next.boundedSmallRepresentation (input.next_input empty) bounded).bounded

theorem EntrySmallReturned.boundedSmallRepresentation {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (input : EntrySmallInput R lists before) (bounded : BfShape.BoundedBitmap before.σ.mem) :
    BfShape.BoundedSmallRepresentation after.σ.mem family :=
  ⟨post.representation,post.boundedBitmap input bounded⟩

/-- The selected actual log supplies the shared owned-block frame. -/
theorem EntrySmallReturned.live {R lists s b bs family a writes before after H}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x → OutL writes x) :
    LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x high owned
  rw [post.memory,writeLog_out _ _ _ (outside x high owned)]

/-- Reflected footprint of a selected small source and the free-list frame.
It includes both cursor cells, the real bitmap, and modular free accounting. -/
def smallFreeWindows (sp : BitVec 64) (s : Nat) (b : BitVec 64) : List W :=
  [⟨sp.toNat,sp.toNat+32⟩,
   ⟨Layout.sym_bf_small_map,Layout.sym_bf_small_map+4⟩,
   ⟨Layout.sym_caml_fl_cur_wsz,Layout.sym_caml_fl_cur_wsz+8⟩,
   ⟨Layout.sym_bf_small_fl+16,Layout.sym_bf_small_fl+16*17⟩,
   ⟨b.toNat-8,b.toNat+8*s⟩]

theorem small_prefix_inside {sp s b} (positive : 1 ≤ s) (small : s ≤ 16) :
    ∀ a n, InsideW (prefixWindows (BitVec.ofNat 64 s)) a n →
      InsideW (smallFreeWindows sp s b) a n := by
  have size : (BitVec.ofNat 64 s).toNat ≤ 16 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; exact small
  have slot := BestFitRemnant.slot_nat size
  have merge := BestFitRemnant.merge_nat size
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : s < 2^64)] at slot merge
  intro a n inside
  simp only [prefixWindows,slotS,InsideW,slot,merge] at inside
  simp only [smallFreeWindows,InsideW]
  rcases inside with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)))
  · exact Or.inr (Or.inl h)
  · exact h.elim

theorem small_remnant_inside {sp s b w m} (positive : 1 ≤ s) (small : s ≤ 16)
    (remaining : w.toNat ≤ 16) (nonzero : 1 ≤ w.toNat) :
    LogInW (smallFreeWindows sp s b) (BestFitRemnant.insertLog b w m) := by
  apply logInW_transport (BestFitRemnant.insertLog_inside b w m)
  intro a n inside
  have slot := BestFitRemnant.slot_nat remaining
  have merge := BestFitRemnant.merge_nat remaining
  simp only [BestFitRemnant.writeWindows,InsideW,slot,merge] at inside
  simp only [smallFreeWindows,InsideW]
  rcases inside with h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)))
  · exact Or.inr (Or.inl h)
  · exact h.elim

/-- A finite log certificate; no native instruction is reproved. -/
theorem small_route_inside {sp s b request m} (positive : 1 ≤ s) (small : s ≤ 16)
    (geo : SplitGeometry sp b)
    (remaining : (BestFitRemnant.size b (splitMemory sp b request
      (poppedMemory sp (BitVec.ofNat 64 s) b m))).toNat ≤ 16) :
    LogInW (smallFreeWindows sp s b) (routeLog sp (BitVec.ofNat 64 s) b request m) := by
  unfold routeLog completeLog
  simp only [List.append_assoc]
  apply logInW_join (logInW_transport (pick_inside _ _) (small_prefix_inside positive small))
  apply logInW_join (logInW_transport (pop_inside _ _ _ _) (small_prefix_inside positive small))
  apply logInW_join
  · change LogInW (smallFreeWindows sp s b) [(_,8,_),(_,8,_),(_,8,_)]
    simp only [LogInW,InsideW,smallFreeWindows,geo.header_nat]
    exact ⟨Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)))) ,
      Or.inl ⟨by omega,by omega⟩,True.intro⟩
  · unfold BestFitRemnant.effect
    split
    · rename_i inserts
      have nonzero : 1 ≤ (BestFitRemnant.size b (splitMemory sp b request
          (poppedMemory sp (BitVec.ofNat 64 s) b m))).toNat := by
        have := inserts.1
        have zero : (BestFitRemnant.size b (splitMemory sp b request
          (poppedMemory sp (BitVec.ofNat 64 s) b m))).toNat ≠ 0 := by
          intro eq; apply this; exact BitVec.eq_of_toNat_eq eq
        omega
      exact small_remnant_inside positive small remaining nonzero
    · trivial

/-- Selected class bounds are recovered from the retained native branch. -/
theorem EntrySmallReturned.class_bounds {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (input : EntrySmallInput R lists before) : (R 10).toNat ≤ s ∧ s ≤ 16 := by
  cases post.path with
  | exactSize exact => exact ⟨Nat.le_refl _,input.request_small⟩
  | nextSize empty next =>
    obtain ⟨middle,path⟩ := next.path_spec
    obtain ⟨searched,search⟩ := path.search.path_spec
    exact ⟨Nat.le_of_lt search.choice.larger,search.choice.small⟩

theorem EntryNextReturned.split_size {R lists s b bs before after}
    (post : EntryNextReturned R lists s b bs before after) (input : EntryNextInput R lists before) :
    (BestFitRemnant.size b (searchSplitMemory R s b before)).toNat = s-(R 10).toNat-1 := by
  obtain ⟨middle,path⟩ := post.path_spec
  obtain ⟨searched,search⟩ := path.search.path_spec
  have route := (input.search_input path.probe).route_input search.choice search.search
  have size := search.allocation.remnant_size_nat route
  have snapshot : searched.σ.mem = searchMemory R before := by
    rw [search.search.memory]
    simp only [searchMemory,bitmap,path.probe.memory]
  simpa only [searchSplitMemory,snapshot,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := search.choice.small; omega : s < 2^64)] using size

theorem EntrySmallReturned.log_inside {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (input : EntrySmallInput R lists before) : LogInW (smallFreeWindows (frameSp R) s b) writes := by
  have bounds := post.class_bounds input
  have positive : 1 ≤ s := by have := input.requestPositive; omega
  cases post.path with
  | exactSize exact =>
    rw [BestFitExact.effect_parts]
    have slot := BestFitRemnant.slot_nat input.request_small
    have merge := BestFitRemnant.merge_nat input.request_small
    change (BestFitSmall.slot (R 10)).toNat = _ at slot
    change (BestFitSmall.slot (R 10)+8#64).toNat = _ at merge
    have slotIn : InsideW (smallFreeWindows (frameSp R) (R 10).toNat b)
        (BestFitSmall.slot (R 10)).toNat 8 := by
      simp only [smallFreeWindows,InsideW,slot]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by have := input.requestPositive; omega,by omega⟩)))
    have mergeIn : InsideW (smallFreeWindows (frameSp R) (R 10).toNat b)
        (BestFitSmall.slot (R 10)+8#64).toNat 8 := by
      simp only [smallFreeWindows,InsideW,merge]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by have := input.requestPositive; omega,by omega⟩)))
    have bitmapIn : InsideW (smallFreeWindows (frameSp R) (R 10).toNat b)
        Layout.sym_bf_small_map 4 := Or.inr (Or.inl ⟨Nat.le_refl _,Nat.le_refl _⟩)
    have counterIn : InsideW (smallFreeWindows (frameSp R) (R 10).toNat b)
        Layout.sym_caml_fl_cur_wsz 8 := Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _,Nat.le_refl _⟩))
    by_cases empty : BestFitSmall.next (R 10) before = 0
    all_goals by_cases repair : BestFitSmall.cursor (R 10) before = BestFitSmall.first (R 10) before
    all_goals simp only [BestFitEmpty.effect,BestFitEmpty.route,repair,empty,decide_true,decide_false,
      ite_true,ite_false,Bool.false_eq_true,BestFitSmall.repairLog,BestFitFinish.effect,
      List.cons_append,List.nil_append,LogInW,Layout.off_bf_small_merge]
    · exact ⟨mergeIn,slotIn,bitmapIn,counterIn,True.intro⟩
    · exact ⟨slotIn,bitmapIn,counterIn,True.intro⟩
    · exact ⟨mergeIn,slotIn,counterIn,True.intro⟩
    · exact ⟨slotIn,counterIn,True.intro⟩
  | nextSize empty next =>
    apply logInW_join
    · apply logInW_transport (input.toStackConditions.search_inside _)
      intro x n inside
      exact Or.inl (by simpa only [searchWindows,InsideW,or_false] using inside)
    · apply small_route_inside positive bounds.2
        (input.sources s positive bounds.2 b (by rw [post.selected]; simp)).geometry
      have size := next.split_size (input.next_input empty)
      change (BestFitRemnant.size b (searchSplitMemory R s b before)).toNat ≤ 16
      omega

/-- Actual selected header interval, including the zero-size remnant case. -/
theorem EntrySmallReturned.result_interval {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (input : EntrySmallInput R lists before) :
    b.toNat-8 ≤ a.toNat ∧ a.toNat+8*((R 10).toNat+1) = b.toNat+8*s := by
  have bounds := post.class_bounds input
  have positive : 1 ≤ s := by have := input.requestPositive; omega
  have member : b ∈ lists s := by rw [post.selected]; simp
  have physical := input.representation.physical.bounds s positive bounds.2 b member
  have hn := input.representation.physical.header_nat positive bounds.2 member
  cases post.path with
  | exactSize exact => rw [hn]; omega
  | nextSize empty next =>
    obtain ⟨middle,path⟩ := next.path_spec
    obtain ⟨searched,search⟩ := path.search.path_spec
    have larger := search.choice.larger
    have size := post.originalSize
    have smallSize : (sourceSize (sourceHeader b before.σ.mem)).toNat = s := by
      rw [size]; simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : s < 2^64)]
    rw [resultHeader_nat input.requestPositive (by omega) (by omega)
      (by simp only [DlHeap.heapStart] at physical; omega) (by omega)]
    omega

/-- Natural refund uses the real remnant insertion decision. Sweep deferral
is retained; no relationship between list geometry and counter credit is inferred. -/
def smallRefund (R : Nat → BitVec 64) (s : Nat) (b : BitVec 64) (before : Config) : Nat :=
  if s = (R 10).toNat then 0 else
    if BestFitRemnant.Inserts b (searchSplitMemory R s b before) then s-(R 10).toNat else 0

theorem EntrySmallReturned.counter_nat {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after)
    (input : EntrySmallInput R lists before)
    (credit : s+1 ≤ (word before Layout.sym_caml_fl_cur_wsz).toNat) :
    (word after Layout.sym_caml_fl_cur_wsz).toNat =
      (word before Layout.sym_caml_fl_cur_wsz).toNat-(s+1)+smallRefund R s b before := by
  have bounds := post.class_bounds input
  have initialBound := (word before Layout.sym_caml_fl_cur_wsz).isLt
  cases post.path with
  | exactSize exact =>
    have count := exact.execution.counter_nat credit
    simp only [smallRefund,ite_true]
    change (word after Layout.sym_caml_fl_cur_wsz).toNat+(R 10).toNat+1 = _ at count
    simp only [BestFitSmall.total] at count
    omega
  | nextSize empty next =>
    obtain ⟨middle,path⟩ := next.path_spec
    obtain ⟨searched,search⟩ := path.search.path_spec
    have larger := search.choice.larger
    have size := next.split_size (input.next_input empty)
    have sizeNat : (sourceSize (sourceHeader b before.σ.mem)).toNat = s := by
      rw [post.originalSize]
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : s < 2^64)]
    have removed : (removedCount (word before Layout.sym_caml_fl_cur_wsz)
        (sourceHeader b before.σ.mem)).toNat = (word before Layout.sym_caml_fl_cur_wsz).toNat-(s+1) := by
      have debit : (sourceSize (sourceHeader b before.σ.mem)+1#64).toNat = s+1 := by
        simp only [BitVec.toNat_add,sizeNat,BitVec.toNat_ofNat]
        omega
      unfold removedCount
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,debit]; exact credit),debit]
    change (word after Layout.sym_caml_fl_cur_wsz).toNat = _
    rw [show word after Layout.sym_caml_fl_cur_wsz = _ from next.counter]
    unfold smallRefund
    rw [if_neg (by omega : s ≠ (R 10).toNat)]
    by_cases inserts : BestFitRemnant.Inserts b (searchSplitMemory R s b before)
    · simp only [inserts,ite_true]
      change ((removedCount (word before Layout.sym_caml_fl_cur_wsz) (sourceHeader b before.σ.mem)+1#64+
        BestFitRemnant.size b (searchSplitMemory R s b before))).toNat = _
      simp only [BitVec.toNat_add,removed,BitVec.toNat_ofNat,size]
      omega
    · simp only [inserts,ite_false]
      exact removed

/-- All-register frame recovered from the retained native stage summaries. -/
theorem EntrySmallReturned.frame {R lists s b bs family a writes before after}
    (post : EntrySmallReturned R lists s b bs family a writes before after) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [1,2,10,11,12,13,14,15] ++ [16,17], (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r := by
  intro r noise outside
  have cover (xs : List Nat) (subset : ∀ n ∈ xs, n ∈ [1,2,10,11,12,13,14,15,16,17]) :
      ∀ n ∈ xs, (gprReg n == r) = false := fun n hn => outside n (subset n hn)
  cases post.path with
  | exactSize exact => exact exact.execution.native r noise (cover _ (by decide))
  | nextSize empty next =>
    obtain ⟨middle,path⟩ := next.path_spec
    obtain ⟨searched,search⟩ := path.search.path_spec
    obtain ⟨picked,popped,route⟩ := search.allocation.path_spec
    exact (route.complete.frame r noise (cover _ (by decide))).trans
      ((route.pop.frame r noise (cover _ (by decide))).trans
      ((route.pick.frame r noise (cover _ (by decide))).trans
      ((search.search.native r noise (cover _ (by decide))).trans
      (path.probe.machine.frame_subset probe_written r noise (cover _ (by decide))))))

theorem smallRefund_of_memory {R s b} {before after : Config}
    (memory : after.σ.mem = before.σ.mem) : smallRefund R s b after = smallRefund R s b before := by
  simp only [smallRefund,searchSplitMemory,searchMemory,bitmap,memory]
  rfl

end OCaml.Vm.Gc.BestFitFallback
