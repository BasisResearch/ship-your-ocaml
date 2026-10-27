import OCaml.Vm.Gc.BestFitNextRoute
import OCaml.Vm.Gc.BestFitFallbackSaved

/-! The native nonzero bitmap search followed by the complete next-size
allocation. Entry facts describe original data and physical separation. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup BestFitNext

/-- The decoded SLLW mask retains exactly the bits at or above the request. -/
theorem mask_bit {request : BitVec 64} (small : request.toNat < 16)
    {j : Nat} (low : j < 32) :
    (mask request).getLsbD j = decide (request.toNat ≤ j) := by
  have table : ∀ n < 16, ∀ i < 32,
      (mask (BitVec.ofNat 64 n)).getLsbD i = decide (n ≤ i) := by decide
  simpa using table request.toNat small j low

/-- Only low-word bitmap bits are consulted by the native search. -/
theorem filtered_bit {request : BitVec 64} {c : Config} (small : request.toNat < 16)
    {j : Nat} (low : j < 32) :
    (filtered request (bitmap c)).getLsbD j =
      ((BfShape.mapBits c.σ.mem).getLsbD j && decide (request.toNat ≤ j)) := by
  rw [filtered,BitVec.getLsbD_and,mask_bit small low]
  congr 1
  simp only [bitmap,read4_value,BfShape.mapBits,Functions.sign_extend,Sail.BitVec.signExtend,
    BitVec.getLsbD_signExtend]
  simp [low,show j < 64 by omega]

/-- A selected list and the minimality justified by the original bitmap. -/
structure Selection (request : BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64)) : Prop where
  larger : request.toNat < s
  small : s ≤ 16
  selected : lists s = b :: bs
  least : ∀ t, request.toNat < t → t < s → lists t = []

/-- Existence of a larger represented list supplies the least such list. -/
theorem select_list {request : BitVec 64} {lists : Nat → List (BitVec 64)}
    (existsLarger : ∃ s, request.toNat < s ∧ s ≤ 16 ∧ lists s ≠ []) :
    ∃ s b bs, Selection request lists s b bs := by
  classical
  let P := fun s => request.toNat < s ∧ s ≤ 16 ∧ lists s ≠ []
  have least : ∀ n, P n → ∃ s, P s ∧ ∀ t < s, ¬ P t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro pn
      by_cases earlier : ∃ t, t < n ∧ P t
      · obtain ⟨t,lt,pt⟩ := earlier
        exact ih t lt pt
      · exact ⟨n,pn,fun t lt pt => earlier ⟨t,lt,pt⟩⟩
  obtain ⟨n,pn⟩ := existsLarger
  obtain ⟨s,spec,minimal⟩ := least n pn
  obtain ⟨b,bs,selected⟩ : ∃ b bs, lists s = b :: bs := by
    cases h : lists s with
    | nil => exact False.elim (spec.2.2 h)
    | cons b bs => exact ⟨b,bs,rfl⟩
  refine ⟨s,b,bs,spec.1,spec.2.1,selected,?_⟩
  intro t larger smaller
  apply Classical.byContradiction
  intro nonempty
  exact minimal t smaller ⟨larger,by omega,nonempty⟩

/-- Map consistency and least-list selection produce the actual ffs input;
no bit-selection or later machine post is assumed at entry. -/
theorem Selection.lowest {request lists s b bs c}
    (choice : Selection request lists s b bs)
    (map : BfShape.MapConsistent c.σ.mem lists) :
    FfsLowest.Lowest (filtered request (bitmap c)) (s-1) := by
  have small : request.toNat < 16 := by have := choice.larger; have := choice.small; omega
  have positive : 1 ≤ s := by have := choice.larger; omega
  refine ⟨by have := choice.small; omega,?_,?_⟩
  · rw [filtered_bit small (by have := choice.small; omega)]
    have bit := (map s positive choice.small).mpr (by rw [choice.selected]; simp)
    simp only [bit,Bool.true_and,decide_eq_true_eq]
    have := choice.larger; omega
  · intro j below
    rw [filtered_bit small (by have := choice.small; omega)]
    by_cases kept : request.toNat ≤ j
    · have empty := choice.least (j+1) (by omega) (by omega)
      have bit : (BfShape.mapBits c.σ.mem).getLsbD j = false := by
        have h := map (j+1) (by omega) (by change j+1 ≤ 16; have := choice.small; omega)
        simp only [Nat.add_sub_cancel,empty,ne_eq,not_true_eq_false,iff_false] at h
        exact Bool.eq_false_iff.mpr h
      simp [bit]
    · simp [kept]

/-- The original native frame is the only footprint of search and ffs. -/
def searchWindows (R : Nat → BitVec 64) : List W :=
  [⟨(frameSp R).toNat,(frameSp R).toNat+32⟩]

theorem StackConditions.search_inside {R} (conditions : StackConditions R) (bits : BitVec 64) :
    LogInW (searchWindows R) (effect R bits) := by
  have bound := stack_bound (frameSp R) 24 (by decide) (conditions.windows (1,24) (by decide))
  have a8 := stack_address (frameSp R) 8 24 bound (by decide)
  have a24 := stack_address (frameSp R) 24 24 bound (by decide)
  simp only [effect,BitVec.add_zero,searchWindows,LogInW,InsideW,a8,a24]
  exact ⟨Or.inl ⟨by omega,by omega⟩,Or.inl ⟨by omega,by omega⟩,
    Or.inl ⟨by omega,by omega⟩,True.intro⟩

theorem Found.read {R k before after a n} (post : Found R k before after)
    (conditions : StackConditions R) (outside : OutWRange (searchWindows R) a n) :
    bytesT after.σ.mem a n = bytesT before.σ.mem a n := by
  rw [post.memory]
  exact bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (conditions.search_inside _) outside)

/-- Every save is read from the actual generated prefix log after ffs. -/
theorem Found.saved {R k before after} (post : Found R k before after)
    (conditions : StackConditions R) (cell : Nat × Nat) (member : cell ∈ saves) :
    bytesT after.σ.mem (frameSp R + BitVec.ofNat 64 cell.2).toNat 8 =
      bankRegs R (bitmap before) cell.1 := by
  rw [post.memory,effect_bank]
  exact saveShape.read before.σ.mem (frameSp R) (bankRegs R (bitmap before)) conditions.windows cell member

/-- Physical source/header windows from the original ownership geometry. -/
structure SearchSource (sp b : BitVec 64) : Prop where
  header : WriteWindow (b-8#64) 8
  remnant : WriteWindow b 8
  geometry : SplitGeometry sp b

/-- Original data at the real fallback entry. Existence selects the size;
source ownership separates all represented links/headers from the native frame. -/
structure SearchInput (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (c : Config) : Prop extends Input R c where
  ffsCode : Code.FfsLoaded c.σ.mem
  remnantCode : Code.Bf_insert_remnant_smallLoaded c.σ.mem
  shape : BfShape.SmallShape c.σ.mem lists
  headers : BfShape.SmallHeaders c.σ.mem lists
  map : BfShape.MapConsistent c.σ.mem lists
  requestPositive : 1 ≤ (R 10).toNat
  existsLarger : ∃ s, (R 10).toNat < s ∧ s ≤ 16 ∧ lists s ≠ []
  stackHeap : Vsa.Sim.DlHeap.heapStart ≤ (frameSp R).toNat
  sources : ∀ s, 1 ≤ s → s ≤ 16 → ∀ b ∈ lists s, SearchSource (frameSp R) b
  aligned : (R 1).toNat % 4 = 0

theorem SearchInput.static_out {R lists c a n} (input : SearchInput R lists c)
    (high : a+n ≤ Vsa.Sim.DlHeap.heapStart) : OutWRange (searchWindows R) a n :=
  ⟨Or.inl (Nat.le_trans high input.stackHeap),True.intro⟩

theorem SearchSource.header_out {R b} (source : SearchSource (frameSp R) b) :
    OutWRange (searchWindows R) (b-8#64).toNat 8 := by
  rw [source.geometry.header_nat]
  have sep := source.geometry.separate
  have heap := source.geometry.blockHeap
  change ((b.toNat-8)+8 ≤ (frameSp R).toNat ∨ (frameSp R).toNat+32 ≤ b.toNat-8) ∧ True
  exact ⟨by omega,True.intro⟩

theorem SearchSource.link_out {R b} (source : SearchSource (frameSp R) b) :
    OutWRange (searchWindows R) b.toNat 8 := by
  have sep := source.geometry.separate
  change (b.toNat+8 ≤ (frameSp R).toNat ∨ (frameSp R).toNat+32 ≤ b.toNat) ∧ True
  exact ⟨by omega,True.intro⟩

/-- Shape, all header sizes and bitmap consistency survive the real search
prefix; ffs itself has no memory effect. -/
theorem SearchInput.represented {R lists c s b bs after}
    (input : SearchInput R lists c) (_choice : Selection (R 10) lists s b bs)
    (post : Found R (s-1) c after) :
    BfShape.SmallShape after.σ.mem lists ∧ BfShape.SmallHeaders after.σ.mem lists ∧
      BfShape.MapConsistent after.σ.mem lists := by
  have read : ∀ {a n}, OutWRange (searchWindows R) a n →
      bytesT after.σ.mem a n = bytesT c.σ.mem a n := post.read input.toStackConditions
  have bits : BfShape.mapBits after.σ.mem = BfShape.mapBits c.σ.mem :=
    read (input.static_out (by decide))
  refine ⟨input.shape.congr ?_ ?_,⟨?_⟩,?_⟩
  · intro t lo hi
    apply read
    apply input.static_out
    rw [BfShape.slot_toNat t hi]
    simp only [Layout.bf_small_count] at hi
    simp only [Layout.sym_bf_small_fl,Vsa.Sim.DlHeap.heapStart]
    omega
  · intro t lo hi x hx
    exact read (input.sources t lo hi x hx).link_out
  · intro t lo hi x hx
    rw [read (input.sources t lo hi x hx).header_out]
    exact input.headers.sizes t lo hi x hx
  · intro t lo hi
    change (BfShape.mapBits after.σ.mem).getLsbD _ = true ↔ _
    rw [bits]
    exact input.map t lo hi

/-- Produce the complete allocator-route input from the actual search post. -/
theorem SearchInput.route_input {R lists c s b bs after}
    (input : SearchInput R lists c) (choice : Selection (R 10) lists s b bs)
    (post : Found R (s-1) c after) :
    RouteInput (frameSp R) (BitVec.ofNat 64 s) b (R 10) lists bs after := by
  have positive : 1 ≤ s := by have := choice.larger; omega
  have sn : (BitVec.ofNat 64 s).toNat = s := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := choice.small; omega)]
  have represented := input.represented choice post
  have request := post.saved input.toStackConditions (14,8) (by decide)
  have bitmap := post.saved input.toStackConditions (12,0) (by decide)
  have link := post.saved input.toStackConditions (1,24) (by decide)
  change bytesT after.σ.mem (frameSp R+8#64).toNat 8 = R 10 at request
  change bytesT after.σ.mem (frameSp R+0#64).toNat 8 = BestFitFallback.bitmap c at bitmap
  rw [BitVec.add_zero] at bitmap
  change bytesT after.σ.mem (frameSp R+24#64).toNat 8 = R 1 at link
  have bits : BfShape.mapBits after.σ.mem = BfShape.mapBits c.σ.mem :=
    post.read input.toStackConditions (input.static_out (by decide))
  have source := input.sources s positive choice.small b (by rw [choice.selected]; simp)
  refine ⟨post.good,post.tick,post.minstret,post.code,?_,?_,represented.1,represented.2.1,
    represented.2.2,?_,?_,input.requestPositive,?_,request,?_,source.header,source.remnant,
    ?_,?_,?_,source.geometry,?_⟩
  · apply Code.bf_insert_remnant_small_transport input.remnantCode
    intro a lo hi
    rw [post.memory]
    exact writeLog_out _ _ _ (outL_of_range
      (OCaml.Vm.Sim.outLRange_of_windows (input.toStackConditions.search_inside _)
        (input.static_out (a := a) (n := 1) (by
          simp only [Vsa.Sim.DlHeap.heapStart]; omega))) (by omega) (by omega))
  · exact ⟨post.stack,by simpa only [Nat.sub_add_cancel positive] using post.result,True.intro⟩
  · rw [sn]; exact choice.selected
  · rw [sn]; exact choice.small
  · rw [sn]; exact choice.larger
  · rw [bitmap,bits]
    simp only [BestFitFallback.bitmap,read4_value,BfShape.mapBits]
    simp only [Functions.sign_extend,Sail.BitVec.signExtend]
    apply BitVec.eq_of_getLsbD_eq
    intro j hi
    rw [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
    simp only [hi,show j < 64 by omega,decide_true,Bool.true_and,ite_true]
  · simpa only [saves,BitVec.add_zero] using input.windows (12,0) (by decide)
  · exact (input.windows (14,8) (by decide)).read
  · exact (input.windows (1,24) (by decide)).read
  · rw [link]; exact input.aligned

/-- The memory snapshot produced by the three real fallback stores. -/
def searchMemory (R : Nat → BitVec 64) (c : Config) :=
  writeLog c.σ.mem (effect R (bitmap c))

/-- Exact search, cursor/pop, split and branch-dependent remnant logs. -/
def searchRouteLog (R : Nat → BitVec 64) (s : Nat) (b : BitVec 64) (c : Config) :=
  effect R (bitmap c) ++ routeLog (frameSp R) (BitVec.ofNat 64 s) b (R 10) (searchMemory R c)

/-- The concrete branch test is evaluated on the original-data snapshots. -/
def searchSplitMemory (R : Nat → BitVec 64) (s : Nat) (b : BitVec 64) (c : Config) :=
  splitMemory (frameSp R) b (R 10)
    (poppedMemory (frameSp R) (BitVec.ofNat 64 s) b (searchMemory R c))

structure SearchPath (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64))
    (before after searched : Config) : Prop where
  choice : Selection (R 10) lists s b bs
  search : Found R (s-1) before searched
  allocation : RoutePost (frameSp R) (BitVec.ofNat 64 s) b (R 10) lists bs searched after

/-- A selected allocation returned to the original caller, with original
header/counter observations and the exact log of every selected branch. -/
structure SearchReturned (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
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
  path : ∃ searched, SearchPath R lists s b bs before after searched

theorem SearchReturned.path_spec {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after) :
    ∃ searched, SearchPath R lists s b bs before after searched := post.path

/-- The size/head/tail are witnesses produced by original-data selection. -/
structure SearchPost (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (before after : Config) : Prop where
  selected : ∃ s b bs, SearchReturned R lists s b bs before after

theorem SearchPost.selected_spec {R lists before after} (post : SearchPost R lists before after) :
    ∃ s b bs, SearchReturned R lists s b bs before after := post.selected

/-- Actual fallback entry through ffs, least larger small-list allocation,
and native return. The initial memory and ownership geometry supply all
later inputs, including the saved request, bitmap and original caller link. -/
theorem search_allocate {R lists c} (input : SearchInput R lists c) :
    FnSummary pc (fun d => d = c) (SearchPost R lists c) := by
  obtain ⟨s,b,bs,choice⟩ := select_list input.existsLarger
  constructor
  apply Vsa.Logic.Triple.seq (search_nonzero input.toInput input.ffsCode (choice.lowest input.map)).run
  intro searched found
  have routeInput := input.route_input choice found
  obtain ⟨after,run,last⟩ := (allocate_next routeInput).run searched ⟨found.pc,rfl⟩
  have snapshot : searched.σ.mem = searchMemory R c := found.memory
  have positive : 1 ≤ s := by have := choice.larger; omega
  have source := input.sources s positive choice.small b (by rw [choice.selected]; simp)
  have header : sourceHeader b searched.σ.mem = sourceHeader b c.σ.mem :=
    found.read input.toStackConditions source.header_out
  have count : bytesT searched.σ.mem Layout.sym_caml_fl_cur_wsz 8 =
      bytesT c.σ.mem Layout.sym_caml_fl_cur_wsz 8 :=
    found.read input.toStackConditions (input.static_out (by decide))
  have link := found.saved input.toStackConditions (1,24) (by decide)
  change bytesT searched.σ.mem (frameSp R+24#64).toNat 8 = R 1 at link
  refine ⟨after,run,⟨s,b,bs,last.good,last.tick,last.minstret,?_,?_,?_,?_,?_,?_,?_,last.code,
    last.output.trans found.output,?_,⟨searched,choice,found,last⟩⟩⟩
  · simpa only [link] using last.pc
  · simpa only [header] using last.result
  · simpa only [frameSp,frameSize,BitVec.sub_add_cancel] using last.stack
  · exact last.header.trans (congrArg (smallHeader (R 10)) header)
  · simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := choice.small; omega : s < 2^64)]
      using last.remnantSize
  · have counter := last.counter
    rw [header,count] at counter
    have cut : splitMemory (frameSp R) b (R 10)
        (poppedMemory (frameSp R) (BitVec.ofNat 64 s) b searched.σ.mem) =
        searchSplitMemory R s b c :=
      congrArg (fun m => splitMemory (frameSp R) b (R 10)
        (poppedMemory (frameSp R) (BitVec.ofNat 64 s) b m)) snapshot
    rw [cut] at counter
    exact counter
  · rw [last.memory,snapshot,searchRouteLog,writeLog_append]
    rfl
  · exact ((route_gprs (by decide) found.native).trans last.native).mono (by decide)

/-- Selected original owned blocks remain live under separation from the
combined actual log, including the original native save frame. -/
theorem SearchReturned.live {R lists s b bs before after H}
    (post : SearchReturned R lists s b bs before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (searchRouteLog R s b before) x) : LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x high owned
  rw [post.memory,writeLog_out _ _ _ (outside x high owned)]

end OCaml.Vm.Gc.BestFitFallback
