import OCaml.Vm.Gc.BestFitEntryLarge
import OCaml.Vm.Gc.BestFitSplitGeometry
import OCaml.Vm.Gc.BestFitLargeFootprint

/-! Original-entry least-large split. All source observations are in the
original memory. No arbitrary searched or returned snapshot is an input. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup

/-- Original least-block geometry, its nonwrapping extent and native frame.
This supplies neither allocator ownership nor an upper arena bound.
This does not assert or preserve an arbitrary large-tree topology. -/
structure EntryLargeSource (sp request : BitVec 64) (lists : Nat → List (BitVec 64))
    (c : Config) : Prop where
  headerWrite : WriteWindow (BestFitSplit.headerAddr (BestFitLarge.least c)) 8
  heap : DlHeap.heapStart+8 ≤ (BestFitLarge.least c).toNat
  fits : (BestFitLarge.least c).toNat+8*(BestFitSplit.sizeWord (BestFitLarge.header c)).toNat < 2^64
  large : request.toNat+17 < (BestFitSplit.sizeWord (BestFitLarge.header c)).toNat
  stack : (BestFitLarge.least c).toNat+8*(BestFitSplit.sizeWord (BestFitLarge.header c)).toNat ≤ sp.toNat ∨
    sp.toNat+32 ≤ (BestFitLarge.least c).toNat-8
  apart : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ x ∈ lists s,
    (BestFitLarge.least c).toNat+8*(BestFitSplit.sizeWord (BestFitLarge.header c)).toNat ≤ x.toNat-8 ∨
      x.toNat+8*s ≤ (BestFitLarge.least c).toNat-8

structure EntryLargeInput (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (c : Config) : Prop extends EntryInput R lists c where
  bounded : BfShape.BoundedBitmap c.σ.mem
  small : (R 10).toNat ≤ Layout.bf_small_count
  noSuitable : ∀ s, (R 10).toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []
  splitCode : Code.Bf_splitLoaded c.σ.mem
  source : EntryLargeSource (frameSp R) (R 10) lists c

theorem EntryLargeSource.header_nat {sp request lists c}
    (source : EntryLargeSource sp request lists c) :
    (BestFitSplit.headerAddr (BestFitLarge.least c)).toNat = (BestFitLarge.least c).toNat-8 := by
  have bound := (BestFitLarge.least c).isLt
  have heap := source.heap
  simp only [BestFitSplit.headerAddr,Layout.header_bytes,BitVec.toNat_sub,BitVec.toNat_ofNat,DlHeap.heapStart] at *
  omega

theorem EntryLargeInput.searched_read {R lists c a n} (input : EntryLargeInput R lists c)
    (outside : OutWRange (searchWindows R) a n) :
    bytesT (searched R c).σ.mem a n = bytesT c.σ.mem a n :=
  bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows
    (input.toStackConditions.search_inside _) outside)

theorem EntryLargeInput.searched_least {R lists c} (input : EntryLargeInput R lists c) :
    BestFitLarge.least (searched R c) = BestFitLarge.least c := by
  apply input.searched_read
  have heap := input.stackHeap
  refine ⟨Or.inl ?_,True.intro⟩
  change Layout.sym_bf_large_least+8 ≤ (frameSp R).toNat
  simp only [Layout.sym_bf_large_least,DlHeap.heapStart] at *
  omega

theorem EntryLargeInput.searched_header {R lists c} (input : EntryLargeInput R lists c) :
    BestFitLarge.header (searched R c) = BestFitLarge.header c := by
  unfold BestFitLarge.header
  rw [input.searched_least]
  apply input.searched_read
  change ((_+8 ≤ (frameSp R).toNat ∨ (frameSp R).toNat+32 ≤ _) ∧ True)
  rw [show (BestFitLarge.least c - BitVec.ofNat 64 Layout.header_bytes).toNat =
    (BestFitLarge.least c).toNat-8 from input.source.header_nat]
  have sep := input.source.stack
  have heap := input.source.heap
  exact ⟨by omega,True.intro⟩

/-- The original source and real native save-bank supply the searched conditions. -/
theorem EntryLargeInput.large_conditions {R lists c} (input : EntryLargeInput R lists c) :
    LargeConditions R c := by
  have size := input.toInput.searched_size
  have least := input.searched_least
  have header := input.searched_header
  have bound := stack_bound (frameSp R) 24 (by decide) (input.windows (1,24) (by decide))
  have a0 := stack_address (frameSp R) 0 24 bound (by decide)
  have a8 := stack_address (frameSp R) 8 24 bound (by decide)
  refine ⟨⟨⟨input.windows (12,0) (by decide),input.windows (14,8) (by decide)⟩,?_,?_,?_,?_⟩,?_⟩
  · simpa only [least,BestFitSplit.headerAddr] using input.source.headerWrite
  · rw [least]
    intro zero
    have heap := input.source.heap
    rw [zero] at heap
    simp [DlHeap.heapStart] at heap
  · rw [size]; exact input.small
  · rw [size,header]; exact input.source.large
  · simp only [BestFitLarge.effect,OutLRange,BestFitLarge.sizeOffset,BestFitLarge.bitmapOffset,a0,a8,least]
    rw [show (BestFitLarge.least c - BitVec.ofNat 64 Layout.header_bytes).toNat =
      (BestFitLarge.least c).toNat-8 from input.source.header_nat]
    have sep := input.source.stack
    have large := input.source.large
    exact ⟨by omega,by omega,True.intro⟩

/-- Actual pre-split and split stores miss the original caller's saved link. -/
theorem EntryLargeInput.return_outside {R lists c} (input : EntryLargeInput R lists c) :
    ReturnOutside R c := by
  have bound := stack_bound (frameSp R) 24 (by decide) (input.windows (1,24) (by decide))
  have a0 := stack_address (frameSp R) 0 24 bound (by decide)
  have a8 := stack_address (frameSp R) 8 24 bound (by decide)
  have a24 := stack_address (frameSp R) 24 24 bound (by decide)
  simp only [ReturnOutside,BestFitLarge.splitEffect,BestFitLarge.effect,BestFitSplit.effect,
    OutLRange,List.cons_append,List.nil_append,BestFitLarge.sizeOffset,BestFitLarge.bitmapOffset,
    BestFitLargeReturn.returnOffset,a0,a8,a24,input.searched_least]
  rw [input.source.header_nat]
  have sep := input.source.stack
  have heap := input.stackHeap
  have large := input.source.large
  refine ⟨by omega,by omega,Or.inr ?_,by omega,True.intro⟩
  simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at *
  omega

/-- The repaired invariant derives the zero branch at the original entry. -/
theorem EntryLargeInput.filtered_zero {R lists c} (input : EntryLargeInput R lists c) :
    filtered (R 10) (bitmap c) = 0#64 :=
  filtered_of_noSuitable ⟨input.representation,input.bounded⟩ input.requestPositive input.small input.noSuitable

/-- The complete native log has only the saved bank, counter, and original
source-header windows. Values are retained in `completeEffect`. -/
def entryLargeWindows (R : Nat → BitVec 64) (c : Config) : List W :=
  [⟨(frameSp R).toNat,(frameSp R).toNat+32⟩,
   ⟨Layout.sym_caml_fl_cur_wsz,Layout.sym_caml_fl_cur_wsz+8⟩,
   ⟨(BestFitSplit.headerAddr (BestFitLarge.least c)).toNat,
    (BestFitSplit.headerAddr (BestFitLarge.least c)).toNat+8⟩]

theorem EntryLargeInput.complete_inside {R lists c} (input : EntryLargeInput R lists c) :
    LogInW (entryLargeWindows R c) (completeEffect R c) := by
  have bound := stack_bound (frameSp R) 24 (by decide) (input.windows (1,24) (by decide))
  have a0 := stack_address (frameSp R) 0 24 bound (by decide)
  have a8 := stack_address (frameSp R) 8 24 bound (by decide)
  have a24 := stack_address (frameSp R) 24 24 bound (by decide)
  simp only [completeEffect,largeEffect,BestFitLarge.splitEffect,effect,BestFitLarge.effect,
    BestFitSplit.effect,List.cons_append,List.nil_append,LogInW,InsideW,entryLargeWindows,
    BestFitLarge.sizeOffset,BestFitLarge.bitmapOffset,BitVec.add_zero,a0,a8,a24,input.searched_least]
  exact ⟨Or.inl ⟨by omega,by omega⟩,Or.inl ⟨by omega,by omega⟩,
    Or.inl ⟨by omega,by omega⟩,Or.inl ⟨by omega,by omega⟩,Or.inl ⟨by omega,by omega⟩,
    Or.inr (Or.inl ⟨by omega,by omega⟩),Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)),
    Or.inr (Or.inl ⟨by omega,by omega⟩),True.intro⟩

theorem Allocated.entry_read {R lists before after a n} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) (outside : OutWRange (entryLargeWindows R before) a n) :
    bytesT after.σ.mem a n = bytesT before.σ.mem a n := by
  rw [post.memory]
  exact bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows input.complete_inside outside)

theorem EntryLargeInput.static_out {R lists c a n} (input : EntryLargeInput R lists c)
    (high : a+n ≤ DlHeap.heapStart)
    (counter : a+n ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ a) :
    OutWRange (entryLargeWindows R c) a n := by
  have heap := input.source.heap
  have stack := input.stackHeap
  simp only [entryLargeWindows,OutWRange,input.source.header_nat]
  exact ⟨Or.inl (by omega),counter,Or.inl (by omega),True.intro⟩

/-- An original small block's link/header is outside the actual large log.
Both separations are derived from the selected physical source and saved frame. -/
theorem EntryLargeInput.small_out {R lists c t x} (input : EntryLargeInput R lists c)
    (lo : 1 ≤ t) (hi : t ≤ Layout.bf_small_count) (member : x ∈ lists t) :
    OutWRange (entryLargeWindows R c) (x.toNat-8) 16 := by
  have bounds := input.representation.physical.bounds t lo hi x member
  have sep := input.source.apart t lo hi x member
  have stack := (input.sources t lo hi x member).geometry.separate
  have heap := input.source.heap
  have large := input.source.large
  simp only [entryLargeWindows,OutWRange,input.source.header_nat]
  refine ⟨by omega,Or.inr ?_,by omega,True.intro⟩
  simp only [DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz] at bounds ⊢
  omega

/-- The observed least-pointer cell is static and outside every real store.
No statement about unobserved large-tree topology follows from this fact. -/
theorem Allocated.entry_least {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) : BestFitLarge.least after = BestFitLarge.least before :=
  post.entry_read input (input.static_out (by decide) (by decide))

/-- All lower lists, headers, physical extents and the bounded map survive. -/
theorem Allocated.boundedSmallRepresentation {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) : BfShape.BoundedSmallRepresentation after.σ.mem lists := by
  have frame : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ lists t,
      bytesT after.σ.mem x.toNat 8 = bytesT before.σ.mem x.toNat 8 ∧
      bytesT after.σ.mem (x-8#64).toNat 8 = bytesT before.σ.mem (x-8#64).toNat 8 := by
    intro t lo hi x hx
    have outside := input.small_out lo hi hx
    have bounds := input.representation.physical.bounds t lo hi x hx
    have xn := input.representation.physical.header_nat lo hi hx
    constructor
    · apply post.entry_read input
      simp only [entryLargeWindows,OutWRange,input.source.header_nat] at outside ⊢
      rcases outside with ⟨st,ct,hd,_⟩
      exact ⟨by omega,by omega,by omega,True.intro⟩
    · rw [xn]
      apply post.entry_read input
      simp only [entryLargeWindows,OutWRange,input.source.header_nat] at outside ⊢
      rcases outside with ⟨st,ct,hd,_⟩
      exact ⟨by omega,by omega,by omega,True.intro⟩
  have bits : BfShape.mapBits after.σ.mem = BfShape.mapBits before.σ.mem :=
    post.entry_read input (input.static_out (by decide) (by decide))
  refine ⟨⟨input.representation.shape.congr ?_ (fun t lo hi x hx => (frame t lo hi x hx).1),
    input.representation.headers.congr (fun t lo hi x hx => (frame t lo hi x hx).2),?_,
    input.representation.physical⟩,input.bounded.congr bits⟩
  · intro t lo hi
    apply post.entry_read input
    apply input.static_out
    · rw [BfShape.slot_toNat t hi]
      change t ≤ 16 at hi
      simp only [DlHeap.heapStart,Layout.sym_bf_small_fl]; omega
    · rw [BfShape.slot_toNat t hi]
      exact Or.inr (by simp only [Layout.sym_caml_fl_cur_wsz,Layout.sym_bf_small_fl]; omega)
  · intro t lo hi
    change (BfShape.mapBits after.σ.mem).getLsbD _ = true ↔ _
    rw [bits]
    exact input.representation.map t lo hi

/-- The carved header is computed from the original source size and pointer. -/
theorem EntryLargeInput.largeHeader_nat {R lists c} (input : EntryLargeInput R lists c) :
    (largeHeader R c).toNat = (BestFitLarge.least c).toNat-8 +
      8*((BestFitSplit.sizeWord (BestFitLarge.header c)).toNat-(R 10).toNat) := by
  have fits := input.source.fits
  have heap := input.source.heap
  have large := input.source.large
  have sz : (BestFitSplit.sizeWord (BestFitLarge.header c)).toNat =
      (BestFitLarge.header c).toNat / 1024 := by
    simp only [BestFitSplit.sizeWord,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have delta := BestFitSplit.delta_nat (R 10) (BestFitLarge.header c) (by omega)
  simp only [largeHeader,input.toInput.searched_size,input.searched_header,input.searched_least,
    BitVec.toNat_add,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,input.source.header_nat,delta]
  rw [← sz]
  omega

theorem Allocated.entry_allocated_apart {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) :
    BestFitNext.AllocatedApart (largeHeader R before).toNat (R 10) lists := by
  have fits := input.source.fits
  have heap := input.source.heap
  have large := input.source.large
  rw [input.largeHeader_nat]
  constructor
  · omega
  · intro t lo hi x hx
    have sep := input.source.apart t lo hi x hx
    omega

/-- Readbacks needed to identify the split's original source observations. -/
theorem EntryLargeInput.prepared_header {R lists c} (input : EntryLargeInput R lists c) :
    BestFitSplit.header (BestFitLarge.least (searched R c))
      (BestFitLarge.prepared (frameSp R) (searched R c)) = BestFitLarge.header c := by
  change bytesT (writeLog _ _) _ 8 = _
  unfold BestFitSplit.headerAddr
  rw [bytesT_writeLog_out _ input.large_conditions.headerOutside]
  exact input.searched_header

theorem EntryLargeInput.prepared_counter {R lists c} (input : EntryLargeInput R lists c) :
    word (BestFitLarge.prepared (frameSp R) (searched R c)) Layout.sym_caml_fl_cur_wsz =
      word c Layout.sym_caml_fl_cur_wsz := by
  have heap := input.stackHeap
  have bound := stack_bound (frameSp R) 24 (by decide) (input.windows (1,24) (by decide))
  have a0 := stack_address (frameSp R) 0 24 bound (by decide)
  have a8 := stack_address (frameSp R) 8 24 bound (by decide)
  change bytesT (writeLog _ _) _ 8 = _
  rw [bytesT_writeLog_out _ (show OutLRange (BestFitLarge.effect (frameSp R)
      (BestFitLarge.size (frameSp R) (searched R c)) (BestFitLarge.header (searched R c)))
      Layout.sym_caml_fl_cur_wsz 8 from by
    simp only [BestFitLarge.effect,OutLRange,BestFitLarge.sizeOffset,BestFitLarge.bitmapOffset,a0,a8]
    simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at heap ⊢
    exact ⟨Or.inl (by omega),Or.inl (by omega),True.intro⟩)]
  apply input.searched_read
  exact ⟨Or.inl (by simp only [searchWindows]; simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at heap ⊢; omega),True.intro⟩

/-- Exact original-memory normal form of the existing large split log. -/
theorem EntryLargeInput.largeEffect_eq {R lists c} (input : EntryLargeInput R lists c) :
    largeEffect R c = effect R (bitmap c) ++
      [((frameSp R + 8#64).toNat,8,BestFitSplit.sizeWord (BestFitLarge.header c)),
       ((frameSp R + 0#64).toNat,8,R 10),
       (Layout.sym_caml_fl_cur_wsz,8,word c Layout.sym_caml_fl_cur_wsz - 1#64 - BestFitSplit.sizeWord (BestFitLarge.header c)),
       ((BestFitSplit.headerAddr (BestFitLarge.least c)).toNat,8,
         BestFitSplit.remnantHeader (BestFitSplit.route (R 10) (BestFitLarge.header c))
           (BestFitSplit.delta (R 10) (BestFitLarge.header c)))] := by
  unfold largeEffect BestFitLarge.splitEffect BestFitSplit.effect
  rw [input.prepared_header,input.prepared_counter,input.toInput.searched_size,
    input.searched_header,input.searched_least]
  rfl

/-- The shortened source header is the actual split store, with its exact
size/color expression. This is an extent result, not a large-tree theorem. -/
theorem Allocated.entry_header {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) :
    word after (BestFitSplit.headerAddr (BestFitLarge.least before)).toNat =
      BestFitSplit.remnantHeader (BestFitSplit.route (R 10) (BestFitLarge.header before))
        (BestFitSplit.delta (R 10) (BestFitLarge.header before)) := by
  rw [word,post.memory,completeEffect,input.largeEffect_eq]
  apply word_writeLog_at _ _ 6 _ _ rfl
  have heap := input.source.heap
  simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,OutLRange,
    input.source.header_nat,Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at heap ⊢
  change ((_+8 ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ _) ∧ True)
  exact ⟨Or.inr (by simp only [Layout.sym_caml_fl_cur_wsz]; omega),True.intro⟩

/-- The retained block's payload size is shortened by request plus one header. -/
theorem Allocated.entry_remaining {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) :
    HeaderOk (word after (BestFitSplit.headerAddr (BestFitLarge.least before)).toNat)
      ((BestFitLarge.header before).toNat / 1024 - (R 10).toNat - 1)
      (if BestFitSplit.route (R 10) (BestFitLarge.header before) then 0 else Layout.tag_abstract) := by
  rw [post.entry_header input]
  apply BestFitSplit.remnant_header
  have large := input.source.large
  simpa only [BestFitSplit.sizeWord,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] using
    (show (R 10).toNat < (BestFitSplit.sizeWord (BestFitLarge.header before)).toNat by omega)

/-- The implemented strict source-size test selects the large remnant arm. -/
theorem EntryLargeInput.split_large {R lists c} (input : EntryLargeInput R lists c) :
    BestFitSplit.route (R 10) (BestFitLarge.header c) = true := by
  have large := input.source.large
  have sz : (BestFitSplit.sizeWord (BestFitLarge.header c)).toNat =
      (BestFitLarge.header c).toNat / 1024 := by
    simp only [BestFitSplit.sizeWord,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  unfold BestFitSplit.route
  rw [BestFitSplit.delta_nat _ _ (by omega)]
  simp only [BestFitSplit.limit,Layout.bf_small_count,BitVec.toNat_ofNat,decide_eq_true_eq]
  omega

theorem Allocated.entry_remaining_blue {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) :
    HeaderOk (word after (BestFitSplit.headerAddr (BestFitLarge.least before)).toNat)
      ((BestFitLarge.header before).toNat / 1024-(R 10).toNat-1) 0 := by
  simpa only [input.split_large,ite_true] using post.entry_remaining input

/-- The returned allocation starts immediately after the retained extent. -/
theorem Allocated.entry_remaining_apart {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) :
    (BestFitLarge.least before).toNat +
      8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) =
      (largeHeader R before).toNat := by
  rw [input.largeHeader_nat]
  have heap := input.source.heap
  have large := input.source.large
  omega

/-- Scalar readbacks from the actual pre-return split snapshot. -/
structure EntrySplitReadbacks (R : Nat → BitVec 64) (c : Config) : Prop where
  size : BestFitLargeReturn.savedSize (frameSp R) (splitSnapshot R c) = BestFitSplit.sizeWord (BestFitLarge.header c)
  request : BestFitLargeReturn.savedRequest (frameSp R) (splitSnapshot R c) = R 10
  counter : word (splitSnapshot R c) Layout.sym_caml_fl_cur_wsz =
    word c Layout.sym_caml_fl_cur_wsz - 1#64 - BestFitSplit.sizeWord (BestFitLarge.header c)

theorem EntryLargeInput.split_readbacks {R lists c} (input : EntryLargeInput R lists c) :
    EntrySplitReadbacks R c := by
  have heap := input.stackHeap
  have source := input.source.heap
  have sep := input.source.stack
  have large := input.source.large
  have bound := stack_bound (frameSp R) 24 (by decide) (input.windows (1,24) (by decide))
  have a0 := stack_address (frameSp R) 0 24 bound (by decide)
  have a8 : (frameSp R + 8#64).toNat = (frameSp R).toNat+8 :=
    stack_address (frameSp R) 8 24 bound (by decide)
  constructor
  · change bytesT (writeLog _ _) _ 8 = _
    rw [input.largeEffect_eq]
    apply word_writeLog_at _ _ 3 _ _ rfl
    simp only [effect,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,OutLRange,
      BitVec.add_zero,a0,a8,BestFitLargeReturn.sizeOffset,input.source.header_nat]
    refine ⟨Or.inr (by omega),Or.inr ?_,by omega,True.intro⟩
    simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at heap ⊢
    omega
  · change bytesT (writeLog _ _) _ 8 = _
    rw [input.largeEffect_eq]
    apply word_writeLog_at _ _ 4 _ _ rfl
    simp only [effect,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,OutLRange,
      BitVec.add_zero,a0,BestFitLargeReturn.requestOffset,input.source.header_nat]
    refine ⟨Or.inr ?_,by omega,True.intro⟩
    simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at heap ⊢
    omega
  · change bytesT (writeLog _ _) _ 8 = _
    rw [input.largeEffect_eq]
    apply word_writeLog_at _ _ 5 _ _ rfl
    simp only [effect,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,OutLRange,
      input.source.header_nat]
    refine ⟨Or.inl ?_,True.intro⟩
    simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at source ⊢
    omega

/-- Final modular accounting cancels the temporary whole-source debit. -/
theorem Allocated.entry_counter {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) :
    word after Layout.sym_caml_fl_cur_wsz = word before Layout.sym_caml_fl_cur_wsz - 1#64 - R 10 := by
  rw [post.counter,BestFitLargeReturn.counted,input.split_readbacks.size,
    input.split_readbacks.request,input.split_readbacks.counter]
  rw [BitVec.add_comm,BitVec.sub_add_cancel]

/-- Natural subtraction requires explicit credit in the original native
counter; the represented extents alone do not provide that credit. -/
theorem Allocated.entry_counter_nat {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before)
    (credit : (R 10).toNat+1 ≤ (word before Layout.sym_caml_fl_cur_wsz).toNat) :
    (word after Layout.sym_caml_fl_cur_wsz).toNat =
      (word before Layout.sym_caml_fl_cur_wsz).toNat - ((R 10).toNat+1) := by
  rw [post.entry_counter input]
  have count := (word before Layout.sym_caml_fl_cur_wsz).isLt
  have request := (R 10).isLt
  simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

/-- Saved native registers are carried by the shared register-frame abstraction. -/
theorem Allocated.gprsSame {R before after} (post : Allocated R before after) :
    GprsSame before after [1,2,10,11,12,13,14,15] :=
  GprsSame.of_regFrame (by decide) (fun r outside noise => post.native r noise
    (fun n hn => Bool.eq_false_iff.mpr (fun eq => outside n hn (beq_iff_eq.mp eq))))

/-- Physical facts at the original caller return. The retained source is still
large; its extent ends exactly at the actual allocated header. Tree topology
and allocated-header color are deliberately separate obligations. -/
structure EntryLargeReturned (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (before after : Config) : Prop extends Allocated R before after where
  representation : BfShape.BoundedSmallRepresentation after.σ.mem lists
  least : BestFitLarge.least after = BestFitLarge.least before
  originalResult : gprGet after.σ 10 = some
    ((BestFitSplit.delta (R 10) (BestFitLarge.header before) <<< (3 : Nat)) +
      BestFitSplit.headerAddr (BestFitLarge.least before))
  remaining : HeaderOk (word after (BestFitSplit.headerAddr (BestFitLarge.least before)).toNat)
    ((BestFitLarge.header before).toNat / 1024-(R 10).toNat-1)
    0
  remainingHeap : DlHeap.heapStart+8 ≤ (BestFitLarge.least before).toNat
  remainingApart : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ x ∈ lists s,
    (BestFitLarge.least before).toNat+
      8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) ≤ x.toNat-8 ∨
      x.toNat+8*s ≤ (BestFitLarge.least before).toNat-8
  remainingLarge : 16 < (BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1
  remainingBound : (BestFitLarge.least before).toNat+
    8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) < 2^64
  boundary : (BestFitLarge.least before).toNat+
    8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) =
      (largeHeader R before).toNat
  allocated : BestFitNext.AllocatedApart (largeHeader R before).toNat (R 10) lists
  originalCounter : word after Layout.sym_caml_fl_cur_wsz =
    word before Layout.sym_caml_fl_cur_wsz - 1#64 - R 10
  gprs : GprsSame before after [1,2,10,11,12,13,14,15]

theorem EntryLargeReturned.of_allocated {R lists before after} (post : Allocated R before after)
    (input : EntryLargeInput R lists before) : EntryLargeReturned R lists before after := by
  have fits := input.source.fits
  have large := input.source.large
  refine ⟨post,post.boundedSmallRepresentation input,post.entry_least input,?_,post.entry_remaining_blue input,input.source.heap,?_,by omega,by omega,
    post.entry_remaining_apart input,post.entry_allocated_apart input,post.entry_counter input,post.gprsSame⟩
  · simpa only [largeHeader,input.toInput.searched_size,input.searched_header,input.searched_least] using post.result
  · intro t lo hi x hx
    have sep := input.source.apart t lo hi x hx
    omega

/-- Reuse the complete existing run and return all original-entry physical
facts. No arbitrary intermediate/final states or zero observations are premises. -/
theorem allocate_entry_large {R lists c} (input : EntryLargeInput R lists c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (EntryLargeReturned R lists c) :=
  (allocate_large (input.toEntryInput.missing_of_noSuitable input.small input.noSuitable)
    input.ffsCode input.splitCode input.filtered_zero input.large_conditions input.return_outside input.aligned).weaken
      (fun _ h => h) (fun _ post => EntryLargeReturned.of_allocated post input)

/-- A selected caller-owned ledger is framed from the exact native log under
explicit physical separation, using the shared ownership abstraction. -/
theorem EntryLargeReturned.live {R lists before after H} (post : EntryLargeReturned R lists before after)
    (bounds : ∀ e ∈ H, DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ DlHeap.heapEnd)
    (outside : ∀ x, x < DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (completeEffect R before) x) : LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x high owned
  rw [post.memory,writeLog_out _ _ _ (outside x high owned)]

end OCaml.Vm.Gc.BestFitFallback
