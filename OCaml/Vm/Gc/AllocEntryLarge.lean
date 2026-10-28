import OCaml.Vm.Gc.BestFitEntryLargeReturn
import OCaml.Vm.Gc.AllocLargeWrapper
import OCaml.Vm.Gc.AllocOriginal
import OCaml.Vm.Sim.PayloadWindows

/-! Bounded least-large allocation from the real wrapper's original caller.
The selected physical source is not an ownership assertion. Its explicit upper
arena bound supplies the carved header's RAM window. Global allocator readiness,
large-tree topology, expansion and collection remain separate obligations. -/
namespace OCaml.Vm.Gc.AllocEntryLarge
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup

def freeRegs (R : Nat → BitVec 64) := AllocLarge.freeRegs (AllocEntry.frameSp R) (R 10)
theorem freeRegs_request (R : Nat → BitVec 64) : freeRegs R 10 = R 10 := rfl

def nativeSp (R : Nat → BitVec 64) := BestFitFallback.frameSp (freeRegs R)
def sourceEnd (c : Config) := (BestFitLarge.least c).toNat +
  8*(BestFitSplit.sizeWord (BestFitLarge.header c)).toNat
def header (R : Nat → BitVec 64) (c : Config) :=
  (BestFitSplit.delta (R 10) (BestFitLarge.header c) <<< (3 : Nat)) +
    BestFitSplit.headerAddr (BestFitLarge.least c)
def threshold (c : Config) := word c Layout.sym_Caml_state + BitVec.ofNat 64 Layout.off_minor_heap_wsz

/-- The only mutable physical regions before accounting's counter store.
The full source window includes both the retained and carved headers. -/
def windows (R : Nat → BitVec 64) (c : Config) : List W :=
  [⟨(nativeSp R).toNat,(AllocEntry.frameSp R).toNat+48⟩,
   ⟨Layout.sym_caml_fl_cur_wsz,Layout.sym_caml_fl_cur_wsz+8⟩,
   ⟨(BestFitLarge.least c).toNat-8,sourceEnd c⟩]

def fullWindows (R : Nat → BitVec 64) (c : Config) : List W :=
  ⟨Layout.sym_caml_allocated_words,Layout.sym_caml_allocated_words+8⟩ :: windows R c

/-- Facts about original wrapper inputs and physical data only. The credit
bounds are independent of representation. `sourceUpper` is an arena bound,
not selected-ledger ownership. No execution or later snapshot is a premise. -/
structure Facts (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) (c : Config) : Prop where
  representation : BfShape.BoundedSmallRepresentation c.σ.mem lists
  positive : 1 ≤ (R 10).toNat
  requestSmall : (R 10).toNat ≤ Layout.bf_small_count
  noSuitable : ∀ s, (R 10).toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []
  fallbackWindows : BestFitFallback.StackConditions (freeRegs R)
  stackHeap : DlHeap.heapStart ≤ (nativeSp R).toNat
  source : BestFitFallback.EntryLargeSource (nativeSp R) (R 10) lists c
  sourceUpper : sourceEnd c ≤ DlHeap.heapEnd
  sourceNative : sourceEnd c ≤ (nativeSp R).toNat ∨
    (AllocEntry.frameSp R).toNat+48 ≤ (BestFitLarge.least c).toNat-8
  smallNative : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ x ∈ lists s,
    x.toNat+8*s ≤ (nativeSp R).toNat ∨ (AllocEntry.frameSp R).toNat+48 ≤ x.toNat-8
  smallSources : ∀ s, 1 ≤ s → s ≤ 16 → ∀ x ∈ lists s,
    BestFitFallback.SearchSource (nativeSp R) x
  thresholdRead : ReadWindow (threshold c) 8
  thresholdApart : OutWRange (windows R c) (threshold c).toNat 8
  noMajorSlice : (word c Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat ≤
    (word c (threshold c).toNat).toNat
  allocatedCredit : (word c Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat < 2^64
  freeCredit : (R 10).toNat+1 ≤ (word c Layout.sym_caml_fl_cur_wsz).toNat
  tagBound : (R 11).toNat < 256
  aligned : (R 1).toNat % 4 = 0

/-- Original caller of `caml_alloc_shr_for_minor_gc`, before its prologue. -/
structure Input (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) (c : Config) : Prop
    extends AllocEntry.Input R BestFitSmall.pc c, Facts R lists c where
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  ffsCode : Code.FfsLoaded c.σ.mem
  splitCode : Code.Bf_splitLoaded c.σ.mem
  remnantCode : Code.Bf_insert_remnant_smallLoaded c.σ.mem

/-- The two native frames meet exactly; neither subtraction wraps. -/
theorem Input.native_bounds {R lists c} (input : Input R lists c) :
    (nativeSp R).toNat+32 = (AllocEntry.frameSp R).toNat ∧
    (AllocEntry.frameSp R).toNat+48 ≤ 0x100000000 :=
  AllocOriginal.native_bounds input.windows

theorem Input.prologue_inside {R lists c} (input : Input R lists c) :
    LogInW [⟨(AllocEntry.frameSp R).toNat,(AllocEntry.frameSp R).toNat+48⟩] (AllocEntry.effect R) :=
  AllocOriginal.prologue_inside input.windows

theorem Input.prologue_read {R lists c a n} (input : Input R lists c)
    (outside : a+n ≤ (AllocEntry.frameSp R).toNat ∨ (AllocEntry.frameSp R).toNat+48 ≤ a) :
    bytesT (AllocWrapperCore.prepared R c).σ.mem a n = bytesT c.σ.mem a n :=
  AllocOriginal.prologue_read input.windows outside

theorem Input.prepared_least {R lists c} (input : Input R lists c) :
    BestFitLarge.least (AllocWrapperCore.prepared R c) = BestFitLarge.least c := by
  apply input.prologue_read
  have stack := input.native_bounds.1
  have heap := input.stackHeap
  exact Or.inl (by simp only [Layout.sym_bf_large_least,DlHeap.heapStart] at *; omega)

theorem Input.prepared_header {R lists c} (input : Input R lists c) :
    BestFitLarge.header (AllocWrapperCore.prepared R c) = BestFitLarge.header c := by
  unfold BestFitLarge.header
  rw [input.prepared_least]
  apply input.prologue_read
  rw [show (BestFitLarge.least c - BitVec.ofNat 64 Layout.header_bytes).toNat =
    (BestFitLarge.least c).toNat-8 from input.source.header_nat]
  have sep := input.sourceNative
  have stack := input.native_bounds.1
  have large := input.source.large
  change _ + 8 ≤ _ ∨ _ ≤ _
  dsimp [sourceEnd] at sep
  omega

theorem Input.prepared_representation {R lists c} (input : Input R lists c) :
    BfShape.BoundedSmallRepresentation (AllocWrapperCore.prepared R c).σ.mem lists := by
  apply AllocOriginal.prepared_representation input.windows input.representation
  · have := input.stackHeap; have := input.native_bounds.1; omega
  · intro s lo hi x hx
    have := input.smallNative s lo hi x hx
    have := input.native_bounds.1
    omega

theorem Input.entered_least {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) : BestFitLarge.least middle = BestFitLarge.least c := by
  change bytesT middle.σ.mem _ 8 = _
  rw [entered.memory]
  exact input.prepared_least

theorem Input.entered_header {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) : BestFitLarge.header middle = BestFitLarge.header c := by
  calc
    BestFitLarge.header middle = BestFitLarge.header (AllocWrapperCore.prepared R c) := by
      simp only [BestFitLarge.header,BestFitLarge.least,word,entered.memory,AllocWrapperCore.prepared]
    _ = BestFitLarge.header c := input.prepared_header

/-- Every free-list observation is supplied by the original representation
and the actual wrapper prologue. No missing-slot or filtered-zero pin is input. -/
theorem Input.entry_input {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    BestFitFallback.EntryLargeInput (freeRegs R) lists middle := by
  have memory : middle.σ.mem = (AllocWrapperCore.prepared R c).σ.mem := entered.memory
  have least := input.entered_least entered
  have hd := input.entered_header entered
  refine { input.fallbackWindows with
    good := entered.good
    tick := entered.tick
    minstret := entered.minstret
    code := entered.image input.windows Code.bf_allocate_transport (by decide) input.freeCode
    registers := ⟨entered.link,gholds_lookup _ entered.registers rfl,
      gholds_lookup _ entered.registers rfl,True.intro⟩
    ffsCode := entered.image input.windows Code.ffs_transport (by decide) input.ffsCode
    remnantCode := entered.image input.windows Code.bf_insert_remnant_small_transport (by decide) input.remnantCode
    representation := memory ▸ input.prepared_representation.toSmallRepresentation
    requestPositive := input.positive
    stackHeap := input.stackHeap
    sources := input.smallSources
    aligned := by change AllocEntry.returnPc.toNat % 4 = 0; decide
    bounded := memory ▸ input.prepared_representation.bounded
    small := input.requestSmall
    noSuitable := input.noSuitable
    splitCode := entered.image input.windows Code.bf_split_transport (by decide) input.splitCode
    source := ?_ }
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [least] using input.source.headerWrite
  · simpa only [least] using input.source.heap
  · simpa only [least,hd] using input.source.fits
  · simpa only [hd,freeRegs_request] using input.source.large
  · simpa only [least,hd,nativeSp] using input.source.stack
  · simpa only [least,hd] using input.source.apart

theorem Input.result_header {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    BestFitFallback.largeHeader (freeRegs R) middle = header R c := by
  have entry := input.entry_input entered
  simp only [BestFitFallback.largeHeader,entry.toInput.searched_size,entry.searched_header,
    entry.searched_least,input.entered_header entered,input.entered_least entered]
  rfl

theorem Input.header_nat {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    (header R c).toNat = (BestFitLarge.least c).toNat-8 +
      8*((BestFitSplit.sizeWord (BestFitLarge.header c)).toNat-(R 10).toNat) := by
  have addr := (input.entry_input entered).largeHeader_nat
  simpa only [input.result_header entered,input.entered_header entered,input.entered_least entered,
    freeRegs_request] using addr

theorem Input.header_write {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) : WriteWindow (header R c) 8 := by
  have addr := input.header_nat entered
  have heap := input.source.heap
  have upper := input.sourceUpper
  have large := input.source.large
  have align := input.source.headerWrite.aligned
  rw [input.source.header_nat] at align
  simp only [sourceEnd] at upper
  constructor
  · rw [addr]; simp only [DlHeap.heapStart] at heap; omega
  · rw [addr]; simp only [DlHeap.heapEnd] at upper; omega
  · rw [addr]; simp only [DlHeap.heapStart,Layout.sym_tohost] at heap ⊢; omega
  · rw [addr]; omega

theorem Input.static_out {R lists c a n} (input : Input R lists c)
    (high : a+n ≤ DlHeap.heapStart)
    (counter : a+n ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ a) :
    OutWRange (windows R c) a n := by
  have heap := input.source.heap
  have stack := input.stackHeap
  change (a+n ≤ (nativeSp R).toNat ∨ (AllocEntry.frameSp R).toNat+48 ≤ a) ∧
    (a+n ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ a) ∧
    (a+n ≤ (BestFitLarge.least c).toNat-8 ∨ sourceEnd c ≤ a) ∧ True
  exact ⟨Or.inl (by omega),counter,Or.inl (by omega),True.intro⟩

theorem Input.free_inside {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    LogInW (windows R c) (BestFitFallback.completeEffect (freeRegs R) middle) := by
  apply logInW_transport (input.entry_input entered).complete_inside
  intro a n hin
  have heap := input.source.heap
  have large := input.source.large
  have bound := input.native_bounds.1
  simp only [BestFitFallback.entryLargeWindows,InsideW,input.entered_least entered,
    input.source.header_nat] at hin
  change ((nativeSp R).toNat ≤ a ∧ a+n ≤ (nativeSp R).toNat+32) ∨
    (Layout.sym_caml_fl_cur_wsz ≤ a ∧ a+n ≤ Layout.sym_caml_fl_cur_wsz+8) ∨
    ((BestFitLarge.least c).toNat-8 ≤ a ∧ a+n ≤ (BestFitLarge.least c).toNat-8+8) ∨ False at hin
  change ((nativeSp R).toNat ≤ a ∧ a+n ≤ (AllocEntry.frameSp R).toNat+48) ∨
    (Layout.sym_caml_fl_cur_wsz ≤ a ∧ a+n ≤ Layout.sym_caml_fl_cur_wsz+8) ∨
    ((BestFitLarge.least c).toNat-8 ≤ a ∧ a+n ≤ sourceEnd c) ∨ False
  dsimp only [sourceEnd]
  rcases hin with h | h | h | h
  · exact Or.inl ⟨h.1,by omega⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1,by omega⟩))
  · exact False.elim h

theorem Input.prefix_inside {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    LogInW (windows R c) (AllocEntry.effect R ++ BestFitFallback.completeEffect (freeRegs R) middle) := by
  apply logInW_join ?_ (input.free_inside entered)
  apply logInW_transport input.prologue_inside
  intro a n hin
  have := input.native_bounds.1
  change ((AllocEntry.frameSp R).toNat ≤ a ∧ a+n ≤ (AllocEntry.frameSp R).toNat+48) ∨ False at hin
  change ((nativeSp R).toNat ≤ a ∧ a+n ≤ (AllocEntry.frameSp R).toNat+48) ∨ _
  rcases hin with hin | impossible
  · exact Or.inl ⟨by omega,hin.2⟩
  · exact False.elim impossible

theorem Input.free_outside {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    ∀ cell ∈ AllocEntry.saveCells, OutLRange (BestFitFallback.completeEffect (freeRegs R) middle)
      (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8 := by
  intro cell member
  apply OCaml.Vm.Sim.outLRange_of_windows (input.entry_input entered).complete_inside
  have off := AllocEntry.saveCells_bounded cell member
  have addr := stack_address (AllocEntry.frameSp R) cell.2 AllocEntry.maxSave.2 input.windows.frame_bound off
  have stack := input.native_bounds.1
  have heap := input.stackHeap
  have sep := input.sourceNative
  simp only [BestFitFallback.entryLargeWindows,OutWRange,input.entered_least entered,
    input.source.header_nat]
  change ((AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat+8 ≤ (nativeSp R).toNat ∨
    (nativeSp R).toNat+32 ≤ (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat) ∧
    (_ ∨ _) ∧ (_ ∨ _) ∧ True
  rw [addr]
  change cell.2 ≤ 40 at off
  refine ⟨Or.inr (by omega),Or.inr ?_,?_,True.intro⟩
  · simp only [DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz] at heap ⊢; omega
  · have large := input.source.large
    have source := input.source.heap
    dsimp [sourceEnd] at sep
    omega

theorem Input.header_inside {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) (value : BitVec 64) :
    LogInW (windows R c) [((header R c).toNat,8,value)] := by
  have hd := input.header_nat entered
  have large := input.source.large
  have hp := input.source.heap
  simp only [LogInW,windows,InsideW]
  exact ⟨Or.inr (Or.inr (Or.inl ⟨by omega,by dsimp [sourceEnd]; omega⟩)),True.intro⟩

/-- The initialized snapshot reads original state/threshold/counters: header
installation is included, with no later-memory observation as an entry premise. -/
theorem Input.initialized_read {R lists c middle a n} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (outside : OutWRange (windows R c) a n) :
    bytesT (AllocAccount.initialized
      (AllocSuccess.completed (AllocFinish.entryRegs (AllocEntry.frameSp R) (R 10) (header R c))
        (AllocFinish.snapshot (BestFitFallback.completeEffect (freeRegs R) middle) middle))
      (AllocFinish.snapshot (BestFitFallback.completeEffect (freeRegs R) middle) middle)) a n =
      bytesT c.σ.mem a n :=
  AllocOriginal.initialized_read entered (input.prefix_inside entered) (input.header_inside entered) outside

def ready (R : Nat → BitVec 64) (middle : Config) :=
  AllocFinish.snapshot (BestFitFallback.completeEffect (freeRegs R) middle) middle
def finishRegs (R : Nat → BitVec 64) (c : Config) :=
  AllocFinish.entryRegs (AllocEntry.frameSp R) (R 10) (header R c)

theorem Input.ready_read {R lists c middle a n} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (outside : OutWRange (windows R c) a n) :
    bytesT (ready R middle).σ.mem a n = bytesT c.σ.mem a n :=
  AllocOriginal.ready_read entered (input.prefix_inside entered) outside

theorem Input.saved_tag {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    AllocSelect.tag (finishRegs R c) (ready R middle) = R 11 :=
  AllocOriginal.saved (cell := (11,AllocEntry.tagOffset)) entered input.windows (by decide)
    (input.free_outside entered _ (by decide))

/-- Phase-selected color computed using the original phase and sweep reads. -/
def isBlack (R : Nat → BitVec 64) (c : Config) := AllocSelect.isBlack (finishRegs R c) c

theorem Input.color {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    AllocSelect.isBlack (finishRegs R c) (ready R middle) = isBlack R c :=
  AllocOriginal.color entered (input.prefix_inside entered)
    (input.static_out (by decide) (by decide)) (input.static_out (by decide) (by decide))

/-- Concrete original-read suppliers for the shared successful continuation. -/
theorem Input.continuation {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    AllocSuccess.Conditions (finishRegs R c) (ready R middle) := by
  apply AllocOriginal.continuation entered input.windows (input.header_write entered)
    (input.initialized_read entered (input.static_out (by decide) (by decide)))
    (input.initialized_read entered (input.static_out (by decide) (by decide)))
    input.thresholdRead (input.initialized_read entered input.thresholdApart)
    input.noMajorSlice input.allocatedCredit (input.free_outside entered) ?_ input.aligned
  intro off member
  have offBound : off ≤ AllocEntry.maxSave.2 := by
    have bound : ∀ off ∈ AllocReturn.offsets, off ≤ AllocEntry.maxSave.2 := by decide
    exact bound off member
  have addr := stack_address (AllocEntry.frameSp R) off AllocEntry.maxSave.2 input.windows.frame_bound offBound
  have stack := input.native_bounds.1
  have heap := input.stackHeap
  have sep := input.sourceNative
  have hd := input.header_nat entered
  have large := input.source.large
  dsimp [sourceEnd] at sep
  change ((_+8 ≤ (header R c).toNat ∨ (header R c).toNat+8 ≤ _) ∧
    (_+8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words+8 ≤ _))
  rw [addr]
  change off ≤ 40 at offBound
  constructor
  · exact (by omega)
  · exact Or.inr (by simp only [Layout.sym_caml_allocated_words,DlHeap.heapStart] at heap ⊢; omega)

/-- Whole internal condition bundle supplied from the original caller facts
and the real prologue. This is a result, never an original-entry premise. -/
theorem Input.large_input {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    AllocLarge.Input (AllocEntry.frameSp R) (R 10) middle := by
  have entry := input.entry_input entered
  have missing := entry.toEntryInput.missing_of_noSuitable entry.small entry.noSuitable
  refine { missing with
    tagRead := input.windows.tag.read
    emptyBitmap := entry.filtered_zero
    large := entry.large_conditions
    returnOutside := entry.return_outside
    continuation := ?_
    ffsCode := entry.ffsCode
    splitCode := entry.splitCode
    wrapperCode := entered.code
    sizeRegister := gholds_lookup _ entered.registers rfl }
  change AllocSuccess.Conditions
    (AllocFinish.entryRegs (AllocEntry.frameSp R) (R 10) (BestFitFallback.largeHeader (freeRegs R) middle))
    (ready R middle)
  rw [input.result_header entered]
  exact input.continuation entered

theorem Input.wrapper_conditions {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) : AllocLargeWrapper.Conditions R c := by
  have memory : (AllocWrapperCore.prepared R c).σ.mem = middle.σ.mem := entered.memory.symm
  refine ⟨(input.large_input entered).toConditions.of_memory memory,?_⟩
  change ∀ cell ∈ AllocEntry.saveCells,
    OutLRange (BestFitFallback.completeEffect (freeRegs R) (AllocWrapperCore.prepared R c))
      (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8
  rw [BestFitFallback.completeEffect_of_memory memory]
  exact input.free_outside entered

/-- The finish summary writes exactly the initialized header and allocated
counter after the already proved physical split. -/
theorem finish_memory {R c lists middle freeState after}
    (split : BestFitFallback.EntryLargeReturned (freeRegs R) lists middle freeState)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) (header R c)
      (BestFitFallback.completeEffect (freeRegs R) middle) middle after) :
    after.σ.mem = writeLog freeState.σ.mem
      (AllocAccount.effect (AllocSuccess.completed (finishRegs R c) (ready R middle)) (ready R middle)) :=
  AllocOriginal.finish_memory split.memory finished

theorem finish_read {R c lists middle freeState after a n}
    (split : BestFitFallback.EntryLargeReturned (freeRegs R) lists middle freeState)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) (header R c)
      (BestFitFallback.completeEffect (freeRegs R) middle) middle after)
    (headerApart : a+n ≤ (header R c).toNat ∨ (header R c).toNat+8 ≤ a)
    (counterApart : a+n ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words+8 ≤ a) :
    bytesT after.σ.mem a n = bytesT freeState.σ.mem a n :=
  AllocOriginal.finish_read split.memory finished headerApart counterApart

theorem Input.finished_representation {R lists c middle freeState after} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (split : BestFitFallback.EntryLargeReturned (freeRegs R) lists middle freeState)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) (header R c)
      (BestFitFallback.completeEffect (freeRegs R) middle) middle after) :
    BfShape.BoundedSmallRepresentation after.σ.mem lists := by
  apply AllocOriginal.finished_representation (R := R) split.representation
    (by simpa only [input.result_header entered,freeRegs_request] using split.allocated) ?_ split.memory finished
  have hd := input.header_nat entered
  have heap := input.source.heap
  omega

structure Post (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) (before after : Config) : Prop
    extends AllocLargeWrapper.Post R before after where
  representation : BfShape.BoundedSmallRepresentation after.σ.mem lists
  originalResult : gprGet after.σ 10 = some (header R before + 8#64)
  exactHeader : word after (header R before).toNat = AllocColor.header (isBlack R before) (R 10) (R 11)
  headerOk : HeaderOk (word after (header R before).toNat) (R 10).toNat (R 11).toNat
  least : BestFitLarge.least after = BestFitLarge.least before
  remaining : word after (BestFitSplit.headerAddr (BestFitLarge.least before)).toNat =
    BestFitSplit.remnantHeader true (BestFitSplit.delta (R 10) (BestFitLarge.header before))
  remainingLarge : 16 < (BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1
  remainingBound : (BestFitLarge.least before).toNat+
    8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) < 2^64
  remainingApart : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ x ∈ lists s,
    (BestFitLarge.least before).toNat+
      8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) ≤ x.toNat-8 ∨
      x.toNat+8*s ≤ (BestFitLarge.least before).toNat-8
  boundary : (BestFitLarge.least before).toNat+
    8*((BestFitSplit.sizeWord (BestFitLarge.header before)).toNat-(R 10).toNat-1) = (header R before).toNat
  allocated : BestFitNext.AllocatedApart (header R before).toNat (R 10) lists
  freeCounter : (word after Layout.sym_caml_fl_cur_wsz).toNat =
    (word before Layout.sym_caml_fl_cur_wsz).toNat-((R 10).toNat+1)
  allocatedCounter : (word after Layout.sym_caml_allocated_words).toNat =
    (word before Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat
  inside : LogInW (fullWindows R before) (AllocLargeWrapper.effect R before)

theorem Input.wrapper_header {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) : AllocLargeWrapper.resultHeader R c = header R c := by
  have memory : middle.σ.mem = (AllocWrapperCore.prepared R c).σ.mem := entered.memory
  have same := AllocLarge.resultHeader_of_memory (sp := AllocEntry.frameSp R) (size := R 10)
    (before := AllocWrapperCore.prepared R c) (after := middle) memory
  change BestFitFallback.largeHeader (freeRegs R) middle = AllocLargeWrapper.resultHeader R c at same
  exact same.symm.trans (input.result_header entered)

theorem Input.wrapper_log {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    AllocLargeWrapper.freeEffect R c = BestFitFallback.completeEffect (freeRegs R) middle :=
  (AllocLarge.freeEffect_of_memory entered.memory).symm

/-- Reflect the entire actual wrapper write log once for caller frames. -/
theorem Input.effect_inside {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) :
    LogInW (fullWindows R c) (AllocLargeWrapper.effect R c) := by
  have memory : middle.σ.mem = (AllocWrapperCore.prepared R c).σ.mem := entered.memory
  have finishEq := AllocFinish.effect_of_memory (sp := AllocEntry.frameSp R) (size := R 10)
    (hp := header R c) (log := BestFitFallback.completeEffect (freeRegs R) middle) memory
  unfold AllocLargeWrapper.effect AllocWrapperCore.effect
  rw [input.wrapper_header entered,input.wrapper_log entered,← finishEq,AllocFinish.effect,← List.append_assoc]
  apply logInW_join
  · apply logInW_transport (input.prefix_inside entered)
    intro a n hin
    exact Or.inr hin
  · change LogInW (fullWindows R c)
      [((header R c).toNat,8,AllocSuccess.completed (finishRegs R c) (ready R middle) 11),
       (Layout.sym_caml_allocated_words,8,
        AllocAccount.counted (AllocSuccess.completed (finishRegs R c) (ready R middle)) (ready R middle))]
    exact ⟨Or.inr (input.header_inside entered _).1,Or.inl ⟨Nat.le_refl _,Nat.le_refl _⟩,True.intro⟩

/-- Representation and original-read results after the common finish, keeping
physical source/list separation through header initialization and accounting. -/
theorem Input.returned {R lists c middle freeState after} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (split : BestFitFallback.EntryLargeReturned (freeRegs R) lists middle freeState)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) (header R c)
      (BestFitFallback.completeEffect (freeRegs R) middle) middle after) : Post R lists c after := by
  have entry := input.entry_input entered
  have hd := input.header_nat entered
  have heap := input.source.heap
  have large := input.source.large
  have static (a n : Nat) (high : a+n ≤ DlHeap.heapStart)
      (counter : a+n ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words+8 ≤ a) :
      bytesT after.σ.mem a n = bytesT freeState.σ.mem a n := by
    apply finish_read split finished _ counter
    exact Or.inl (by omega)
  have least : BestFitLarge.least after = BestFitLarge.least c :=
    (static _ _ (by decide) (by decide)).trans (split.least.trans (input.entered_least entered))
  have sourceRead : word after (BestFitSplit.headerAddr (BestFitLarge.least c)).toNat =
      word freeState (BestFitSplit.headerAddr (BestFitLarge.least c)).toNat := by
    apply finish_read split finished
    · rw [input.source.header_nat]
      exact Or.inl (by omega)
    · rw [input.source.header_nat]
      exact Or.inr (by simp only [Layout.sym_caml_allocated_words,DlHeap.heapStart] at heap ⊢; omega)
  have remaining := split.toAllocated.entry_header entry
  rw [entry.split_large,input.entered_header entered,input.entered_least entered,freeRegs_request] at remaining
  have freeOriginal : word middle Layout.sym_caml_fl_cur_wsz = word c Layout.sym_caml_fl_cur_wsz := by
    rw [word,entered.memory]
    exact input.prologue_read (Or.inl (by
      have := input.native_bounds.1; have := input.stackHeap
      simp only [Layout.sym_caml_fl_cur_wsz,DlHeap.heapStart] at *; omega))
  have credit : (freeRegs R 10).toNat+1 ≤ (word middle Layout.sym_caml_fl_cur_wsz).toNat := by
    rw [freeOriginal]; exact input.freeCredit
  have freeCount := split.toAllocated.entry_counter_nat entry credit
  rw [freeOriginal,freeRegs_request] at freeCount
  have finalFree := static Layout.sym_caml_fl_cur_wsz 8 (by decide) (by decide)
  have memory := finish_memory split finished
  have headerStored : word after (header R c).toNat =
      AllocSuccess.completed (finishRegs R c) (ready R middle) 11 := by
    rw [word,memory]
    apply word_writeLog_at _ _ 0 _ _ rfl
    exact ⟨Or.inr (by simp only [Layout.sym_caml_allocated_words,DlHeap.heapStart] at heap ⊢; omega),True.intro⟩
  have exactHeader : word after (header R c).toNat = AllocColor.header (isBlack R c) (R 10) (R 11) := by
    rw [headerStored]
    change AllocColor.header (AllocSelect.isBlack (finishRegs R c) (ready R middle)) (R 10)
      (AllocSelect.tag (finishRegs R c) (ready R middle)) = _
    rw [input.color entered,input.saved_tag entered]
  have allocatedCounter : word after Layout.sym_caml_allocated_words =
      AllocAccount.counted (AllocSuccess.completed (finishRegs R c) (ready R middle)) (ready R middle) := by
    rw [word,memory]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial
  have countedOriginal : (word after Layout.sym_caml_allocated_words).toNat =
      (word c Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat := by
    have read : bytesT (AllocAccount.initialized
        (AllocSuccess.completed (finishRegs R c) (ready R middle)) (ready R middle))
        Layout.sym_caml_allocated_words 8 = word c Layout.sym_caml_allocated_words :=
      input.initialized_read entered (input.static_out (by decide) (by decide))
    rw [allocatedCounter,AllocAccount.counted,read]
    change ((word c Layout.sym_caml_allocated_words)+1#64+R 10).toNat = _
    have bound := input.allocatedCredit
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  have complete := entered.complete input.windows (input.free_outside entered) finished
  have wrapper : AllocLargeWrapper.Post R c after := by
    simpa only [AllocLargeWrapper.Post,input.wrapper_header entered,input.wrapper_log entered] using complete
  have sizeBound : (R 10).toNat < 2^54 := by
    have small := input.requestSmall
    change (R 10).toNat ≤ 16 at small
    omega
  refine ⟨wrapper,input.finished_representation entered split finished,?_,exactHeader,?_,least,
    sourceRead.trans remaining,?_,?_,?_,?_,?_,?_,countedOriginal,input.effect_inside entered⟩
  · simpa only [input.wrapper_header entered,Layout.header_bytes] using wrapper.result
  · rw [exactHeader]
    exact AllocColor.header_ok _ _ _ sizeBound input.tagBound
  · simpa only [input.entered_header entered,freeRegs_request] using split.remainingLarge
  · simpa only [input.entered_header entered,input.entered_least entered,freeRegs_request] using split.remainingBound
  · simpa only [input.entered_header entered,input.entered_least entered,freeRegs_request] using split.remainingApart
  · simpa only [input.entered_header entered,input.entered_least entered,input.result_header entered,freeRegs_request] using split.boundary
  · simpa only [input.result_header entered,freeRegs_request] using split.allocated
  · exact (congrArg BitVec.toNat finalFree).trans freeCount

/-- Actual wrapper entry, bounded original-entry least-large split, shared
color/accounting finish and original caller ABI, with preserved representation. -/
theorem allocate {R lists c} (input : Input R lists c) :
    FnSummary AllocEntry.pc (fun d => d = c) (Post R lists c) := by
  constructor
  apply Vsa.Logic.Triple.seq (AllocWrapperCore.enter input.toInput).run
  intro middle entered
  obtain ⟨freeState,freeRun,split⟩ := (BestFitFallback.allocate_entry_large (input.entry_input entered)).run
    middle ⟨entered.pc,rfl⟩
  have body := input.large_input entered
  obtain ⟨after,finishRun,finished⟩ := (body.finish split.toAllocated).run freeState ⟨split.pc,rfl⟩
  have normalized : AllocFinish.Post (AllocEntry.frameSp R) (R 10) (header R c)
      (BestFitFallback.completeEffect (freeRegs R) middle) middle after := by
    change AllocFinish.Post (AllocEntry.frameSp R) (R 10)
      (BestFitFallback.largeHeader (freeRegs R) middle)
      (BestFitFallback.completeEffect (freeRegs R) middle) middle after at finished
    rw [input.result_header entered] at finished
    exact finished
  exact ⟨after,freeRun.trans finishRun,input.returned entered split normalized⟩

/-- Caller payload framing uses `LogWindows` with the returned exact log.
The caller supplies its own payload geometry and window classifications. -/
theorem Post.logWindows {R lists before after P s pl cp top high offs}
    (post : Post R lists before after)
    (geometry : OCaml.Vm.Sim.StackGeometry P s before pl cp high)
    (kinds : ∀ w ∈ fullWindows R before, OCaml.Vm.Sim.LogWindow P s before pl cp top high offs w)
    (topBound : top ≤ high) (fits : ∀ off ∈ offs, off+8 ≤ Layout.domainStateBytes) :
    OCaml.Vm.Sim.LogWindows (AllocLargeWrapper.effect R before) P s before pl cp top high offs :=
  ⟨geometry,⟨fullWindows R before,post.inside,kinds⟩,topBound,fits⟩

/-- Selected caller ledgers use the shared ownership frame, with explicit
separation from the composed actual write log. Geometry alone supplies no ledger. -/
theorem Post.live {R lists before after H} (post : Post R lists before after)
    (bounds : ∀ e ∈ H, DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ DlHeap.heapEnd)
    (outside : ∀ x, x < DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (AllocLargeWrapper.effect R before) x) : LiveFrame H before after :=
  AllocOriginal.live post.memory bounds outside

end OCaml.Vm.Gc.AllocEntryLarge
