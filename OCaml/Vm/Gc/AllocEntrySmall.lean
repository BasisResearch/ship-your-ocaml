import OCaml.Vm.Gc.AllocOriginal
import OCaml.Vm.Gc.BestFitEntrySmall

/-! Original-caller small success for caml_alloc_shr_for_minor_gc.
The selected physical family survives the real header, accounting and return.
Caller invariant production, large search, expansion and collection stay separate. -/
namespace OCaml.Vm.Gc.AllocEntrySmall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup BestFitNext BestFitFallback

def freeRegs (R : Nat → BitVec 64) (n : Nat) :=
  if n = 1 then AllocEntry.returnPc else if n = 2 then AllocEntry.frameSp R else R 10

def nativeSp (R : Nat → BitVec 64) := BestFitFallback.frameSp (freeRegs R)

def windows (R : Nat → BitVec 64) (s : Nat) (b : BitVec 64) :=
  AllocOriginal.prologueWindows R ++ smallFreeWindows (nativeSp R) s b

def fullWindows (R : Nat → BitVec 64) (s : Nat) (b : BitVec 64) :=
  ⟨Layout.sym_caml_allocated_words,Layout.sym_caml_allocated_words+8⟩ :: windows R s b

/-- Facts of the original memory, selected physical sources and both native
frames. Natural credit is separate from the bounded representation. -/
structure Facts (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) (c : Config) : Prop where
  representation : BfShape.BoundedSmallRepresentation c.σ.mem lists
  positive : 1 ≤ (R 10).toNat
  suitable : ∃ s, (R 10).toNat ≤ s ∧ s ≤ 16 ∧ lists s ≠ []
  fallbackWindows : BestFitFallback.StackConditions (freeRegs R)
  stackHeap : DlHeap.heapStart ≤ (nativeSp R).toNat
  sources : ∀ s, 1 ≤ s → s ≤ 16 → ∀ b ∈ lists s, SearchSource (nativeSp R) b
  sourceUpper : ∀ s, (R 10).toNat ≤ s → s ≤ 16 → ∀ b ∈ lists s,
    b.toNat+8*s ≤ DlHeap.heapEnd
  sourceNative : ∀ s, 1 ≤ s → s ≤ 16 → ∀ b ∈ lists s,
    b.toNat+8*s ≤ (nativeSp R).toNat ∨ (AllocEntry.frameSp R).toNat+48 ≤ b.toNat-8
  thresholdRead : ReadWindow (AllocOriginal.threshold c) 8
  thresholdApart : ∀ s, (R 10).toNat ≤ s → s ≤ 16 → ∀ b ∈ lists s,
    OutWRange (windows R s b) (AllocOriginal.threshold c).toNat 8
  noMajorSlice : (word c Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat ≤
    (word c (AllocOriginal.threshold c).toNat).toNat
  allocatedCredit : (word c Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat < 2^64
  freeCredit : ∀ s, (R 10).toNat ≤ s → s ≤ 16 → lists s ≠ [] →
    s+1 ≤ (word c Layout.sym_caml_fl_cur_wsz).toNat
  tagBound : (R 11).toNat < 256
  aligned : (R 1).toNat % 4 = 0

/-- Actual wrapper ABI, code and free-list pointer at the original caller. -/
structure Input (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) (c : Config) : Prop
    extends AllocEntry.Input R BestFitSmall.pc c, Facts R lists c where
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  ffsCode : Code.FfsLoaded c.σ.mem
  remnantCode : Code.Bf_insert_remnant_smallLoaded c.σ.mem

theorem Input.native_bounds {R lists c} (input : Input R lists c) :
    (nativeSp R).toNat+32 = (AllocEntry.frameSp R).toNat ∧
    (AllocEntry.frameSp R).toNat+48 ≤ 0x100000000 :=
  AllocOriginal.native_bounds input.windows

theorem Input.prepared_representation {R lists c} (input : Input R lists c) :
    BfShape.BoundedSmallRepresentation (AllocWrapperCore.prepared R c).σ.mem lists := by
  apply AllocOriginal.prepared_representation input.windows input.representation
  · have := input.stackHeap; have := input.native_bounds.1; omega
  · intro s lo hi x hx
    have := input.sourceNative s lo hi x hx
    have := input.native_bounds.1
    omega

/-- Native search and exact-size conditions are derived on the actual entered
state from the represented family, prologue and original physical windows. -/
theorem Input.entry_input {R lists c middle} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle) : EntrySmallInput (freeRegs R) lists middle := by
  refine { input.fallbackWindows with
    good := entered.good
    tick := entered.tick
    minstret := entered.minstret
    code := entered.image input.windows Code.bf_allocate_transport (by decide) input.freeCode
    registers := ⟨entered.link,gholds_lookup _ entered.registers rfl,
      gholds_lookup _ entered.registers rfl,True.intro⟩
    ffsCode := entered.image input.windows Code.ffs_transport (by decide) input.ffsCode
    remnantCode := entered.image input.windows Code.bf_insert_remnant_small_transport (by decide) input.remnantCode
    representation := entered.memory ▸ input.prepared_representation.toSmallRepresentation
    requestPositive := input.positive
    stackHeap := input.stackHeap
    sources := input.sources
    aligned := by change AllocEntry.returnPc.toNat % 4 = 0; decide
    suitable := input.suitable }

/-- Small static words sit below both frames and every selected source. -/
theorem Input.static_out {R lists c s b a n} (input : Input R lists c)
    (positive : 1 ≤ s) (small : s ≤ 16) (member : b ∈ lists s)
    (high : a+n ≤ DlHeap.heapStart)
    (map : a+n ≤ Layout.sym_bf_small_map ∨ Layout.sym_bf_small_map+4 ≤ a)
    (free : a+n ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ a)
    (slots : a+n ≤ Layout.sym_bf_small_fl+16 ∨ Layout.sym_bf_small_fl+16*17 ≤ a) :
    OutWRange (windows R s b) a n := by
  have heap := input.representation.physical.bounds s positive small b member
  have stack := input.stackHeap
  have frames := input.native_bounds.1
  simp only [windows,AllocOriginal.prologueWindows,smallFreeWindows,List.cons_append,List.nil_append,OutWRange]
  exact ⟨Or.inl (by omega),Or.inl (by omega),map,free,slots,Or.inl (by omega),True.intro⟩

theorem Input.source_header {R lists c middle s b} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (lo : 1 ≤ s) (hi : s ≤ 16) (member : b ∈ lists s) :
    sourceHeader b middle.σ.mem = sourceHeader b c.σ.mem := by
  unfold sourceHeader
  rw [entered.memory]
  have hn := input.representation.physical.header_nat lo hi member
  have bounds := input.representation.physical.bounds s lo hi b member
  apply AllocOriginal.prologue_read input.windows
  rw [hn]
  have := input.sourceNative s lo hi b member
  have := input.native_bounds.1
  omega

/-- Selected source geometry is retained beside the checked native return. -/
structure Selection (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (a : BitVec 64) (before : Config) : Prop where
  larger : (R 10).toNat ≤ s
  small : s ≤ 16
  member : b ∈ lists s
  originalSize : sourceSize (sourceHeader b before.σ.mem) = BitVec.ofNat 64 s
  interval : b.toNat-8 ≤ a.toNat
  boundary : a.toNat+8*((R 10).toNat+1) = b.toNat+8*s
  headerWrite : WriteWindow a 8

theorem Input.selection {R lists c middle freeState s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState) :
    Selection R lists s b a c := by
  have entry := input.entry_input entered
  have bounds := post.class_bounds entry
  have lo : 1 ≤ s := by have := input.positive; have := bounds.1; change (R 10).toNat ≤ s at this; omega
  have member : b ∈ lists s := by rw [post.selected]; simp
  have physical := input.representation.physical.bounds s lo bounds.2 b member
  have interval := post.result_interval entry
  change b.toNat-8 ≤ a.toNat ∧ a.toNat+8*((R 10).toNat+1) = b.toNat+8*s at interval
  have hn := input.representation.physical.header_nat lo bounds.2 member
  have align := (input.sources s lo bounds.2 b member).header.aligned
  rw [hn] at align
  have upper := input.sourceUpper s bounds.1 bounds.2 b member
  refine ⟨bounds.1,bounds.2,member,?_,interval.1,interval.2,?_⟩
  · rw [← input.source_header entered lo bounds.2 member]; exact post.originalSize
  · constructor
    · simp only [DlHeap.heapStart] at physical ⊢; omega
    · simp only [DlHeap.heapEnd] at upper ⊢; omega
    · simp only [DlHeap.heapStart,Layout.sym_tohost] at physical ⊢; omega
    · omega

/-- Original wrapper saves and native small writes, reflected together. -/
theorem Input.prefix_inside {R lists c middle freeState s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState) :
    LogInW (windows R s b) (AllocEntry.effect R ++ writes) := by
  apply logInW_join
  · apply logInW_transport (AllocOriginal.prologue_inside input.windows)
    intro x n inside
    change (_ ∨ False) at inside
    change _ ∨ _
    exact Or.inl (by rcases inside with h | h; exact h; exact h.elim)
  · apply logInW_transport (post.log_inside (input.entry_input entered))
    intro x n inside
    change (_ ∨ _)
    exact Or.inr inside

theorem Selection.header_inside {R lists s b a c} (selected : Selection R lists s b a c) (v : BitVec 64) :
    LogInW (windows R s b) [(a.toNat,8,v)] := by
  have lo := selected.interval
  have hi := selected.boundary
  simp only [windows,AllocOriginal.prologueWindows,smallFreeWindows,List.cons_append,List.nil_append,LogInW,InsideW]
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,by omega⟩))))),True.intro⟩

/-- Free-list writes avoid the wrapper's complete saved bank, including tag. -/
theorem Input.free_outside {R lists c middle freeState s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState) :
    ∀ cell ∈ AllocEntry.saveCells, OutLRange writes
      (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8 := by
  have selected := input.selection entered post
  have positive : 1 ≤ s := by have := input.positive; have := selected.larger; omega
  intro cell member
  apply OCaml.Vm.Sim.outLRange_of_windows (post.log_inside (input.entry_input entered))
  have off := AllocEntry.saveCells_bounded cell member
  have addr := stack_address (AllocEntry.frameSp R) cell.2 AllocEntry.maxSave.2 input.windows.frame_bound off
  have stack := input.native_bounds.1
  have heap := input.stackHeap
  change DlHeap.heapStart ≤ (BestFitFallback.frameSp (freeRegs R)).toNat at heap
  change (BestFitFallback.frameSp (freeRegs R)).toNat+32 = _ at stack
  have sep := input.sourceNative s positive selected.small b selected.member
  change b.toNat+8*s ≤ (BestFitFallback.frameSp (freeRegs R)).toNat ∨ _ at sep
  simp only [smallFreeWindows,OutWRange,addr]
  change cell.2 ≤ 40 at off
  refine ⟨Or.inr (by omega),Or.inr ?_,Or.inr ?_,Or.inr ?_,by omega,True.intro⟩
  all_goals simp only [DlHeap.heapStart,Layout.sym_bf_small_map,Layout.sym_caml_fl_cur_wsz,Layout.sym_bf_small_fl] at heap ⊢
  all_goals omega

/-- Concrete finish suppliers from original reads and the selected real log. -/
theorem Input.continuation {R lists c middle freeState s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState) :
    AllocSuccess.Conditions (AllocOriginal.regs R a) (AllocOriginal.ready writes middle) := by
  have selected := input.selection entered post
  have positive : 1 ≤ s := by have := input.positive; have := selected.larger; omega
  have read {x n : Nat} := AllocOriginal.initialized_read (a := x) (n := n) entered (input.prefix_inside entered post) selected.header_inside
  apply AllocOriginal.continuation entered input.windows selected.headerWrite
    (read (input.static_out positive selected.small selected.member (by decide) (by decide) (by decide) (by decide)))
    (read (input.static_out positive selected.small selected.member (by decide) (by decide) (by decide) (by decide)))
    input.thresholdRead (read (input.thresholdApart s selected.larger selected.small b selected.member))
    input.noMajorSlice input.allocatedCredit (input.free_outside entered post) ?_ input.aligned
  intro off member
  have offBound : off ≤ AllocEntry.maxSave.2 := by
    have bound : ∀ off ∈ AllocReturn.offsets, off ≤ AllocEntry.maxSave.2 := by decide
    exact bound off member
  have addr := stack_address (AllocEntry.frameSp R) off AllocEntry.maxSave.2 input.windows.frame_bound offBound
  have sep := input.sourceNative s positive selected.small b selected.member
  have hd := selected.interval
  have upper := selected.boundary
  have stack := input.native_bounds.1
  have heap := input.stackHeap
  rw [addr]
  change off ≤ 40 at offBound
  refine ⟨by omega,Or.inr ?_⟩
  simp only [Layout.sym_caml_allocated_words,DlHeap.heapStart] at heap ⊢
  omega

/-- Adapt the proved small callee to the shared finish; code and the saved
size register are framed from the actual entered state. -/
theorem Input.callee {R lists c middle freeState s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState) :
    AllocFinish.CalleePost (AllocEntry.frameSp R) (R 10) a writes middle freeState [16,17] := by
  have inside := post.log_inside (input.entry_input entered)
  have selected := input.selection entered post
  have positive : 1 ≤ s := by have := input.positive; have := selected.larger; omega
  have source := input.representation.physical.bounds s positive selected.small b selected.member
  have code : Code.Caml_alloc_shr_for_minor_gcLoaded freeState.σ.mem := by
    rw [post.memory]
    apply image_writeLog Code.caml_alloc_shr_for_minor_gc_transport entered.code
    intro e member
    have within := logInW_member inside member
    have stack := input.stackHeap
    change DlHeap.heapStart ≤ (BestFitFallback.frameSp (freeRegs R)).toNat at stack
    simp only [smallFreeWindows,InsideW] at within
    rcases within with h | h | h | h | h | h
    all_goals simp only [DlHeap.heapStart,Layout.sym_tohost,Layout.sym_bf_small_map,
      Layout.sym_caml_fl_cur_wsz,Layout.sym_bf_small_fl] at *
    all_goals omega
  have savedSize : gprGet freeState.σ 8 = some (R 10) :=
    post.native.get (by decide) (by decide) (by decide) (gholds_lookup _ entered.registers rfl)
  refine ⟨post.good,post.tick,post.minstret,code,post.pc,
    ⟨post.stack,savedSize,post.result,True.intro⟩,post.memory,post.output,?_⟩
  intro r noise outside
  exact post.frame r noise outside

/-- Both real stages and the existing native branch witness remain available. -/
structure Path (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64)) (family : Nat → List (BitVec 64))
    (a : BitVec 64) (writes : List WEntry) (before after middle freeState : Config) : Prop where
  entered : AllocWrapperCore.Entered R before middle
  allocated : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState
  finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) a writes middle after [16,17]

/-- Exact original-caller small success, with the actual remaining family and
branch-dependent natural free accounting under original selected credit. -/
structure Post (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64))
    (s : Nat) (b : BitVec 64) (bs : List (BitVec 64)) (family : Nat → List (BitVec 64))
    (a : BitVec 64) (writes : List WEntry) (before after : Config) : Prop
    extends AllocWrapperCore.Post R a writes before after [16,17] where
  selected : lists s = b :: bs
  source : Selection R lists s b a before
  representation : BfShape.BoundedSmallRepresentation after.σ.mem family
  allocated : AllocatedApart a.toNat (R 10) family
  exactHeader : word after a.toNat = AllocColor.header (AllocOriginal.isBlack a before) (R 10) (R 11)
  headerOk : HeaderOk (word after a.toNat) (R 10).toNat (R 11).toNat
  freeCounter : (word after Layout.sym_caml_fl_cur_wsz).toNat =
    (word before Layout.sym_caml_fl_cur_wsz).toNat-(s+1)+
      smallRefund (freeRegs R) s b (AllocWrapperCore.prepared R before)
  allocatedCounter : (word after Layout.sym_caml_allocated_words).toNat =
    (word before Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat
  inside : LogInW (fullWindows R s b) (AllocWrapperCore.effect R a writes before)
  path : ∃ middle freeState, Path R lists s b bs family a writes before after middle freeState

theorem Post.path_spec {R lists s b bs family a writes before after}
    (post : Post R lists s b bs family a writes before after) :
    ∃ middle freeState, Path R lists s b bs family a writes before after middle freeState := post.path

/-- The full reflected log includes the original saves, actual native small
writes, phase-selected allocated header and allocated-word counter. -/
theorem Input.effect_inside {R lists c middle freeState s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState) :
    LogInW (fullWindows R s b) (AllocWrapperCore.effect R a writes c) := by
  have selected := input.selection entered post
  have same := AllocFinish.effect_of_memory (sp := AllocEntry.frameSp R) (size := R 10)
    (hp := a) (log := writes) (before := AllocWrapperCore.prepared R c) (after := middle) entered.memory
  unfold AllocWrapperCore.effect
  rw [← same,AllocFinish.effect,← List.append_assoc]
  apply logInW_join
  · apply logInW_transport (input.prefix_inside entered post)
    intro x n inside; exact Or.inr inside
  · change LogInW (fullWindows R s b)
      [(a.toNat,8,AllocSuccess.completed (AllocOriginal.regs R a) (AllocOriginal.ready writes middle) 11),
       (Layout.sym_caml_allocated_words,8,_)]
    exact ⟨Or.inr (selected.header_inside _).1,Or.inl ⟨Nat.le_refl _,Nat.le_refl _⟩,True.intro⟩

/-- Preserve the selected representation through header/color/accounting and
recover original size, tag, phase-selected color, counters and caller bank. -/
theorem Input.returned {R lists c middle freeState after s b bs family a writes} (input : Input R lists c)
    (entered : AllocWrapperCore.Entered R c middle)
    (post : EntrySmallReturned (freeRegs R) lists s b bs family a writes middle freeState)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) a writes middle after [16,17]) :
    Post R lists s b bs family a writes c after := by
  have entry := input.entry_input entered
  have selected := input.selection entered post
  have positive : 1 ≤ s := by have := input.positive; have := selected.larger; omega
  have physical := input.representation.physical.bounds s positive selected.small b selected.member
  have headerHeap : DlHeap.heapStart ≤ a.toNat := by have := selected.interval; omega
  have prefixLog := input.prefix_inside entered post
  have static {x n : Nat} := input.static_out (a := x) (n := n) positive selected.small selected.member
  have initialized {x n : Nat} := AllocOriginal.initialized_read (a := x) (n := n) entered prefixLog selected.header_inside
  have memory := AllocOriginal.finish_memory post.memory finished
  have separate : Layout.sym_caml_allocated_words+8 ≤ a.toNat := by
    simp only [DlHeap.heapStart,Layout.sym_caml_allocated_words] at headerHeap ⊢; omega
  have stored : word after a.toNat = AllocSuccess.completed (AllocOriginal.regs R a)
      (AllocOriginal.ready writes middle) 11 := by
    rw [word,memory]
    apply word_writeLog_at _ _ 0 _ _ rfl
    exact ⟨Or.inr separate,True.intro⟩
  have tag : AllocSelect.tag (AllocOriginal.regs R a) (AllocOriginal.ready writes middle) = R 11 :=
    AllocOriginal.saved (cell := (11,AllocEntry.tagOffset)) entered input.windows (by decide)
      (input.free_outside entered post _ (by decide))
  have color := AllocOriginal.color (hp := a) entered prefixLog
    (static (by decide) (by decide) (by decide) (by decide))
    (static (by decide) (by decide) (by decide) (by decide))
  have exactHeader : word after a.toNat = AllocColor.header (AllocOriginal.isBlack a c) (R 10) (R 11) := by
    rw [stored]
    change AllocColor.header (AllocSelect.isBlack (AllocOriginal.regs R a) (AllocOriginal.ready writes middle))
      (R 10) (AllocSelect.tag (AllocOriginal.regs R a) (AllocOriginal.ready writes middle)) = _
    rw [color,tag]
  have freeOriginal : word middle Layout.sym_caml_fl_cur_wsz = word c Layout.sym_caml_fl_cur_wsz := by
    rw [word,entered.memory]
    apply AllocOriginal.prologue_read input.windows
    apply Or.inl
    have heap := input.stackHeap
    have frames := input.native_bounds.1
    simp only [DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz] at heap ⊢
    omega
  have credit := input.freeCredit s selected.larger selected.small (by rw [post.selected]; simp)
  have freeCount := post.counter_nat entry (by rw [freeOriginal]; exact credit)
  have refund := smallRefund_of_memory (R := freeRegs R) (s := s) (b := b)
    (before := AllocWrapperCore.prepared R c) (after := middle) entered.memory
  rw [freeOriginal,refund] at freeCount
  have finalFree : word after Layout.sym_caml_fl_cur_wsz = word freeState Layout.sym_caml_fl_cur_wsz :=
    AllocOriginal.finish_read post.memory finished (Or.inl (by
      simp only [DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz] at headerHeap ⊢; omega)) (by decide)
  have counterStored : word after Layout.sym_caml_allocated_words = AllocAccount.counted
      (AllocSuccess.completed (AllocOriginal.regs R a) (AllocOriginal.ready writes middle))
      (AllocOriginal.ready writes middle) := by
    rw [word,memory]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial
  have counted : (word after Layout.sym_caml_allocated_words).toNat =
      (word c Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat := by
    rw [counterStored,AllocAccount.counted,initialized (static (by decide) (by decide) (by decide) (by decide))]
    change ((word c Layout.sym_caml_allocated_words)+1#64+R 10).toNat = _
    have := input.allocatedCredit
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
  have sizeBound : (R 10).toNat < 2^54 := by have := selected.larger; have := selected.small; omega
  refine ⟨entered.complete input.windows (input.free_outside entered post) finished,post.selected,selected,
    AllocOriginal.finished_representation (R := R) (post.boundedSmallRepresentation entry
      (entered.memory ▸ input.prepared_representation.bounded)) post.allocated headerHeap post.memory finished,
    post.allocated,exactHeader,?_,?_,counted,input.effect_inside entered post,⟨middle,freeState,entered,post,finished⟩⟩
  · rw [exactHeader]; exact AllocColor.header_ok _ _ _ sizeBound input.tagBound
  · exact (congrArg BitVec.toNat finalFree).trans freeCount

structure Returned (R : Nat → BitVec 64) (lists : Nat → List (BitVec 64)) (before after : Config) : Prop where
  selected : ∃ s b bs family a writes, Post R lists s b bs family a writes before after

theorem Returned.selected_spec {R lists before after} (post : Returned R lists before after) :
    ∃ s b bs family a writes, Post R lists s b bs family a writes before after := post.selected

/-- Actual original wrapper success for every existing exact-size branch and
next-size dispatch with a suitable represented class. No later-state premise. -/
theorem allocate {R lists c} (input : Input R lists c) :
    FnSummary AllocEntry.pc (fun d => d = c) (Returned R lists c) := by
  constructor
  apply Vsa.Logic.Triple.seq (AllocWrapperCore.enter input.toInput).run
  intro middle entered
  obtain ⟨freeState,freeRun,allocated⟩ := (allocate_entry_small (input.entry_input entered)).run middle ⟨entered.pc,rfl⟩
  obtain ⟨s,b,bs,family,a,writes,post⟩ := allocated.selected_spec
  obtain ⟨after,finishRun,finished⟩ := ((input.callee entered post).finish input.windows.tag.read
    (input.continuation entered post)).run freeState ⟨post.pc,rfl⟩
  exact ⟨after,freeRun.trans finishRun,⟨s,b,bs,family,a,writes,input.returned entered post finished⟩⟩

/-- Caller payload transport uses the selected actual windows. -/
theorem Post.logWindows {R lists s b bs family a writes before after P st pl cp top high offs}
    (post : Post R lists s b bs family a writes before after)
    (geometry : OCaml.Vm.Sim.StackGeometry P st before pl cp high)
    (kinds : ∀ w ∈ fullWindows R s b, OCaml.Vm.Sim.LogWindow P st before pl cp top high offs w)
    (topBound : top ≤ high) (fits : ∀ off ∈ offs, off+8 ≤ Layout.domainStateBytes) :
    OCaml.Vm.Sim.LogWindows (AllocWrapperCore.effect R a writes before) P st before pl cp top high offs :=
  AllocOriginal.logWindows post.toPost post.inside geometry kinds topBound fits

/-- Selected caller ownership is an explicit ledger and log-separation fact. -/
theorem Post.live {R lists s b bs family a writes before after H}
    (post : Post R lists s b bs family a writes before after)
    (bounds : ∀ e ∈ H, DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ DlHeap.heapEnd)
    (outside : ∀ x, x < DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (AllocWrapperCore.effect R a writes before) x) : LiveFrame H before after :=
  AllocOriginal.live post.memory bounds outside

end OCaml.Vm.Gc.AllocEntrySmall
