import OCaml.Vm.Gc.AllocWrapperCore
import OCaml.Vm.Gc.BestFitPreservation
import OCaml.Vm.Sim.PayloadWindows

/-! Shared original-caller observations for every successful wrapper route.
These laws consume reflected logs, never an assumed native execution. -/
namespace OCaml.Vm.Gc.AllocOriginal
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup

def prologueWindows (R : Nat → BitVec 64) : List W :=
  [⟨(AllocEntry.frameSp R).toNat,(AllocEntry.frameSp R).toNat+48⟩]

/-- The 32-byte free-list frame meets the 48-byte wrapper frame without wrap. -/
theorem native_bounds {R} (windows : AllocEntry.Windows R) :
    (AllocEntry.frameSp R - 32#64).toNat+32 = (AllocEntry.frameSp R).toNat ∧
    (AllocEntry.frameSp R).toNat+48 ≤ 0x100000000 := by
  have upper := windows.frame_bound
  have addr := stack_address (AllocEntry.frameSp R) AllocEntry.maxSave.2 AllocEntry.maxSave.2 upper (by omega)
  have lower := (windows.saved AllocEntry.maxSave (by decide)).lower
  rw [addr] at lower
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat,AllocEntry.maxSave,AllocEntry.saves,List.head!] at upper lower ⊢
  constructor <;> omega

theorem prologue_inside {R} (windows : AllocEntry.Windows R) :
    LogInW (prologueWindows R) (AllocEntry.effect R) := by
  rw [AllocEntry.effect_bank]
  apply logInW_of_forall
  intro e member
  obtain ⟨cell,hcell,rfl⟩ := List.mem_map.mp member
  have off := AllocEntry.saveCells_bounded cell hcell
  have addr := stack_address (AllocEntry.frameSp R) cell.2 AllocEntry.maxSave.2 windows.frame_bound off
  simp only [InsideW,prologueWindows,addr,AllocEntry.maxSave,AllocEntry.saves,List.head!] at off ⊢
  exact Or.inl ⟨by omega,by omega⟩

theorem prologue_read {R c a n} (windows : AllocEntry.Windows R)
    (outside : a+n ≤ (AllocEntry.frameSp R).toNat ∨ (AllocEntry.frameSp R).toNat+48 ≤ a) :
    bytesT (AllocWrapperCore.prepared R c).σ.mem a n = bytesT c.σ.mem a n :=
  bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (prologue_inside windows) ⟨outside,True.intro⟩)

theorem prepared_representation {R c lists} (windows : AllocEntry.Windows R)
    (repr : BfShape.BoundedSmallRepresentation c.σ.mem lists)
    (stackHeap : DlHeap.heapStart ≤ (AllocEntry.frameSp R).toNat)
    (separate : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ x ∈ lists s,
      x.toNat+8 ≤ (AllocEntry.frameSp R).toNat ∨ (AllocEntry.frameSp R).toNat+48 ≤ x.toNat-8) :
    BfShape.BoundedSmallRepresentation (AllocWrapperCore.prepared R c).σ.mem lists := by
  have static (a n : Nat) (high : a+n ≤ DlHeap.heapStart) :
      bytesT (AllocWrapperCore.prepared R c).σ.mem a n = bytesT c.σ.mem a n :=
    prologue_read windows (Or.inl (by omega))
  apply repr.of_reads
  · intro s lo hi
    apply static
    rw [BfShape.slot_toNat s hi]
    change s ≤ 16 at hi
    simp only [DlHeap.heapStart,Layout.sym_bf_small_fl]; omega
  · intro s lo hi x hx
    exact prologue_read windows (by have := separate s lo hi x hx; omega)
  · intro s lo hi x hx
    rw [repr.physical.header_nat lo hi hx]
    apply prologue_read windows
    have := separate s lo hi x hx
    have := repr.physical.bounds s lo hi x hx
    omega
  · exact static _ _ (by decide)

def regs (R : Nat → BitVec 64) (hp : BitVec 64) :=
  AllocFinish.entryRegs (AllocEntry.frameSp R) (R 10) hp

def ready (log : List WEntry) (middle : Config) := AllocFinish.snapshot log middle

def threshold (c : Config) := word c Layout.sym_Caml_state + BitVec.ofNat 64 Layout.off_minor_heap_wsz

/-- Read transport through the real prologue, selected free-list log, and
header installation. All three logs are reflected into the same windows. -/
theorem initialized_read {R before middle hp log ws a n}
    (entered : AllocWrapperCore.Entered R before middle)
    (prefixLog : LogInW ws (AllocEntry.effect R ++ log))
    (header : ∀ v, LogInW ws [(hp.toNat,8,v)]) (outside : OutWRange ws a n) :
    bytesT (AllocAccount.initialized (AllocSuccess.completed (regs R hp) (ready log middle))
      (ready log middle)) a n = bytesT before.σ.mem a n := by
  change bytesT (writeLog (writeLog middle.σ.mem log) [(hp.toNat,8,_)]) a n = _
  rw [bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (header _) outside)]
  rw [entered.memory,← writeLog_append]
  exact bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows prefixLog outside)

theorem ready_read {R before middle log ws a n}
    (entered : AllocWrapperCore.Entered R before middle)
    (prefixLog : LogInW ws (AllocEntry.effect R ++ log)) (outside : OutWRange ws a n) :
    bytesT (ready log middle).σ.mem a n = bytesT before.σ.mem a n := by
  change bytesT (writeLog middle.σ.mem log) a n = _
  rw [entered.memory,← writeLog_append]
  exact bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows prefixLog outside)

theorem saved {R before middle log cell} (entered : AllocWrapperCore.Entered R before middle)
    (windows : AllocEntry.Windows R) (member : cell ∈ AllocEntry.saveCells)
    (outside : OutLRange log (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8) :
    word (ready log middle) (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1 := by
  change bytesT (writeLog middle.σ.mem log) _ 8 = _
  rw [entered.memory]
  exact AllocEntry.saved_after _ windows log cell member outside

def isBlack (hp : BitVec 64) (c : Config) := AllocSelect.isBlack (fun _ => hp) c

theorem color {R before middle log hp ws}
    (entered : AllocWrapperCore.Entered R before middle)
    (prefixLog : LogInW ws (AllocEntry.effect R ++ log))
    (phaseOut : OutWRange ws Layout.sym_caml_gc_phase 4)
    (sweepOut : OutWRange ws Layout.sym_caml_gc_sweep_hp 8) :
    AllocSelect.isBlack (regs R hp) (ready log middle) = isBlack hp before := by
  have phase : AllocSelect.phase (ready log middle) = AllocSelect.phase before := by
    simp only [AllocSelect.phase,read4_value]
    exact congrArg (fun v : BitVec 32 => v.signExtend 64) (ready_read entered prefixLog phaseOut)
  have sweep : AllocSelect.sweep (ready log middle) = AllocSelect.sweep before :=
    ready_read entered prefixLog sweepOut
  simp only [AllocSelect.isBlack,phase,sweep,isBlack,regs,AllocFinish.entryRegs,ite_false,show ¬(10 = 2) from by decide,show ¬(10 = 8) from by decide]

/-- Internal finish conditions produced from original accounting reads and
physical header/caller-bank separation. They are never an entry assumption. -/
theorem continuation {R before middle hp log}
    (entered : AllocWrapperCore.Entered R before middle) (windows : AllocEntry.Windows R)
    (headerWrite : WriteWindow hp 8)
    (stateRead : bytesT (AllocAccount.initialized (AllocSuccess.completed (regs R hp) (ready log middle))
      (ready log middle)) Layout.sym_Caml_state 8 = word before Layout.sym_Caml_state)
    (counterRead : bytesT (AllocAccount.initialized (AllocSuccess.completed (regs R hp) (ready log middle))
      (ready log middle)) Layout.sym_caml_allocated_words 8 = word before Layout.sym_caml_allocated_words)
    (thresholdRead : ReadWindow (threshold before) 8)
    (thresholdValue : bytesT (AllocAccount.initialized (AllocSuccess.completed (regs R hp) (ready log middle))
      (ready log middle)) (threshold before).toNat 8 = word before (threshold before).toNat)
    (noMajorSlice : (word before Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat ≤
      (word before (threshold before).toNat).toNat)
    (credit : (word before Layout.sym_caml_allocated_words).toNat+1+(R 10).toNat < 2^64)
    (freeOutside : ∀ cell ∈ AllocEntry.saveCells,
      OutLRange log (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8)
    (finishOutside : ∀ off ∈ AllocReturn.offsets,
      ((AllocEntry.frameSp R + BitVec.ofNat 64 off).toNat+8 ≤ hp.toNat ∨
        hp.toNat+8 ≤ (AllocEntry.frameSp R + BitVec.ofNat 64 off).toNat) ∧
      ((AllocEntry.frameSp R + BitVec.ofNat 64 off).toNat+8 ≤ Layout.sym_caml_allocated_words ∨
        Layout.sym_caml_allocated_words+8 ≤ (AllocEntry.frameSp R + BitVec.ofNat 64 off).toNat))
    (aligned : (R 1).toNat % 4 = 0) :
    AllocSuccess.Conditions (regs R hp) (ready log middle) := by
  let completed := AllocSuccess.completed (regs R hp) (ready log middle)
  have state : AllocAccount.state completed (ready log middle) = word before Layout.sym_Caml_state := stateRead
  have thresholdAddr : AllocAccount.thresholdAddr completed (ready log middle) = threshold before := by
    unfold AllocAccount.thresholdAddr threshold
    rw [state]
  have room : (AllocAccount.counted completed (ready log middle)).toNat ≤
      (bytesT (AllocAccount.initialized completed (ready log middle))
        (AllocAccount.thresholdAddr completed (ready log middle)).toNat 8).toNat := by
    rw [AllocAccount.counted,counterRead,thresholdAddr,thresholdValue]
    change ((word before Layout.sym_caml_allocated_words)+1#64+R 10).toNat ≤ _
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  refine ⟨⟨headerWrite,?_,room⟩,⟨?_,?_,?_⟩⟩
  · change ReadWindow (AllocAccount.thresholdAddr completed (ready log middle)) 8
    rw [thresholdAddr]; exact thresholdRead
  · intro off member
    change ReadWindow (AllocEntry.frameSp R + BitVec.ofNat 64 off) 8
    have saves : ∀ off ∈ AllocReturn.offsets, ∃ cell ∈ AllocEntry.saves, cell.2 = off := by decide
    obtain ⟨cell,hcell,rfl⟩ := saves off member
    exact (windows.saved cell hcell).read
  · intro off member
    exact ⟨(finishOutside off member).1,(finishOutside off member).2,True.intro⟩
  · change (AllocReturn.returnWord (AllocEntry.frameSp R) hp (ready log middle)).toNat % 4 = 0
    have returnWord : AllocReturn.returnWord (AllocEntry.frameSp R) hp (ready log middle) = R 1 :=
      saved (cell := (1,40)) entered windows (by decide) (freeOutside _ (by decide))
    rw [returnWord]; exact aligned

/-- The common finish writes only the allocated header and counter. -/
theorem finish_memory {R hp log extra} {middle freeState after : Config}
    (freeMemory : freeState.σ.mem = writeLog middle.σ.mem log)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) hp log middle after extra) :
    after.σ.mem = writeLog freeState.σ.mem
      (AllocAccount.effect (AllocSuccess.completed (regs R hp) (ready log middle)) (ready log middle)) := by
  rw [finished.memory,AllocFinish.effect,writeLog_append,← freeMemory]
  rfl

theorem finish_read {R hp log a n extra} {middle freeState after : Config}
    (freeMemory : freeState.σ.mem = writeLog middle.σ.mem log)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) hp log middle after extra)
    (headerApart : a+n ≤ hp.toNat ∨ hp.toNat+8 ≤ a)
    (counterApart : a+n ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words+8 ≤ a) :
    bytesT after.σ.mem a n = bytesT freeState.σ.mem a n := by
  rw [finish_memory freeMemory finished]
  exact bytesT_writeLog_out _ ⟨headerApart,counterApart,True.intro⟩

/-- Explicit selected ledgers, framed by the actual composed log. -/
theorem live {before after : Config} {log H}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (bounds : ∀ e ∈ H, DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ DlHeap.heapEnd)
    (outside : ∀ x, x < DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x → OutL log x) :
    LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x high owned
  rw [memory]
  rw [writeLog_out _ _ _ (outside x high owned)]

/-- Header installation preserves every remaining represented free cell.
Allocated separation is the selected physical fact; no ownership is inferred. -/
theorem finished_representation {R hp log extra lists} {middle freeState after : Config}
    (repr : BfShape.BoundedSmallRepresentation freeState.σ.mem lists)
    (apart : BestFitNext.AllocatedApart hp.toNat (R 10) lists)
    (headerHeap : DlHeap.heapStart ≤ hp.toNat)
    (freeMemory : freeState.σ.mem = writeLog middle.σ.mem log)
    (finished : AllocFinish.Post (AllocEntry.frameSp R) (R 10) hp log middle after extra) :
    BfShape.BoundedSmallRepresentation after.σ.mem lists := by
  have static (a n : Nat) (high : a+n ≤ DlHeap.heapStart)
      (counter : a+n ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words+8 ≤ a) :
      bytesT after.σ.mem a n = bytesT freeState.σ.mem a n :=
    finish_read freeMemory finished (Or.inl (by omega)) counter
  have small (s : Nat) (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (x : BitVec 64) (hx : x ∈ lists s) :
      bytesT after.σ.mem x.toNat 8 = bytesT freeState.σ.mem x.toNat 8 ∧
      bytesT after.σ.mem (x-8#64).toNat 8 = bytesT freeState.σ.mem (x-8#64).toNat 8 := by
    have sep := apart.separate s lo hi x hx
    have bounds := repr.physical.bounds s lo hi x hx
    have hn := repr.physical.header_nat lo hi hx
    constructor
    · apply finish_read freeMemory finished (by omega)
      exact Or.inr (by simp only [Layout.sym_caml_allocated_words,DlHeap.heapStart] at bounds ⊢; omega)
    · rw [hn]
      apply finish_read freeMemory finished (by omega)
      exact Or.inr (by simp only [Layout.sym_caml_allocated_words,DlHeap.heapStart] at bounds ⊢; omega)
  apply repr.of_reads
  · intro s lo hi
    apply static
    · rw [BfShape.slot_toNat s hi]
      change s ≤ 16 at hi
      simp only [DlHeap.heapStart,Layout.sym_bf_small_fl]; omega
    · rw [BfShape.slot_toNat s hi]
      exact Or.inr (by simp only [Layout.sym_caml_allocated_words,Layout.sym_bf_small_fl]; omega)
  · intro s lo hi x hx; exact (small s lo hi x hx).1
  · intro s lo hi x hx; exact (small s lo hi x hx).2
  · exact static _ _ (by decide) (by decide)

/-- Classify the exact returned wrapper log once for caller payloads. -/
theorem logWindows {R hp log before after extra ws P s pl cp top high offs}
    (post : AllocWrapperCore.Post R hp log before after extra)
    (inside : LogInW ws (AllocWrapperCore.effect R hp log before))
    (geometry : OCaml.Vm.Sim.StackGeometry P s before pl cp high)
    (kinds : ∀ w ∈ ws, OCaml.Vm.Sim.LogWindow P s before pl cp top high offs w)
    (topBound : top ≤ high) (fits : ∀ off ∈ offs, off+8 ≤ Layout.domainStateBytes) :
    OCaml.Vm.Sim.LogWindows (AllocWrapperCore.effect R hp log before) P s before pl cp top high offs :=
  ⟨geometry,⟨ws,inside,kinds⟩,topBound,fits⟩

end OCaml.Vm.Gc.AllocOriginal
