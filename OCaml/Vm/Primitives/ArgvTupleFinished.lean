import OCaml.Vm.Primitives.ArgvTupleAllocated
import OCaml.Vm.Primitives.AccessPlanObservation
import OCaml.Vm.Primitives.PairLayout
import OCaml.Vm.Gc.Readback

namespace OCaml.Vm.Primitives.ArgvTuple
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

def argvGlobal : BitVec 64 := BitVec.ofNat 64 Layout.sym_main_argv

def finishRegisters (R : Nat → BitVec 64) (roots blockYoung : BitVec 64) : Nat → BitVec 64
  | 2 => frameSp (R 2) | 8 => roots | 9 => DoubleAllocation.domainGlobal
  | 10 => tupleWord blockYoung | _ => 0

/-- The tuple initializer's stores: the result root slot, both fields, and
the restored local-roots pointer. -/
def tupleLog (sp tuple str argv domain roots : BitVec 64) : List WEntry :=
  [((sp + 8#64).toNat, 8, tuple)] ++ pairLog tuple str argv ++
    [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, roots)]

/-- Static windows and separation for the finishing stores and reloads. -/
structure FinishLayout (sp tuple str argv domain roots : BitVec 64) : Prop where
  stringSlot : ReadWindow sp 8
  resultSlot : WriteWindow (sp + 8#64) 8
  firstField : WriteWindow tuple 8
  secondField : WriteWindow (tuple + 8#64) 8
  argvRead : ReadWindow argvGlobal 8
  domainRead : ReadWindow DoubleAllocation.domainGlobal 8
  rootsWrite : WriteWindow (domain + BitVec.ofNat 64 Layout.off_local_roots) 8
  savedRa : ReadWindow (sp + 104#64) 8
  savedS0 : ReadWindow (sp + 96#64) 8
  savedS1 : ReadWindow (sp + 88#64) 8
  savedS2 : ReadWindow (sp + 80#64) 8
  resultOutsideTuple : OutLRange (pairLog tuple str argv) (sp + 8#64).toNat 8
  argvOutside : OutLRange ([((sp + 8#64).toNat, 8, tuple)] ++ pairLog tuple str argv) argvGlobal.toNat 8
  domainOutside : OutLRange ([((sp + 8#64).toNat, 8, tuple)] ++ pairLog tuple str argv)
    DoubleAllocation.domainGlobal.toNat 8
  savedOutside : ∀ k ∈ [80, 88, 96, 104], OutLRange (tupleLog sp tuple str argv domain roots)
    (sp + BitVec.ofNat 64 k).toNat 8
  image : ImageOutside (tupleLog sp tuple str argv domain roots)
  rootsOutsideFirst : OutLRange [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, roots)] tuple.toNat 8
  rootsOutsideSecond : OutLRange [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, roots)]
    (tuple.toNat + 8) 8

/-- Pins for a load chosen as the observation of a predicted memory. -/
theorem lpins8_of_view {m m' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {bs : List (BitVec 8)}
    (memory : m = m') (bytes : bs = read8 m' a) : LPins8 m a bs := by
  subst memory bytes; exact read8_pins _ _

def finishM2 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str : BitVec 64) :=
  writeLog m [((R 2 + 8#64).toNat, 8, R 10), ((R 10).toNat, 8, str)]

def finishM3 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str argv : BitVec 64) :=
  writeLog (finishM2 m R str) [((R 10 + 8#64).toNat, 8, argv)]

def finishM4 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str argv domain : BitVec 64) :=
  writeLog (finishM3 m R str argv) [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, R 8)]

/-- Scalar observations of the finishing block over a predicted memory: each
load reads the memory produced by the stores preceding it. -/
def finishLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64)
    (str argv domain : BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (R 2).toNat, read8 (finishM2 m R str) (R 2 + 8#64).toNat,
   read8 (finishM2 m R str) argvGlobal.toNat, read8 (finishM3 m R str argv) DoubleAllocation.domainGlobal.toNat,
   read8 (finishM3 m R str argv) (R 2 + 8#64).toNat,
   read8 (finishM4 m R str argv domain) (R 2 + 104#64).toNat,
   read8 (finishM4 m R str argv domain) (R 2 + 96#64).toNat,
   read8 (finishM4 m R str argv domain) (R 2 + 88#64).toNat,
   read8 (finishM4 m R str argv domain) (R 2 + 80#64).toNat]

theorem finish_access (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64)
    (str argv domain : BitVec 64)
    (v0 : bytesVal .ld ((finishLoads m R str argv domain).getD 0 []) = str)
    (v1 : bytesVal .ld ((finishLoads m R str argv domain).getD 1 []) = R 10)
    (v2 : bytesVal .ld ((finishLoads m R str argv domain).getD 2 []) = argv)
    (v3 : bytesVal .ld ((finishLoads m R str argv domain).getD 3 []) = domain)
    (hl : FinishLayout (R 2) (R 10) str argv domain (R 8))
    (domainReg : R 9 = DoubleAllocation.domainGlobal) :
    AccessPlan m (finish_input R) (finishLoads m R str argv domain) finish_body := by
  simp only [finishLoads, List.getD_cons_zero, List.getD_cons_succ] at v0 v1 v2 v3
  simp only [AccessPlan, finish_body]
  refine ⟨?_, ?_, ?_, ?_, True.intro, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro, True.intro⟩
  · apply hl.stringSlot.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · exact read8_pins _ _
  · apply hl.resultSlot.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
  · apply hl.firstField.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
  · apply hl.resultSlot.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM2 m R str)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.argvRead.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM2 m R str)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.secondField.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
  · apply hl.domainRead.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM3 m R str argv)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.resultSlot.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM3 m R str argv)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.rootsWrite.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
  · apply hl.savedRa.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM4 m R str argv domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.savedS0.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM4 m R str argv domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.savedS1.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM4 m R str argv domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.savedS2.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        argvGlobal, Layout.sym_main_argv, Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM4 m R str argv domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, writeLog, Layout.off_local_roots]
      · rfl


/-- Writes after the four native register saves, up to the tuple's return. -/
def afterSavedLog (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) : List WEntry :=
  (prepareLog R domain roots).drop 4 ++
    StringCopy.completeLog prepare_call.link (frameSp (R 2)) a len g domain young ++
    afterCopyLog R domain young blockYoung len

theorem allocatedLog_saved (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) :
    allocatedLog R domain roots young blockYoung a len g =
      savedLog R ++ afterSavedLog R domain roots young blockYoung a len g := by
  have drop : (prepareLog R domain roots).drop 4 = (prepareLog R domain roots).drop (savedLog R).length := rfl
  rw [afterSavedLog, drop, prepareLog, List.drop_left, allocatedLog, copiedLog, prepareLog]
  simp only [List.append_assoc]

/-- Inputs of the complete argv tuple construction. Beyond the allocation
stages, the caller supplies the static layout of the finishing stores and
reloads; every loaded value is recovered from the exact write logs. -/
structure FinishStageInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (bd be br : List (BitVec 8)) (a len : Nat) (g : Nat → BitVec 8)
    (young limit blockYoung argv : BitVec 64) (c : Config) : Prop
    extends AllocateStageInput live Dt DA R bd be br a len g young limit blockYoung c where
  layout : FinishLayout (frameSp (R 2)) (tupleWord blockYoung) (StringCopy.resultWord young len) argv
    (bytesVal .ld bd) (bytesVal .ld br)
  argvValue : word c argvGlobal.toNat = argv
  argvAllocated : OutLRange (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g)
    argvGlobal.toNat 8
  stringSlotOutside : OutLRange (SmallAllocation.constructorLog allocate_call.link 2#64 0#64
    (bytesVal .ld bd) blockYoung) (frameSp (R 2)).toNat 8
  savedTail : ∀ k ∈ [80, 88, 96, 104], OutLRange
    (afterSavedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g)
    (frameSp (R 2) + BitVec.ofNat 64 k).toNat 8
  stringOutsideTuple : ObjectOutside (tupleLog (frameSp (R 2)) (tupleWord blockYoung)
    (StringCopy.resultWord young len) argv (bytesVal .ld bd) (bytesVal .ld br))
    (StringCopy.resultWord young len).toNat (.bytes (List.replicate len 0))
  headerOutsideTuple : OutLRange (tupleLog (frameSp (R 2)) (tupleWord blockYoung)
    (StringCopy.resultWord young len) argv (bytesVal .ld bd) (bytesVal .ld br))
    (SmallAllocation.nurseryHeader blockYoung 2#64).toNat 8


/-- Two RAM-resident slots at distinct offsets of one frame do not overlap. -/
theorem frame_slots_apart {x : BitVec 64} {j k : Nat} (hj : j < 4096) (hk : k < 4096)
    (wj : ReadWindow (x + BitVec.ofNat 64 j) 8) (wk : ReadWindow (x + BitVec.ofNat 64 k) 8)
    (apart : j + 8 ≤ k ∨ k + 8 ≤ j) :
    (x + BitVec.ofNat 64 j).toNat + 8 ≤ (x + BitVec.ofNat 64 k).toNat ∨
      (x + BitVec.ofNat 64 k).toNat + 8 ≤ (x + BitVec.ofNat 64 j).toNat := by
  have lj := wj.lower; have uj := wj.upper; have lk := wk.lower; have uk := wk.upper
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega

/-- The four native register saves read back after all later writes. -/
theorem saved_readback {R : Nat → BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {tail : List WEntry}
    (w104 : ReadWindow (frameSp (R 2) + 104#64) 8) (w96 : ReadWindow (frameSp (R 2) + 96#64) 8)
    (w88 : ReadWindow (frameSp (R 2) + 88#64) 8) (w80 : ReadWindow (frameSp (R 2) + 80#64) 8)
    (outside : ∀ k ∈ [80, 88, 96, 104], OutLRange tail (frameSp (R 2) + BitVec.ofNat 64 k).toNat 8) :
    bytesT (writeLog m (savedLog R ++ tail)) (frameSp (R 2) + 104#64).toNat 8 = R 1 ∧
    bytesT (writeLog m (savedLog R ++ tail)) (frameSp (R 2) + 96#64).toNat 8 = R 8 ∧
    bytesT (writeLog m (savedLog R ++ tail)) (frameSp (R 2) + 88#64).toNat 8 = R 9 ∧
    bytesT (writeLog m (savedLog R ++ tail)) (frameSp (R 2) + 80#64).toNat 8 = R 18 := by
  have a := fun j k hj hk wj wk ap => frame_slots_apart (x := frameSp (R 2)) (j := j) (k := k) hj hk wj wk ap
  have s104_88 := a 104 88 (by decide) (by decide) w104 w88 (by decide)
  have s104_80 := a 104 80 (by decide) (by decide) w104 w80 (by decide)
  have s104_96 := a 104 96 (by decide) (by decide) w104 w96 (by decide)
  have s88_80 := a 88 80 (by decide) (by decide) w88 w80 (by decide)
  have s88_96 := a 88 96 (by decide) (by decide) w88 w96 (by decide)
  have s80_96 := a 80 96 (by decide) (by decide) w80 w96 (by decide)
  rw [writeLog_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesT_writeLog_out _ (outside 104 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 0 _ _ rfl
      ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, True.intro⟩
  · rw [bytesT_writeLog_out _ (outside 96 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 3 _ _ rfl True.intro
  · rw [bytesT_writeLog_out _ (outside 88 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 1 _ _ rfl ⟨by dsimp only; omega, by dsimp only; omega, True.intro⟩
  · rw [bytesT_writeLog_out _ (outside 80 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 2 _ _ rfl ⟨by dsimp only; omega, True.intro⟩


theorem frameSp_restore (x : BitVec 64) : frameSp x + 112#64 = x := by
  simp only [frameSp, BitVec.add_assoc]
  rw [show (-112#64 : BitVec 64) + 112#64 = 0#64 from by decide, BitVec.add_zero]

/-- The constructed pair is returned with both fields, the native frame and
callee-saved registers restored, and the copied executable name retained. -/
structure FinishStagePost (live : Nat → Prop) (R : Nat → BitVec 64)
    (domain roots young blockYoung argv : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (before after : Config) : Prop extends LeafInput (R 1) after where
  libraryGood : VsaOk live after
  pc : pcOf after = some (R 1)
  result : gpr after 10 = some (tupleWord blockYoung)
  stack : gpr after 2 = some (R 2)
  s0 : gpr after 8 = some (R 8)
  s1 : gpr after 9 = some (R 9)
  s2 : gpr after 18 = some (R 18)
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem
    (allocatedLog R domain roots young blockYoung a len g ++
      tupleLog (frameSp (R 2)) (tupleWord blockYoung) (StringCopy.resultWord young len) argv domain roots))
  stringObject : ∀ (pl : Place) (cp : ChanPlace) (bs : List UInt8), bs.length = len →
    (∀ i x, bs[i]? = some x → g (a + i) = BitVec.ofNat 8 x.toNat) →
    ObjAt after pl cp (StringCopy.resultWord young len).toNat (.bytes bs)
  header : HeaderOk (word after (SmallAllocation.nurseryHeader blockYoung 2#64).toNat) 2 0
  fields : word after (tupleWord blockYoung).toNat = StringCopy.resultWord young len ∧
    word after ((tupleWord blockYoung).toNat + 8) = argv
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ callerWrites → gpr after n = gpr before n

theorem argv_finish_stage {live Dt DA R bd be br a len g young limit blockYoung argv c}
    (h : FinishStageInput live Dt DA R bd be br a len g young limit blockYoung argv c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_argv) (fun d => d = c)
      (FinishStagePost live R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung argv a len g c) := by
  apply summary_bind (argv_allocate_stage h.toAllocateStageInput) (fun _ p => p.pc)
  intro alloc p
  have L := h.layout
  -- Values of the finishing block's loads, read from the predicted memory.
  have v0 : bytesVal .ld (read8 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br)
      young blockYoung a len g)) (frameSp (R 2)).toNat) = StringCopy.resultWord young len := by
    rw [read8_value, allocatedLog, afterCopyLog, ← List.append_assoc, writeLog_append,
      bytesT_writeLog_out _ h.stringSlotOutside, writeLog_append]
    exact word_writeLog _ _ _
  -- Abbreviations (kept as explicit terms so hypotheses match syntactically).
  have M0eq : Vsa.Densify.MemEqv alloc.σ.mem (writeLog c.σ.mem
      (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g)) := p.memory
  have v1 : bytesVal .ld (read8 (finishM2 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd)
      (bytesVal .ld br) young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung)
      (StringCopy.resultWord young len)) (frameSp (R 2) + 8#64).toNat) = tupleWord blockYoung := by
    rw [read8_value, finishM2]
    simp only [finishRegisters]
    rw [show ∀ x y : WEntry, [x, y] = [x] ++ [y] from fun _ _ => rfl, writeLog_append,
      bytesT_writeLog_out (log := [((tupleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _
        ⟨L.resultOutsideTuple.1, True.intro⟩]
    exact word_writeLog _ _ _
  have v2 : bytesVal .ld (read8 (finishM2 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd)
      (bytesVal .ld br) young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung)
      (StringCopy.resultWord young len)) argvGlobal.toNat) = argv := by
    rw [read8_value, finishM2]
    simp only [finishRegisters]
    rw [bytesT_writeLog_out (log := [((frameSp (R 2) + 8#64).toNat, 8, tupleWord blockYoung),
        ((tupleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _
        ⟨L.argvOutside.1, L.argvOutside.2.1, True.intro⟩,
      bytesT_writeLog_out _ h.argvAllocated]
    exact h.argvValue
  have v3 : bytesVal .ld (read8 (finishM3 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd)
      (bytesVal .ld br) young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung)
      (StringCopy.resultWord young len) argv) DoubleAllocation.domainGlobal.toNat) = bytesVal .ld bd := by
    rw [read8_value, finishM3, finishM2]
    simp only [finishRegisters]
    rw [bytesT_writeLog_out (log := [((tupleWord blockYoung + 8#64).toNat, 8, argv)]) _
        ⟨L.domainOutside.2.2.1, True.intro⟩,
      bytesT_writeLog_out (log := [((frameSp (R 2) + 8#64).toNat, 8, tupleWord blockYoung),
        ((tupleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _
        ⟨L.domainOutside.1, L.domainOutside.2.1, True.intro⟩]
    have small := h.small.domainAfterHeader
    rw [memoryView_mem, ← writeLog_append, beforeSmallLog, List.append_assoc] at small
    exact small
  have access := (finish_access _ (finishRegisters R (bytesVal .ld br) blockYoung)
    (StringCopy.resultWord young len) argv (bytesVal .ld bd) v0 v1 v2 v3 L rfl).observed_transport M0eq
  have regs : GHolds alloc.σ (finish_input (finishRegisters R (bytesVal .ld br) blockYoung)) :=
    ⟨p.stack, p.rootsReg, p.domainReg, p.result, True.intro⟩
  have hlog : finishLog (finishRegisters R (bytesVal .ld br) blockYoung)
      (finishLoads (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g))
        (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) argv (bytesVal .ld bd)) =
      tupleLog (frameSp (R 2)) (tupleWord blockYoung) (StringCopy.resultWord young len) argv
        (bytesVal .ld bd) (bytesVal .ld br) := by
    simp only [finishLog, finishLoads, List.getD_cons_zero, List.getD_cons_succ, finishRegisters]
    rw [v0, v1, v2, v3]
    rfl
  have saved := saved_readback (m := c.σ.mem) L.savedRa L.savedS0 L.savedS1 L.savedS2 h.savedTail
  rw [← allocatedLog_saved] at saved
  have M4 : finishM4 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g))
      (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) argv (bytesVal .ld bd) =
      writeLog (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g))
        (tupleLog (frameSp (R 2)) (tupleWord blockYoung) (StringCopy.resultWord young len) argv
          (bytesVal .ld bd) (bytesVal .ld br)) := by
    simp only [finishM4, finishM3, finishM2, tupleLog, pairLog, finishRegisters, ← writeLog_append,
      List.cons_append, List.nil_append, List.append_assoc]
  have slot := fun k (hk : k ∈ [80, 88, 96, 104]) =>
    bytesT_writeLog_out (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g))
      (L.savedOutside k hk)
  have v5 : bytesVal .ld ((finishLoads (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young
      blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) argv
      (bytesVal .ld bd)).getD 5 []) = R 1 := by
    simp only [finishLoads, List.getD_cons_zero, List.getD_cons_succ]
    rw [read8_value, M4]
    exact (slot 104 (by simp)).trans saved.1
  have F := finish_fast alloc (R 1) allocate_call.link (finishRegisters R (bytesVal .ld br) blockYoung) _
    p.toLeafInput h.aligned regs access (by rw [hlog]; exact L.image) v5
  apply F.weaken (fun _ eq => eq)
  intro after fin
  have v6 : bytesVal .ld (read8 (finishM4 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br)
      young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)
      argv (bytesVal .ld bd)) (frameSp (R 2) + 96#64).toNat) = R 8 := by
    rw [read8_value, M4]; exact (slot 96 (by simp)).trans saved.2.1
  have v7 : bytesVal .ld (read8 (finishM4 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br)
      young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)
      argv (bytesVal .ld bd)) (frameSp (R 2) + 88#64).toNat) = R 9 := by
    rw [read8_value, M4]; exact (slot 88 (by simp)).trans saved.2.2.1
  have v8 : bytesVal .ld (read8 (finishM4 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br)
      young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)
      argv (bytesVal .ld bd)) (frameSp (R 2) + 80#64).toNat) = R 18 := by
    rw [read8_value, M4]; exact (slot 80 (by simp)).trans saved.2.2.2
  have v4 : bytesVal .ld (read8 (finishM3 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br)
      young blockYoung a len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)
      argv) (frameSp (R 2) + 8#64).toNat) = tupleWord blockYoung := by
    rw [read8_value, finishM3, finishM2]
    simp only [finishRegisters]
    rw [bytesT_writeLog_out (log := [((tupleWord blockYoung + 8#64).toNat, 8, argv)]) _
        ⟨L.resultOutsideTuple.2.1, True.intro⟩,
      show ∀ x y : WEntry, [x, y] = [x] ++ [y] from fun _ _ => rfl, writeLog_append,
      bytesT_writeLog_out (log := [((tupleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _
        ⟨L.resultOutsideTuple.1, True.intro⟩]
    exact word_writeLog _ _ _
  have lookup := fun n v (e : lookupG n (finish_regs (finishRegisters R (bytesVal .ld br) blockYoung)
      (finishLoads (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g))
        (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) argv
        (bytesVal .ld bd))) = some v) => gholds_lookup _ fin.regs e
  have finMem : after.σ.mem = writeLog alloc.σ.mem (tupleLog (frameSp (R 2)) (tupleWord blockYoung)
      (StringCopy.resultWord young len) argv (bytesVal .ld bd) (bytesVal .ld br)) := by
    rw [fin.memory, hlog]
  have raReg : gpr after 1 = some (R 1) := by rw [← v5]; exact lookup 1 _ rfl
  have resultReg : gpr after 10 = some (tupleWord blockYoung) := by rw [← v4]; exact lookup 10 _ rfl
  have s0Reg : gpr after 8 = some (R 8) := by rw [← v6]; exact lookup 8 _ rfl
  have s1Reg : gpr after 9 = some (R 9) := by rw [← v7]; exact lookup 9 _ rfl
  have s2Reg : gpr after 18 = some (R 18) := by rw [← v8]; exact lookup 18 _ rfl
  have spReg : gpr after 2 = some (R 2) := by rw [← frameSp_restore (R 2)]; exact lookup 2 _ rfl
  refine ⟨⟨fin.good, fin.image, fin.minstret, raReg, h.aligned, fin.tick⟩,
    fin.vsaOk p.libraryGood (by decide) (by simp [finish_regs, keysG]), fin.pc, resultReg, spReg,
    s0Reg, s1Reg, s2Reg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finMem, writeLog_append]
    exact M0eq.writeLog _
  · intro pl cp bs length source
    apply object_copied (p.stringObject pl cp bs length source)
      (copied_of_writeLog finMem h.stringOutsideTuple.header)
    apply copied_of_writeLog finMem
    simpa only [Obj.wosize, List.length_replicate, length] using h.stringOutsideTuple.payload
  · change HeaderOk (bytesT after.σ.mem _ 8) 2 0
    rw [finMem, bytesT_writeLog_out _ h.headerOutsideTuple]
    exact p.header
  · exact pairLog_fields finMem L.firstField L.rootsOutsideFirst L.rootsOutsideSecond
  · exact (by simp only [Vsa.Machine.output, fin.output] : Vsa.Machine.output after.σ =
      Vsa.Machine.output alloc.σ).trans p.output
  · intro n lo hi unwritten
    apply (fin.toEffectPost.gpr_frame (by decide) n lo hi (by
      simp only [callerWrites, List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢; omega)).trans
    exact p.registers n lo hi unwritten

end OCaml.Vm.Primitives.ArgvTuple
