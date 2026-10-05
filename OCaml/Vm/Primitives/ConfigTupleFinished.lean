import OCaml.Vm.Primitives.ConfigTupleAllocated
import OCaml.Vm.Primitives.ArgvTupleFinished

namespace OCaml.Vm.Primitives.ConfigTuple
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ArgvTuple (frameSp memoryView memoryView_mem callerWrites lpins8_of_view frame_slots_apart
  frameSp_restore)

def finishRegisters (R : Nat → BitVec 64) (roots blockYoung : BitVec 64) : Nat → BitVec 64
  | 2 => frameSp (R 2) | 8 => 1#64 | 9 => roots | 10 => tripleWord blockYoung
  | 18 => DoubleAllocation.domainGlobal | _ => 0

/-- The triple initializer's stores: the result root slot, the three fields
(OS type, `Val_long 64`, `Val_false`), and the restored local-roots pointer. -/
def tripleLog (sp triple str domain roots : BitVec 64) : List WEntry :=
  [(sp.toNat, 8, triple), (triple.toNat, 8, str), ((triple + 8#64).toNat, 8, 129#64),
   ((triple + 16#64).toNat, 8, 1#64),
   ((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, roots)]

def rootsEntry (domain roots : BitVec 64) : List WEntry :=
  [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, roots)]

/-- Static windows and separation for the finishing stores and reloads. -/
structure FinishLayout (sp triple str domain roots : BitVec 64) : Prop where
  stringSlot : ReadWindow (sp + 8#64) 8
  resultSlot : WriteWindow sp 8
  firstField : WriteWindow triple 8
  secondField : WriteWindow (triple + 8#64) 8
  thirdField : WriteWindow (triple + 16#64) 8
  domainRead : ReadWindow DoubleAllocation.domainGlobal 8
  rootsWrite : WriteWindow (domain + BitVec.ofNat 64 Layout.off_local_roots) 8
  savedRa : ReadWindow (sp + 104#64) 8
  savedS0 : ReadWindow (sp + 96#64) 8
  savedS1 : ReadWindow (sp + 88#64) 8
  savedS2 : ReadWindow (sp + 80#64) 8
  resultOutsideFields : OutLRange [(triple.toNat, 8, str), ((triple + 8#64).toNat, 8, 129#64),
    ((triple + 16#64).toNat, 8, 1#64)] sp.toNat 8
  domainOutside : OutLRange ((tripleLog sp triple str domain roots).take 4) DoubleAllocation.domainGlobal.toNat 8
  savedOutside : ∀ k ∈ [80, 88, 96, 104], OutLRange (tripleLog sp triple str domain roots)
    (sp + BitVec.ofNat 64 k).toNat 8
  rootsOutsideFields : ∀ k ∈ [0, 8, 16], OutLRange (rootsEntry domain roots) (triple.toNat + k) 8
  image : ImageOutside (tripleLog sp triple str domain roots)

def finishM2 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str : BitVec 64) :=
  writeLog m [((R 2).toNat, 8, R 10), ((R 10).toNat, 8, str)]

def finishM3 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str : BitVec 64) :=
  writeLog (finishM2 m R str) [((R 10 + 8#64).toNat, 8, 129#64)]

def finishM4 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str : BitVec 64) :=
  writeLog (finishM3 m R str) [((R 10 + 16#64).toNat, 8, R 8)]

def finishM5 (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) (str domain : BitVec 64) :=
  writeLog (finishM4 m R str) [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, R 9)]

/-- Scalar observations of the finishing block over a predicted memory: each
load reads the memory produced by the stores preceding it. -/
def finishLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64)
    (str domain : BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (R 2 + 8#64).toNat, read8 (finishM2 m R str) (R 2).toNat,
   read8 (finishM3 m R str) (R 2).toNat,
   read8 (finishM4 m R str) DoubleAllocation.domainGlobal.toNat,
   read8 (finishM4 m R str) (R 2).toNat,
   read8 (finishM5 m R str domain) (R 2 + 104#64).toNat,
   read8 (finishM5 m R str domain) (R 2 + 96#64).toNat,
   read8 (finishM5 m R str domain) (R 2 + 88#64).toNat,
   read8 (finishM5 m R str domain) (R 2 + 80#64).toNat]

theorem finish_access (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64)
    (str domain : BitVec 64)
    (v0 : bytesVal .ld ((finishLoads m R str domain).getD 0 []) = str)
    (v1 : bytesVal .ld ((finishLoads m R str domain).getD 1 []) = R 10)
    (v2 : bytesVal .ld ((finishLoads m R str domain).getD 2 []) = R 10)
    (v3 : bytesVal .ld ((finishLoads m R str domain).getD 3 []) = domain)
    (hl : FinishLayout (R 2) (R 10) str domain (R 9))
    (domainReg : R 18 = DoubleAllocation.domainGlobal) :
    AccessPlan m (finish_input R) (finishLoads m R str domain) finish_body := by
  simp only [finishLoads, List.getD_cons_zero, List.getD_cons_succ] at v0 v1 v2 v3
  simp only [AccessPlan, finish_body]
  refine ⟨?_, ?_, True.intro, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro, True.intro⟩
  · apply hl.stringSlot.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · exact read8_pins _ _
  · apply hl.resultSlot.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
  · apply hl.firstField.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
  · apply hl.resultSlot.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM2 m R str)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.secondField.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
  · apply hl.resultSlot.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM3 m R str)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.thirdField.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
  · apply hl.domainRead.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM4 m R str)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.resultSlot.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM4 m R str)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.rootsWrite.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
  · apply hl.savedRa.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM5 m R str domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.savedS0.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM5 m R str domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.savedS1.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM5 m R str domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl
  · apply hl.savedS2.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add,
        Layout.off_local_roots]
    · apply lpins8_of_view (m' := finishM5 m R str domain)
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, finish_input, srcVal, lookupG, eraseG, imm20Of, finishLoads,
        v0, v1, v2, v3, domainReg, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
        simp [finishM2, finishM3, finishM4, finishM5, writeLog, Layout.off_local_roots]
      · rfl


/-- Writes after the four native register saves, up to the triple's return. -/
def afterSavedLog (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (len : Nat) (g : Nat → BitVec 8) : List WEntry :=
  (prepareLog R domain roots).drop 4 ++
    StringCopy.completeLog prepare_call.link (frameSp (R 2)) osTypeAddress.toNat len g domain young ++
    afterCopyLog R domain young blockYoung len

theorem allocatedLog_saved (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (len : Nat) (g : Nat → BitVec 8) :
    allocatedLog R domain roots young blockYoung len g =
      savedLog R ++ afterSavedLog R domain roots young blockYoung len g := by
  have drop : (prepareLog R domain roots).drop 4 = (prepareLog R domain roots).drop (savedLog R).length := rfl
  rw [afterSavedLog, drop, prepareLog, List.drop_left, allocatedLog, copiedLog, prepareLog]
  simp only [List.append_assoc]

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
  have s96_80 := a 96 80 (by decide) (by decide) w96 w80 (by decide)
  have s96_88 := a 96 88 (by decide) (by decide) w96 w88 (by decide)
  have s80_88 := a 80 88 (by decide) (by decide) w80 w88 (by decide)
  rw [writeLog_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesT_writeLog_out _ (outside 104 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 0 _ _ rfl
      ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, True.intro⟩
  · rw [bytesT_writeLog_out _ (outside 96 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 1 _ _ rfl ⟨by dsimp only; omega, by dsimp only; omega, True.intro⟩
  · rw [bytesT_writeLog_out _ (outside 88 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 3 _ _ rfl True.intro
  · rw [bytesT_writeLog_out _ (outside 80 (by simp))]
    exact Gc.word_writeLog_at m (savedLog R) 2 _ _ rfl ⟨by dsimp only; omega, True.intro⟩

/-- Inputs of the complete configuration-triple construction. -/
structure FinishStageInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (bd br : List (BitVec 8)) (len : Nat) (g : Nat → BitVec 8)
    (young limit blockYoung : BitVec 64) (c : Config) : Prop
    extends AllocateStageInput live Dt DA R bd br len g young limit blockYoung c where
  layout : FinishLayout (frameSp (R 2)) (tripleWord blockYoung) (StringCopy.resultWord young len)
    (bytesVal .ld bd) (bytesVal .ld br)
  stringSlotOutside : OutLRange (SmallAllocation.constructorLog allocate_call.link 3#64 0#64
    (bytesVal .ld bd) blockYoung) (frameSp (R 2) + 8#64).toNat 8
  savedTail : ∀ k ∈ [80, 88, 96, 104], OutLRange
    (afterSavedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)
    (frameSp (R 2) + BitVec.ofNat 64 k).toNat 8
  stringOutsideTriple : ObjectOutside (tripleLog (frameSp (R 2)) (tripleWord blockYoung)
    (StringCopy.resultWord young len) (bytesVal .ld bd) (bytesVal .ld br))
    (StringCopy.resultWord young len).toNat (.bytes (List.replicate len 0))
  headerOutsideTriple : OutLRange (tripleLog (frameSp (R 2)) (tripleWord blockYoung)
    (StringCopy.resultWord young len) (bytesVal .ld bd) (bytesVal .ld br))
    (SmallAllocation.nurseryHeader blockYoung 3#64).toNat 8

/-- The constructed triple is returned with its fields, the native frame and
callee-saved registers restored, and the copied OS type retained. -/
structure FinishStagePost (live : Nat → Prop) (R : Nat → BitVec 64)
    (domain roots young blockYoung : BitVec 64) (len : Nat) (g : Nat → BitVec 8)
    (before after : Config) : Prop extends LeafInput (R 1) after where
  libraryGood : VsaOk live after
  pc : pcOf after = some (R 1)
  result : gpr after 10 = some (tripleWord blockYoung)
  stack : gpr after 2 = some (R 2)
  s0 : gpr after 8 = some (R 8)
  s1 : gpr after 9 = some (R 9)
  s2 : gpr after 18 = some (R 18)
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem
    (allocatedLog R domain roots young blockYoung len g ++
      tripleLog (frameSp (R 2)) (tripleWord blockYoung) (StringCopy.resultWord young len) domain roots))
  stringObject : ∀ (pl : Place) (cp : ChanPlace) (bs : List UInt8), bs.length = len →
    (∀ i x, bs[i]? = some x → g (osTypeAddress.toNat + i) = BitVec.ofNat 8 x.toNat) →
    ObjAt after pl cp (StringCopy.resultWord young len).toNat (.bytes bs)
  header : HeaderOk (word after (SmallAllocation.nurseryHeader blockYoung 3#64).toNat) 3 0
  field0 : word after (tripleWord blockYoung).toNat = StringCopy.resultWord young len
  field1 : word after ((tripleWord blockYoung).toNat + 8) = 129#64
  field2 : word after ((tripleWord blockYoung).toNat + 16) = 1#64
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ callerWrites → gpr after n = gpr before n

theorem triple_addresses {triple : BitVec 64} (w0 : WriteWindow triple 8) (w2 : WriteWindow (triple + 16#64) 8) :
    (triple + 8#64).toNat = triple.toNat + 8 ∧ (triple + 16#64).toNat = triple.toNat + 16 := by
  have l0 := w0.lower; have u0 := w0.upper; have l2 := w2.lower; have u2 := w2.upper
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega

theorem config_finish_stage {live Dt DA R bd br len g young limit blockYoung c}
    (h : FinishStageInput live Dt DA R bd br len g young limit blockYoung c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_config) (fun d => d = c)
      (FinishStagePost live R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g c) := by
  apply summary_bind (config_allocate_stage h.toAllocateStageInput) (fun _ p => p.pc)
  intro alloc p
  have L := h.layout
  have M0eq : Vsa.Densify.MemEqv alloc.σ.mem (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) := p.memory
  have v0 : bytesVal .ld (read8 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (frameSp (R 2) + 8#64).toNat) = (StringCopy.resultWord young len) := by
    rw [read8_value, allocatedLog, afterCopyLog, ← List.append_assoc, writeLog_append,
      bytesT_writeLog_out _ h.stringSlotOutside, writeLog_append]
    exact word_writeLog _ _ _
  have v1 : bytesVal .ld (read8 (finishM2 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)) (frameSp (R 2)).toNat) = tripleWord blockYoung := by
    rw [read8_value, finishM2]
    simp only [finishRegisters]
    rw [show ∀ x y : WEntry, [x, y] = [x] ++ [y] from fun _ _ => rfl, writeLog_append,
      bytesT_writeLog_out (log := [((tripleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _ ⟨L.resultOutsideFields.1, True.intro⟩]
    exact word_writeLog _ _ _
  have v2 : bytesVal .ld (read8 (finishM3 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)) (frameSp (R 2)).toNat) = tripleWord blockYoung := by
    rw [read8_value, finishM3, finishM2]
    simp only [finishRegisters]
    rw [bytesT_writeLog_out (log := [((tripleWord blockYoung + 8#64).toNat, 8, 129#64)]) _ ⟨L.resultOutsideFields.2.1, True.intro⟩,
      show ∀ x y : WEntry, [x, y] = [x] ++ [y] from fun _ _ => rfl, writeLog_append,
      bytesT_writeLog_out (log := [((tripleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _ ⟨L.resultOutsideFields.1, True.intro⟩]
    exact word_writeLog _ _ _
  have v3 : bytesVal .ld (read8 (finishM4 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)) DoubleAllocation.domainGlobal.toNat) = bytesVal .ld bd := by
    rw [read8_value, finishM4, finishM3, finishM2]
    simp only [finishRegisters]
    rw [bytesT_writeLog_out (log := [((tripleWord blockYoung + 16#64).toNat, 8, 1#64)]) _ ⟨L.domainOutside.2.2.2.1, True.intro⟩,
      bytesT_writeLog_out (log := [((tripleWord blockYoung + 8#64).toNat, 8, 129#64)]) _ ⟨L.domainOutside.2.2.1, True.intro⟩,
      bytesT_writeLog_out (log := [((frameSp (R 2)).toNat, 8, tripleWord blockYoung), ((tripleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _ ⟨L.domainOutside.1, L.domainOutside.2.1, True.intro⟩]
    have small := h.small.domainAfterHeader
    rw [memoryView_mem, ← writeLog_append, beforeSmallLog, List.append_assoc] at small
    exact small
  have v4 : bytesVal .ld (read8 (finishM4 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len)) (frameSp (R 2)).toNat) = tripleWord blockYoung := by
    rw [read8_value, finishM4, finishM3, finishM2]
    simp only [finishRegisters]
    rw [bytesT_writeLog_out (log := [((tripleWord blockYoung + 16#64).toNat, 8, 1#64)]) _ ⟨L.resultOutsideFields.2.2.1, True.intro⟩,
      bytesT_writeLog_out (log := [((tripleWord blockYoung + 8#64).toNat, 8, 129#64)]) _ ⟨L.resultOutsideFields.2.1, True.intro⟩,
      show ∀ x y : WEntry, [x, y] = [x] ++ [y] from fun _ _ => rfl, writeLog_append,
      bytesT_writeLog_out (log := [((tripleWord blockYoung).toNat, 8, StringCopy.resultWord young len)]) _ ⟨L.resultOutsideFields.1, True.intro⟩]
    exact word_writeLog _ _ _
  have access := (finish_access _ (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd) v0 v1 v2 v3 L rfl).observed_transport M0eq
  have regs : GHolds alloc.σ (finish_input (finishRegisters R (bytesVal .ld br) blockYoung)) :=
    ⟨p.stack, p.unitReg, p.rootsReg, p.result, p.domainReg, True.intro⟩
  have hlog : finishLog (finishRegisters R (bytesVal .ld br) blockYoung) (finishLoads (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd)) =
      tripleLog (frameSp (R 2)) (tripleWord blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd) (bytesVal .ld br) := by
    simp only [finishLog, finishLoads, List.getD_cons_zero, List.getD_cons_succ, finishRegisters]
    rw [v0, v1, v2, v3]
    rfl
  have saved := saved_readback (m := c.σ.mem) L.savedRa L.savedS0 L.savedS1 L.savedS2 h.savedTail
  rw [← allocatedLog_saved] at saved
  have M5 : finishM5 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd) =
      writeLog (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (tripleLog (frameSp (R 2)) (tripleWord blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd) (bytesVal .ld br)) := by
    simp only [finishM5, finishM4, finishM3, finishM2, tripleLog, finishRegisters, ← writeLog_append,
      List.cons_append, List.nil_append, List.append_assoc]
  have slot := fun k (hk : k ∈ [80, 88, 96, 104]) => bytesT_writeLog_out (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (L.savedOutside k hk)
  have v5 : bytesVal .ld ((finishLoads (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd)).getD 5 []) = R 1 := by
    simp only [finishLoads, List.getD_cons_zero, List.getD_cons_succ]
    rw [read8_value, M5]
    exact (slot 104 (by simp)).trans saved.1
  have v6 : bytesVal .ld (read8 (finishM5 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd)) (frameSp (R 2) + 96#64).toNat) = R 8 := by
    rw [read8_value, M5]; exact (slot 96 (by simp)).trans saved.2.1
  have v7 : bytesVal .ld (read8 (finishM5 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd)) (frameSp (R 2) + 88#64).toNat) = R 9 := by
    rw [read8_value, M5]; exact (slot 88 (by simp)).trans saved.2.2.1
  have v8 : bytesVal .ld (read8 (finishM5 (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd)) (frameSp (R 2) + 80#64).toNat) = R 18 := by
    rw [read8_value, M5]; exact (slot 80 (by simp)).trans saved.2.2.2
  have F := finish_fast alloc (R 1) allocate_call.link (finishRegisters R (bytesVal .ld br) blockYoung) _
    p.toLeafInput h.aligned regs access (by rw [hlog]; exact L.image) v5
  apply F.weaken (fun _ eq => eq)
  intro after fin
  have lookup := fun n v (e : lookupG n (finish_regs (finishRegisters R (bytesVal .ld br) blockYoung)
      (finishLoads (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung len g)) (finishRegisters R (bytesVal .ld br) blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd))) = some v) => gholds_lookup _ fin.regs e
  have finMem : after.σ.mem = writeLog alloc.σ.mem
      (tripleLog (frameSp (R 2)) (tripleWord blockYoung) (StringCopy.resultWord young len) (bytesVal .ld bd) (bytesVal .ld br)) := by
    rw [fin.memory, hlog]
  have raReg : gpr after 1 = some (R 1) := by rw [← v5]; exact lookup 1 _ rfl
  have resultReg : gpr after 10 = some (tripleWord blockYoung) := by rw [← v4]; exact lookup 10 _ rfl
  have s0Reg : gpr after 8 = some (R 8) := by rw [← v6]; exact lookup 8 _ rfl
  have s1Reg : gpr after 9 = some (R 9) := by rw [← v7]; exact lookup 9 _ rfl
  have s2Reg : gpr after 18 = some (R 18) := by rw [← v8]; exact lookup 18 _ rfl
  have spReg : gpr after 2 = some (R 2) := by rw [← frameSp_restore (R 2)]; exact lookup 2 _ rfl
  have addr := triple_addresses L.firstField L.thirdField
  have r0 := L.rootsOutsideFields 0 (by simp)
  have r8 := L.rootsOutsideFields 8 (by simp)
  have r16 := L.rootsOutsideFields 16 (by simp)
  simp only [rootsEntry, Nat.add_zero] at r0 r8 r16
  refine ⟨⟨fin.good, fin.image, fin.minstret, raReg, h.aligned, fin.tick⟩,
    fin.vsaOk p.libraryGood (by decide) (by simp [finish_regs, keysG]), fin.pc, resultReg, spReg,
    s0Reg, s1Reg, s2Reg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finMem, writeLog_append]
    exact M0eq.writeLog _
  · intro pl cp bs length source
    apply object_copied (p.stringObject pl cp bs length source)
      (copied_of_writeLog finMem h.stringOutsideTriple.header)
    apply copied_of_writeLog finMem
    simpa only [Obj.wosize, List.length_replicate, length] using h.stringOutsideTriple.payload
  · change HeaderOk (bytesT after.σ.mem _ 8) 3 0
    rw [finMem, bytesT_writeLog_out _ h.headerOutsideTriple]
    exact p.header
  · change bytesT after.σ.mem _ 8 = _
    rw [finMem]
    exact Gc.word_writeLog_at _ _ 1 _ _ rfl
      ⟨by dsimp only; omega, by dsimp only; omega, r0.1, True.intro⟩
  · change bytesT after.σ.mem _ 8 = _
    rw [finMem, ← addr.1]
    refine Gc.word_writeLog_at _ _ 2 _ _ rfl ⟨by dsimp only; omega, ?_, True.intro⟩
    rw [addr.1]; exact r8.1
  · change bytesT after.σ.mem _ 8 = _
    rw [finMem, ← addr.2]
    refine Gc.word_writeLog_at _ _ 3 _ _ rfl ⟨?_, True.intro⟩
    rw [addr.2]; exact r16.1
  · exact (by simp only [Vsa.Machine.output, fin.output] : Vsa.Machine.output after.σ =
      Vsa.Machine.output alloc.σ).trans p.output
  · intro n lo hi unwritten
    apply (fin.toEffectPost.gpr_frame (by decide) n lo hi (by
      simp only [callerWrites, List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢; omega)).trans
    exact p.registers n lo hi unwritten

end OCaml.Vm.Primitives.ConfigTuple
