import OCaml.Vm.Sim.ArgvLogWindows
import OCaml.Vm.Sim.ConfigInput

/-!
# `caml_sys_get_argv`'s stage inputs at the callee entry

The argv instance of `ConfigInput`: the generated stage contracts
(`ArgvTupleCopied`, `…Allocated`, `…Finished`) take their memory accesses and
layout as inputs; this file supplies them from `StringAllocEntry` with a
40-byte nursery block (`AllocNumbers … 40`). The copy's source is the
executable name (`ExeNamePlaced`), loaded through `caml_exe_name`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ArgvTuple
  LeanRV64DExecutable
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Memcpy

/-- `caml_exe_name`'s address, the prepare block's second load. -/
def exeNameGlobal : BitVec 64 := BitVec.ofNat 64 Layout.sym_caml_exe_name

/-- The prepare block's three loads: the domain pointer, `caml_exe_name` and
the old `local_roots`, all after the four register saves. -/
def argvPrepareLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 (writeLog m (savedLog R)) DoubleAllocation.domainGlobal.toNat,
   read8 (writeLog m (savedLog R)) exeNameGlobal.toNat,
   read8 (writeLog m (savedLog R))
     (bytesVal .ld (read8 (writeLog m (savedLog R)) DoubleAllocation.domainGlobal.toNat) + 288#64).toNat]

theorem argv_prepare_access (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64)
    (hl : PrepareLayout R (bytesVal .ld ((argvPrepareLoads m R).getD 0 [])))
    (exeRead : ReadWindow exeNameGlobal 8) :
    AccessPlan m (prepare_input R) (argvPrepareLoads m R) prepare_body := by
  have s80 := hl.saves 80 (by simp)
  have s88 := hl.saves 88 (by simp)
  have s96 := hl.saves 96 (by simp)
  have s104 := hl.saves 104 (by simp)
  have t0 := hl.slots 0 (by simp)
  have t8 := hl.slots 8 (by simp)
  have t16 := hl.slots 16 (by simp)
  have t24 := hl.slots 24 (by simp)
  have t32 := hl.slots 32 (by simp)
  have t40 := hl.slots 40 (by simp)
  have t48 := hl.slots 48 (by simp)
  have rw' := hl.rootsWrite
  simp only [argvPrepareLoads, List.getD_cons_zero] at rw'
  simp only [AccessPlan, prepare_body]
  refine ⟨True.intro, ?_, ?_, ?_, ?_, True.intro, True.intro, ?_, True.intro, ?_, True.intro, ?_, True.intro, ?_,
    True.intro, True.intro, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · apply s104.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply s88.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply s80.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply s96.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply hl.domainRead.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
    · apply lpins8_of_view (m' := writeLog m (savedLog R))
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, savedLog, writeLog, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
      · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply exeRead.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, exeNameGlobal, Layout.sym_caml_exe_name, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
    · apply lpins8_of_view (m' := writeLog m (savedLog R))
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, savedLog, writeLog, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
      · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, exeNameGlobal, Layout.sym_caml_exe_name, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply rw'.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
    · apply lpins8_of_view (m' := writeLog m (savedLog R))
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, savedLog, writeLog, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
      · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply rw'.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t0.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t8.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t32.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t48.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t16.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t24.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t40.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, argvPrepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]

/-- A word apart from the native frame and from `local_roots` misses the
prepare stores. -/
theorem argv_prepare_out {N D x : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (h2 : R 2 = BitVec.ofNat 64 N)
    (roots' : x + 8 ≤ D + 288 ∨ D + 296 ≤ x) (frame : x + 8 ≤ N - 112 ∨ N ≤ x) :
    OutLRange (prepareLog R (BitVec.ofNat 64 D) roots) x 8 := by
  simp only [prepareLog, savedLog, frameSp, h2, OutLRange, List.cons_append, List.nil_append,
    Layout.off_local_roots, frameSp_ofNat (N := N) (by omega) (by omega), ← BitVec.ofNat_add,
    BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem argvBlockYoung_eq (Y : Nat) (h : 16 ≤ Y) (h' : Y < 2 ^ 64) :
    StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64 = BitVec.ofNat 64 (Y - 16) := by
  rw [progExeName_length, resultWord_eq (len := 5) span5 (Y := Y) (by omega) h']
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_sub_small (by omega) (by omega),
    show Y - 8 - 8 = Y - 16 by omega]

theorem argvResultWord_eq (Y : Nat) (h : 16 ≤ Y) (h' : Y < 2 ^ 64) :
    StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length = BitVec.ofNat 64 (Y - 8) := by
  rw [progExeName_length]; exact resultWord_eq (len := 5) span5 (by omega) h'

theorem smallHeader2 (Y : Nat) (h : 40 ≤ Y) (h' : Y < 2 ^ 64) :
    SmallAllocation.nurseryHeader (BitVec.ofNat 64 (Y - 16)) 2#64 = BitVec.ofNat 64 (Y - 40) := by
  simp only [SmallAllocation.nurseryHeader, shift2]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem tupleWord_eq (Y : Nat) (h : 40 ≤ Y) (h' : Y < 2 ^ 64) :
    tupleWord (BitVec.ofNat 64 (Y - 16)) = BitVec.ofNat 64 (Y - 32) := by
  simp only [tupleWord]
  rw [smallHeader2 Y h h', show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_add_small]
  congr 1; omega

/-- **The pair's nursery inputs** on the memory after the string copy. -/
theorem argv_small {c : Config} {N D Y Lm a : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    {g : Nat → BitVec 8} (nums : AllocNumbers N D Y Lm 40) (h2 : R 2 = BitVec.ofNat 64 N)
    (wD : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (wL : word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm) :
    SmallAllocation.NurseryMemory allocate_call.link 2#64 0#64 (BitVec.ofNat 64 D)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) (BitVec.ofNat 64 Lm)
      (memoryView c (writeLog c.σ.mem
        (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g))) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have F := frameSp_eq h2 (by omega) (by omega)
  have ys := youngSlot_eq D (by omega)
  have ls := limitSlot_eq D
  have gd : DoubleAllocation.domainGlobal.toNat = Layout.sym_Caml_state := rfl
  have cs : Layout.sym_Caml_state = 0x80064d08 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have inside := argv_beforeSmallLog_in (R := R) (roots := roots) (g := g) (a := a) (Y := Y) (D := D) (N := N)
    (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have out : ∀ x, (x + 8 ≤ N - 152 ∨ N ≤ x) → (x + 8 ≤ Y - 40 ∨ Y ≤ x) → (x + 8 ≤ D + 8 ∨ D + 16 ≤ x) →
      (x + 8 ≤ D + 288 ∨ D + 296 ≤ x) →
      OutLRange (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g) x 8 :=
    fun x a1 a2 a3 a4 => outLRange_of_windows inside (by
      simp only [allocWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega)
  have BY := argvBlockYoung_eq Y (by omega) (by omega)
  have SH := smallHeader2 Y (by omega) (by omega)
  rw [BY]
  have wv : ∀ x, OutLRange (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g) x 8 →
      word (memoryView c (writeLog c.σ.mem
        (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g))) x = word c x :=
    fun x h => view_word h
  refine { domainValue := ?_, youngValue := ?_, limitValue := ?_, youngWrite := ?_, limitRead := ?_,
           headerWrite := ?_, room := ?_, reserveImage := ?_, initializeImage := ?_, domainAfterHeader := ?_,
           youngAfterHeader := ?_ }
  · rw [gd, wv _ (out _ (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega)), wD]
  · change bytesT (writeLog c.σ.mem _) _ 8 = _
    rw [argv_beforeSmallLog_split, word_last_store]
    · rw [progExeName_length, span5]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]; omega
    · rw [ys, nat _ (by omega)]
      simp only [StringAllocation.initializationLog, StringAllocation.reservedRegisters, progExeName_length,
        nurseryHeader_eq (len := 5) span5 (Y := Y) (by omega) (by omega),
        resultWord_eq (len := 5) span5 (Y := Y) (by omega) (by omega), byteCopyLog, span5,
        allocateLog, allocateRegisters, F, OutLRange, List.cons_append, List.nil_append, List.range_succ,
        List.range_zero, List.map_cons, List.map_nil, List.append_assoc,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
      omega
  · rw [ls, nat _ (by omega), wv _ (out _ (by omega) (by omega) (by omega) (by omega))]
    simpa only [Layout.off_young_limit, Nat.add_zero] using wL
  · rw [ys]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  · rw [ls]; exact (window_of_nat (by rw [tohost]; omega) (by omega) (by omega)).read
  · rw [SH]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  · rw [SH]; simp only [guardB]
    exact Vsa.Sim.bltu_false_of_ge _ _ (by rw [nat _ (by omega), nat _ (by omega)]; omega)
  · apply imageOutside_of_above
    intro e he
    simp only [StringAllocation.reservationLog, ys, List.mem_singleton] at he
    subst he
    rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
  · apply imageOutside_of_above
    intro e he
    simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH, List.mem_singleton] at he
    subst he
    rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
  · rw [gd]
    change bytesT (writeLog (writeLog c.σ.mem _) _) _ 8 = _
    rw [bytesT_writeLog_out _ (by
      simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog, SmallAllocation.initializationLog,
        SmallAllocation.reservedRegisters, SH, ys, cs, OutLRange, List.cons_append, List.nil_append,
        nat _ (show D + 8 < 2 ^ 64 by omega), nat _ (show Y - 40 < 2 ^ 64 by omega), and_true]
      omega)]
    exact (wv _ (out _ (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega))).trans wD
  · simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog]
    rw [show ∀ (e : WEntry) (l : List WEntry), [e] ++ l = [] ++ e :: l from fun _ _ => rfl, word_last_store]
    · rfl
    · simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH, ys, OutLRange,
        nat _ (show D + 8 < 2 ^ 64 by omega), nat _ (show Y - 40 < 2 ^ 64 by omega), and_true]
      omega

/-- **The pair's layout** around the native frame `F = N - 112`. -/
theorem argv_finish_layout {N D Y Lm : Nat} {argv roots : BitVec 64} (nums : AllocNumbers N D Y Lm 40) :
    FinishLayout (BitVec.ofNat 64 (N - 112)) (BitVec.ofNat 64 (Y - 32)) (BitVec.ofNat 64 (Y - 8)) argv
      (BitVec.ofNat 64 D) roots := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have gd : DoubleAllocation.domainGlobal = BitVec.ofNat 64 0x80064d08 := rfl
  have ag : argvGlobal = BitVec.ofNat 64 0x80064c10 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have add : ∀ x k, x + k < 2 ^ 64 → BitVec.ofNat 64 x + BitVec.ofNat 64 k = BitVec.ofNat 64 (x + k) :=
    fun x k _ => ofNat_add_small
  have w : ∀ n, 0x80061fc0 + 16 ≤ n → n + 8 ≤ 0x100000000 → n % 8 = 0 → WriteWindow (BitVec.ofNat 64 n) 8 :=
    fun n lo hi al => window_of_nat (by rw [tohost]; exact lo) hi al
  have roots288 : BitVec.ofNat 64 D + BitVec.ofNat 64 Layout.off_local_roots = BitVec.ofNat 64 (D + 288) := by
    rw [ofNat_add_small]; rfl
  refine { stringSlot := ?_, resultSlot := ?_, firstField := ?_, secondField := ?_, argvRead := ?_,
           domainRead := ?_, rootsWrite := ?_, savedRa := ?_, savedS0 := ?_, savedS1 := ?_, savedS2 := ?_,
           resultOutsideTuple := ?_, argvOutside := ?_, domainOutside := ?_, savedOutside := ?_, image := ?_,
           rootsOutsideFirst := ?_, rootsOutsideSecond := ?_ }
  · exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact w _ (by omega) (by omega) (by omega)
  · exact w _ (by omega) (by omega) (by omega)
  · rw [add _ _ (by omega)]; exact w _ (by omega) (by omega) (by omega)
  · rw [ag]; exact (w _ (by omega) (by omega) (by decide)).read
  · rw [gd]; exact (w _ (by omega) (by omega) (by decide)).read
  · rw [roots288]; exact w _ (by omega) (by omega) (by omega)
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · simp only [pairLog, OutLRange, add _ _ (show Y - 32 + 8 < 2 ^ 64 by omega),
      add _ _ (show N - 112 + 8 < 2 ^ 64 by omega), nat _ (show Y - 32 < 2 ^ 64 by omega),
      nat _ (show Y - 32 + 8 < 2 ^ 64 by omega), nat _ (show N - 112 + 8 < 2 ^ 64 by omega), and_true]
    omega
  · simp only [pairLog, List.cons_append, List.nil_append, OutLRange, ag,
      add _ _ (show Y - 32 + 8 < 2 ^ 64 by omega), add _ _ (show N - 112 + 8 < 2 ^ 64 by omega),
      nat _ (show Y - 32 < 2 ^ 64 by omega), nat _ (show Y - 32 + 8 < 2 ^ 64 by omega),
      nat _ (show N - 112 + 8 < 2 ^ 64 by omega), nat _ (show 0x80064c10 < 2 ^ 64 by omega), and_true]
    omega
  · simp only [pairLog, List.cons_append, List.nil_append, OutLRange, gd,
      add _ _ (show Y - 32 + 8 < 2 ^ 64 by omega), add _ _ (show N - 112 + 8 < 2 ^ 64 by omega),
      nat _ (show Y - 32 < 2 ^ 64 by omega), nat _ (show Y - 32 + 8 < 2 ^ 64 by omega),
      nat _ (show N - 112 + 8 < 2 ^ 64 by omega), nat _ (show 0x80064d08 < 2 ^ 64 by omega), and_true]
    omega
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    simp only [tupleLog, pairLog, List.cons_append, List.nil_append, OutLRange, roots288,
      add _ _ (show Y - 32 + 8 < 2 ^ 64 by omega), add _ _ (show N - 112 + 8 < 2 ^ 64 by omega),
      nat _ (show Y - 32 < 2 ^ 64 by omega), nat _ (show Y - 32 + 8 < 2 ^ 64 by omega),
      nat _ (show N - 112 + 8 < 2 ^ 64 by omega), nat _ (show D + 288 < 2 ^ 64 by omega), and_true]
    rcases hk with rfl | rfl | rfl | rfl <;>
      rw [add _ _ (by omega), nat _ (by omega)] <;> omega
  · apply imageOutside_of_above
    intro e he
    simp only [tupleLog, pairLog, roots288, add _ _ (show Y - 32 + 8 < 2 ^ 64 by omega),
      add _ _ (show N - 112 + 8 < 2 ^ 64 by omega), List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [Layout.sym_bss_end]
    rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> rw [nat _ (by omega)] <;> omega
  · simp only [OutLRange, roots288, nat _ (show Y - 32 < 2 ^ 64 by omega),
      nat _ (show D + 288 < 2 ^ 64 by omega), and_true]
    omega
  · simp only [OutLRange, roots288, nat _ (show Y - 32 < 2 ^ 64 by omega),
      nat _ (show D + 288 < 2 ^ 64 by omega), and_true]
    omega

/-- **The four register saves survive every later store.** -/
theorem argv_savedTail {N D Y Lm a : Nat} {R : Nat → BitVec 64} {roots : BitVec 64} {g : Nat → BitVec 8}
    (nums : AllocNumbers N D Y Lm 40) (h2 : R 2 = BitVec.ofNat 64 N) :
    ∀ k ∈ [80, 88, 96, 104], OutLRange
      (afterSavedLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
        (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) a progExeName.length g)
      (frameSp (R 2) + BitVec.ofNat 64 k).toNat 8 := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  intro k hk
  have F := frameSp_eq h2 (by omega) (by omega)
  have hk' : k + 8 ≤ 112 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  rw [F, ofNat_add_small, toNat_ofNat_small (by omega)]
  simp only [afterSavedLog, prepareLog, savedLog, List.drop, List.cons_append, List.nil_append,
    StringCopy.completeLog, StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog,
    StringCopy.entryRegisters, StringCopy.sizeLog, StringCopy.lengthRegisters,
    StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
    StringAllocation.initializationLog, StringAllocation.reservedRegisters, StringAllocation.nurseryHeader,
    StringCopy.resultWord, DoubleAllocation.youngSlot, progExeName_length, span5, byteCopyLog,
    afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
    SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SmallAllocation.nurseryHeader, shift2,
    frameSp, h2, frameSp_ofNat (N := N) (by omega) (by omega), Layout.off_local_roots, Layout.off_young_ptr,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.append_assoc, OutLRange,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> omega

/-- The copied string object misses the pair's stores. -/
theorem argv_stringOutsideTuple {N D Y Lm : Nat} {argv roots : BitVec 64} (nums : AllocNumbers N D Y Lm 40) :
    ObjectOutside (tupleLog (BitVec.ofNat 64 (N - 112)) (BitVec.ofNat 64 (Y - 32)) (BitVec.ofNat 64 (Y - 8))
        argv (BitVec.ofNat 64 D) roots)
      (Y - 8) (.bytes (List.replicate 5 0)) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have w : (Obj.bytes (List.replicate 5 (0 : UInt8))).wosize = 1 := rfl
  refine ⟨?_, ?_⟩ <;> (try rw [w]) <;>
    simp only [tupleLog, pairLog, List.cons_append, List.nil_append, OutLRange, Layout.off_local_roots,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true] <;> omega

/-- The pair's header misses the pair's stores. -/
theorem argv_headerOutsideTuple {N D Y Lm : Nat} {argv roots : BitVec 64} (nums : AllocNumbers N D Y Lm 40) :
    OutLRange (tupleLog (BitVec.ofNat 64 (N - 112)) (BitVec.ofNat 64 (Y - 32)) (BitVec.ofNat 64 (Y - 8))
        argv (BitVec.ofNat 64 D) roots) (Y - 40) 8 := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  simp only [tupleLog, pairLog, List.cons_append, List.nil_append, OutLRange, Layout.off_local_roots,
    ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

/-- The copied string and the string slot miss the pair's reservation. -/
theorem argv_afterCopy {N D Y Lm : Nat} {R : Nat → BitVec 64} (nums : AllocNumbers N D Y Lm 40)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    ObjectOutside (afterCopyLog R (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)
        (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) progExeName.length)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length).toNat
      (.bytes (List.replicate progExeName.length 0)) ∧
    OutLRange (SmallAllocation.constructorLog allocate_call.link 2#64 0#64 (BitVec.ofNat 64 D)
        (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64)) (frameSp (R 2)).toNat 8 ∧
    ImageOutside (allocateLog (allocateRegisters R (BitVec.ofNat 64 Y) progExeName.length)) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have F := frameSp_eq h2 (by omega) (by omega)
  have BY := argvBlockYoung_eq Y (by omega) (by omega)
  have SH := smallHeader2 Y (by omega) (by omega)
  have rW := argvResultWord_eq Y (by omega) (by omega)
  have w : (Obj.bytes (List.replicate progExeName.length (0 : UInt8))).wosize = 1 := rfl
  rw [BY, rW]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
      StringAllocation.reservationLog, SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH,
      DoubleAllocation.youngSlot, F, OutLRange, List.cons_append, List.nil_append, Layout.off_young_ptr,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · rw [w]
    simp only [afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
      StringAllocation.reservationLog, SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH,
      DoubleAllocation.youngSlot, F, OutLRange, List.cons_append, List.nil_append, Layout.off_young_ptr,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog, SmallAllocation.initializationLog,
      SmallAllocation.reservedRegisters, SH, DoubleAllocation.youngSlot, F, OutLRange, List.cons_append,
      List.nil_append, Layout.off_young_ptr, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · apply imageOutside_of_above
    intro e he
    simp only [allocateLog, allocateRegisters, F, List.mem_singleton] at he
    subst he
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Layout.sym_bss_end]
    omega

/-- **The copy's site** in `caml_sys_get_argv`: below the 112-byte frame, on
the memory after the prepare block, copying the executable name. -/
theorem argv_site {c : Config} {N D Y Lm : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (nums : AllocNumbers N D Y Lm 40) (h2 : R 2 = BitVec.ofNat 64 N) (image : ExecutableImage c)
    (gp : gpr c 3 = some gpV)
    (wD : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (wY : word c (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y)
    (wL : word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm)
    (exe : ExeNamePlaced c) (nurseryLow : 0x80082000 ≤ Lm)
    (prepIn : LogInW (allocWindows N D Y 40) (prepareLog R (BitVec.ofNat 64 D) roots)) :
    CopySite (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))
      (N - 112) D Y Lm Gc.exeNameAddr 5 8 := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have xa := exe.domainApart
  rw [wD, toNat_ofNat_small (by omega)] at xa
  simp only [Layout.domainStateBytes, Gc.exeNameAddr] at xa
  have low : ∀ x, 0x8007d700 ≤ x → x < 0x8007d706 → OutL (prepareLog R (BitVec.ofNat 64 D) roots) x :=
    fun x lo hx => outL_of_range (outLRange_of_windows (a := x) (n := 1) prepIn (by
      simp only [allocWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega))
      (Nat.le_refl _) (by omega)
  have src : ∀ i : Fin 6, imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))
      (Gc.exeNameAddr + i.val) = Gc.exeNameBytes.getD i.val 0 := fun i => by
    simp only [imgM]
    rw [writeLog_out _ _ _ (low _ (by simp only [Gc.exeNameAddr]; omega)
      (by simp only [Gc.exeNameAddr]; omega)), ← exe.bytes i, byte_total]
  have out : ∀ x, (x + 8 ≤ D + 288 ∨ D + 296 ≤ x) → x + 8 ≤ N - 112 →
      OutLRange (prepareLog R (BitVec.ofNat 64 D) roots) x 8 := fun x r f =>
    argv_prepare_out (by omega) (by omega) (by omega) h2 r (.inl f)
  have cs : Layout.sym_Caml_state = 0x80064d08 := rfl
  refine { image := image_of_writeLog image ?_ rfl, gp := by rw [memoryView_gpr]; exact gp,
           nativeLow := by omega, nativeHigh := by omega, nativeAligned := by omega,
           domainLow := dl, domainHigh := dh, domainAligned := da, youngHigh := yh, youngAligned := ya,
           limitLow := ll, room := by omega, apart := ap, span := span5, spanFits := by decide,
           small := by decide, wD := ?_, wY := ?_, wL := ?_, srcLow := by decide,
           srcHtif := Or.inr (by decide), srcNursery := by simp only [Gc.exeNameAddr]; omega,
           srcDomain := by simp only [Gc.exeNameAddr]; omega, bytesNz := ?_, bytesNul := ?_ }
  · apply imageOutside_of_above
    intro x hx
    have := logInW_mem prepIn hx
    simp only [allocWindows, InsideW, Layout.off_young_ptr, Layout.off_local_roots] at this
    simp only [Layout.sym_bss_end]
    rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · omega
    · omega
    · omega
    · omega
    · exact h.elim
  · rw [view_word (out _ (by rw [cs]; omega) (by rw [cs]; omega)), wD]
  · rw [view_word (out _ (by simp only [Layout.off_young_ptr]; omega) (by simp only [Layout.off_young_ptr]; omega)), wY]
  · rw [view_word (out _ (by simp only [Layout.off_young_limit]; omega) (by simp only [Layout.off_young_limit]; omega)), wL]
  · intro i hi
    have nz : ∀ i, i < 5 → Gc.exeNameBytes.getD i 0 ≠ 0 := by decide
    change imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)) _ ≠ 0
    rw [src ⟨i, by omega⟩]; exact nz i hi
  · change imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)) _ = 0
    exact (src ⟨5, by decide⟩).trans rfl

end OCaml.Vm.Sim
