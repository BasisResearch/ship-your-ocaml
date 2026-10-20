import OCaml.Vm.Sim.ConfigLogWindows
import OCaml.Vm.Sim.PrimExecutableNameReturns
import OCaml.Vm.Primitives.GetArgvContract

/-!
# `caml_sys_get_argv`'s stores, in four windows

The argv instance of `ConfigLogWindows`: the copied executable name (a
16-byte block) and the pair (24 bytes) make a 40-byte nursery block, so every
store lies in `allocWindows N D Y 40`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ArgvTuple

theorem progExeName_length : progExeName.length = 5 := rfl

theorem shift2 : (2#64 <<< 3 : BitVec 64) = 16#64 := by decide

theorem argv_prepareLog_in {N D Y : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (allocWindows N D Y 40) (prepareLog R (BitVec.ofNat 64 D) roots) := by
  simp only [prepareLog, savedLog, frameSp, allocWindows, h2, LogInW, InsideW, List.cons_append,
    List.nil_append, Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem argv_completeLog_in {N D Y a : Nat} {R : Nat → BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 40 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (allocWindows N D Y 40) (StringCopy.completeLog prepare_call.link (frameSp (R 2))
      a progExeName.length g (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)) := by
  simp only [StringCopy.completeLog, StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog,
    StringCopy.entryRegisters, StringCopy.sizeLog, StringCopy.lengthRegisters,
    StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
    StringAllocation.initializationLog, StringAllocation.reservedRegisters, StringAllocation.nurseryHeader,
    StringCopy.resultWord, DoubleAllocation.youngSlot, progExeName_length, span5, byteCopyLog,
    frameSp, allocWindows, h2, LogInW, InsideW, List.cons_append, List.nil_append,
    Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem argv_afterCopyLog_in {N D Y : Nat} {R : Nat → BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 40 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (allocWindows N D Y 40) (afterCopyLog R (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) progExeName.length) := by
  simp only [afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
    StringAllocation.reservationLog, SmallAllocation.initializationLog, SmallAllocation.reservedRegisters,
    SmallAllocation.nurseryHeader, StringAllocation.nurseryHeader, StringCopy.resultWord, DoubleAllocation.youngSlot,
    progExeName_length, span5, shift2, frameSp, allocWindows, h2, LogInW, InsideW, List.cons_append,
    List.nil_append, Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem argv_tupleLog_in {N D Y : Nat} {R : Nat → BitVec 64} {argv roots : BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 40 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (allocWindows N D Y 40) (tupleLog (frameSp (R 2))
      (tupleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64))
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length) argv (BitVec.ofNat 64 D) roots) := by
  simp only [tupleLog, pairLog, tupleWord, SmallAllocation.nurseryHeader, StringAllocation.nurseryHeader,
    StringCopy.resultWord, progExeName_length, span5, shift2, frameSp, allocWindows, h2, LogInW, InsideW,
    List.cons_append, List.nil_append, Layout.off_local_roots, Layout.off_young_ptr,
    frameSp_ofNat (N := N) (by omega) (by omega),
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

/-- **Every store of `caml_sys_get_argv` lies in its four windows.** -/
theorem getArgvLog_in {N D Y a : Nat} {R : Nat → BitVec 64} {argv roots : BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 40 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (allocWindows N D Y 40) (getArgvLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) argv a progExeName.length g) := by
  simp only [getArgvLog, allocatedLog, copiedLog]
  exact logInW_append' (logInW_append' (logInW_append' (argv_prepareLog_in hN hN' hD h2)
    (argv_completeLog_in hN hN' hD hY hY' h2)) (argv_afterCopyLog_in hN hN' hD hY hY' h2))
    (argv_tupleLog_in hN hN' hD hY hY' h2)

/-- The pair's reservation is the last store to the young pointer. -/
theorem getArgvLog_split (R : Nat → BitVec 64) (D Y a : Nat) (argv roots : BitVec 64) (g : Nat → BitVec 8) :
    getArgvLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) argv a progExeName.length g =
    (copiedLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g ++
      allocateLog (allocateRegisters R (BitVec.ofNat 64 Y) progExeName.length)) ++
    ((DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat, 8,
      StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64 - 8#64 - (2#64 <<< 3)) ::
    (SmallAllocation.initializationLog (SmallAllocation.reservedRegisters allocate_call.link 2#64 0#64
        (SmallAllocation.nurseryHeader (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) 2#64)) ++
      tupleLog (frameSp (R 2)) (tupleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64))
        (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length) argv (BitVec.ofNat 64 D) roots) := by
  simp only [getArgvLog, allocatedLog, afterCopyLog, SmallAllocation.constructorLog,
    StringAllocation.reservationLog, List.append_assoc, List.cons_append, List.nil_append]

/-- **The young pointer after `caml_sys_get_argv`**: `Y - 40`, below the
string and the pair. -/
theorem getArgv_young {m : Std.ExtHashMap Nat (BitVec 8)} {N D Y a : Nat} {R : Nat → BitVec 64}
    {argv roots : BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 40 ≤ Y) (hY' : Y < 2 ^ 32)
    (apart : D + 928 ≤ Y - 40 ∨ Y ≤ D) (native : Y + 4096 ≤ N) (domainBelow : D + 928 + 4096 ≤ N)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    bytesT (writeLog m (getArgvLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) argv a progExeName.length g))
      (D + Layout.off_young_ptr) 8 = BitVec.ofNat 64 (Y - 40) := by
  have slot : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + Layout.off_young_ptr := by
    simp only [DoubleAllocation.youngSlot, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Layout.off_young_ptr]
    omega
  rw [getArgvLog_split, ← slot, word_last_store]
  · simp only [StringCopy.resultWord, StringAllocation.nurseryHeader, progExeName_length, span5, shift2]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  · have s8 : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + 8 := slot
    simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, tupleLog, pairLog, tupleWord,
      SmallAllocation.nurseryHeader, StringAllocation.nurseryHeader, StringCopy.resultWord, progExeName_length,
      span5, shift2, frameSp, h2, List.cons_append, List.nil_append, OutLRange, Layout.off_local_roots,
      frameSp_ofNat (N := N) (by omega) (by omega), BitVec.toNat_sub, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega

/-- Every store before the pair's reservation lies in the four windows. -/
theorem argv_beforeSmallLog_in {N D Y a : Nat} {R : Nat → BitVec 64} {roots : BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 40 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (allocWindows N D Y 40)
      (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g) := by
  have after := argv_afterCopyLog_in (R := R) hN hN' hD hY hY' h2
  simp only [afterCopyLog] at after
  simp only [beforeSmallLog, copiedLog]
  exact logInW_append' (logInW_append' (argv_prepareLog_in hN hN' hD h2) (argv_completeLog_in hN hN' hD hY hY' h2))
    (logInW_prefix after)

/-- The string's reservation is the last store to the young pointer before
the pair's. -/
theorem argv_beforeSmallLog_split (R : Nat → BitVec 64) (D Y a : Nat) (roots : BitVec 64) (g : Nat → BitVec 8) :
    beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) a progExeName.length g =
    (prepareLog R (BitVec.ofNat 64 D) roots ++
      StringCopy.prefixLog prepare_call.link (frameSp (R 2)) a progExeName.length ++
      savedRaLog (frameSp (R 2) - 32#64) StringCopy.size_call.link) ++
    ((DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat, 8,
      BitVec.ofNat 64 Y - 8#64 - StringAllocation.stringSpan (BitVec.ofNat 64 progExeName.length)) ::
    (StringAllocation.initializationLog
        (StringAllocation.reservedRegisters StringCopy.size_call.link (frameSp (R 2) - 32#64)
          (BitVec.ofNat 64 progExeName.length)
          (StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) (BitVec.ofNat 64 progExeName.length)))
        (StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) (BitVec.ofNat 64 progExeName.length)) ++
      byteCopyLog (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length).toNat progExeName.length
        (fun i => g (a + i)) ++
      allocateLog (allocateRegisters R (BitVec.ofNat 64 Y) progExeName.length)) := by
  simp only [beforeSmallLog, copiedLog, StringCopy.completeLog, StringCopy.allocationLog,
    StringAllocation.constructorLog, StringAllocation.reservationLog, List.append_assoc, List.cons_append,
    List.nil_append]

end OCaml.Vm.Sim
