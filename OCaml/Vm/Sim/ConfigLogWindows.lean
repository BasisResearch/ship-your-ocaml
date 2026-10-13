import OCaml.Vm.Sim.StringAllocEntry
import OCaml.Vm.Primitives.GetConfigContract

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ConfigTuple
open ArgvTuple (frameSp)

theorem frameSp_ofNat {N : Nat} (h : 112 ≤ N) (h' : N < 2 ^ 64) :
    BitVec.ofNat 64 N + -112#64 = BitVec.ofNat 64 (N - 112) := by
  bv_omega

/-- The four windows `caml_sys_get_config` stores into. -/
def configWindows (N D Y : Nat) : List W :=
  [⟨N - 152, N⟩, ⟨Y - 48, Y⟩, ⟨D + Layout.off_young_ptr, D + Layout.off_young_ptr + 8⟩,
   ⟨D + Layout.off_local_roots, D + Layout.off_local_roots + 8⟩]

theorem prepareLog_in {N D Y : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (configWindows N D Y) (prepareLog R (BitVec.ofNat 64 D) roots) := by
  simp only [prepareLog, savedLog, frameSp, configWindows, h2, LogInW, InsideW, List.cons_append,
    List.nil_append, Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem span4 : StringAllocation.stringSpan (BitVec.ofNat 64 4) = 8#64 := by decide

theorem osType_length : osType.length = 4 := rfl

theorem completeLog_in {N D Y : Nat} {R : Nat → BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 48 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (configWindows N D Y) (StringCopy.completeLog prepare_call.link (frameSp (R 2))
      osTypeAddress.toNat osType.length g (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)) := by
  simp only [StringCopy.completeLog, StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog,
    StringCopy.entryRegisters, StringCopy.sizeLog, StringCopy.lengthRegisters,
    StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
    StringAllocation.initializationLog, StringAllocation.reservedRegisters, StringAllocation.nurseryHeader,
    StringCopy.resultWord, DoubleAllocation.youngSlot, osType_length, span4, byteCopyLog,
    frameSp, configWindows, h2, LogInW, InsideW, List.cons_append, List.nil_append,
    Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem shift3 : (3#64 <<< 3 : BitVec 64) = 24#64 := by decide

theorem afterCopyLog_in {N D Y : Nat} {R : Nat → BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 48 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (configWindows N D Y) (afterCopyLog R (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) osType.length) := by
  simp only [afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
    StringAllocation.reservationLog, SmallAllocation.initializationLog, SmallAllocation.reservedRegisters,
    SmallAllocation.nurseryHeader, StringAllocation.nurseryHeader, StringCopy.resultWord, DoubleAllocation.youngSlot,
    osType_length, span4, shift3, frameSp, configWindows, h2, LogInW, InsideW, List.cons_append, List.nil_append,
    Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem tripleLog_in {N D Y : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 48 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (configWindows N D Y) (tripleLog (frameSp (R 2))
      (tripleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64))
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length) (BitVec.ofNat 64 D) roots) := by
  simp only [tripleLog, tripleWord, SmallAllocation.nurseryHeader, StringAllocation.nurseryHeader,
    StringCopy.resultWord, osType_length, span4, shift3, frameSp, configWindows, h2, LogInW, InsideW,
    Layout.off_local_roots, Layout.off_young_ptr, frameSp_ofNat (N := N) (by omega) (by omega),
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

/-- **Every store of `caml_sys_get_config` lies in its four windows.** -/
theorem getConfigLog_in {N D Y : Nat} {R : Nat → BitVec 64} {roots : BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 48 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (configWindows N D Y) (getConfigLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) g) := by
  simp only [getConfigLog, allocatedLog, copiedLog]
  exact logInW_append' (logInW_append' (logInW_append' (prepareLog_in hN hN' hD h2)
    (completeLog_in hN hN' hD hY hY' h2)) (afterCopyLog_in hN hN' hD hY hY' h2))
    (tripleLog_in hN hN' hD hY hY' h2)

theorem word_last_store {m : Std.ExtHashMap Nat (BitVec 8)} {l1 l2 : List WEntry} {a : Nat} {v : BitVec 64}
    (out : OutLRange l2 a 8) : bytesT (writeLog m (l1 ++ (a, 8, v) :: l2)) a 8 = v := by
  rw [writeLog_append]
  exact Gc.word_writeLog_at _ ((a, 8, v) :: l2) 0 a v rfl (by simpa using out)

/-- The triple's reservation is the last store to the young pointer. -/
theorem getConfigLog_split (R : Nat → BitVec 64) (D Y : Nat) (roots : BitVec 64) (g : Nat → BitVec 8) :
    getConfigLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) g =
    (copiedLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g ++
      allocateLog (allocateRegisters R (BitVec.ofNat 64 Y) osType.length)) ++
    ((DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat, 8,
      StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64 - 8#64 - (3#64 <<< 3)) ::
    (SmallAllocation.initializationLog (SmallAllocation.reservedRegisters allocate_call.link 3#64 0#64
        (SmallAllocation.nurseryHeader (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) 3#64)) ++
      tripleLog (frameSp (R 2)) (tripleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64))
        (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length) (BitVec.ofNat 64 D) roots) := by
  simp only [getConfigLog, allocatedLog, afterCopyLog, SmallAllocation.constructorLog,
    StringAllocation.reservationLog, List.append_assoc, List.cons_append, List.nil_append]

/-- **The young pointer after `caml_sys_get_config`**: `Y - 48`, below the
string and the triple. -/
theorem getConfig_young {m : Std.ExtHashMap Nat (BitVec 8)} {N D Y : Nat} {R : Nat → BitVec 64}
    {roots : BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 48 ≤ Y) (hY' : Y < 2 ^ 32)
    (apart : D + 928 ≤ Y - 48 ∨ Y ≤ D) (native : Y + 4096 ≤ N) (domainBelow : D + 928 + 4096 ≤ N)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    bytesT (writeLog m (getConfigLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) g)) (D + Layout.off_young_ptr) 8 =
      BitVec.ofNat 64 (Y - 48) := by
  have slot : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + Layout.off_young_ptr := by
    simp only [DoubleAllocation.youngSlot, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Layout.off_young_ptr]
    omega
  rw [getConfigLog_split, ← slot, word_last_store]
  · simp only [StringCopy.resultWord, StringAllocation.nurseryHeader, osType_length, span4, shift3]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  · have s8 : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + 8 := slot
    simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, tripleLog, tripleWord,
      SmallAllocation.nurseryHeader, StringAllocation.nurseryHeader, StringCopy.resultWord, osType_length, span4,
      shift3, frameSp, h2, List.cons_append, List.nil_append, OutLRange, Layout.off_local_roots,
      frameSp_ofNat (N := N) (by omega) (by omega), BitVec.toNat_sub, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega

theorem logInW_prefix {ws : List W} {l1 l2 : List WEntry} (h : LogInW ws (l1 ++ l2)) : LogInW ws l1 := by
  induction l1 with
  | nil => trivial
  | cons e l ih => exact ⟨h.1, ih h.2⟩

theorem logInW_suffix {ws : List W} {l1 l2 : List WEntry} (h : LogInW ws (l1 ++ l2)) : LogInW ws l2 := by
  induction l1 with
  | nil => exact h
  | cons e l ih => exact ih h.2

/-- Every store before the triple's reservation lies in the four windows. -/
theorem beforeSmallLog_in {N D Y : Nat} {R : Nat → BitVec 64} {roots : BitVec 64} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 48 ≤ Y) (hY' : Y < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    LogInW (configWindows N D Y) (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g) := by
  have after := afterCopyLog_in (R := R) hN hN' hD hY hY' h2
  simp only [afterCopyLog] at after
  simp only [beforeSmallLog, copiedLog]
  exact logInW_append' (logInW_append' (prepareLog_in hN hN' hD h2) (completeLog_in hN hN' hD hY hY' h2))
    (logInW_prefix after)

/-- The string's reservation is the last store to the young pointer before
the triple's. -/
theorem beforeSmallLog_split (R : Nat → BitVec 64) (D Y : Nat) (roots : BitVec 64) (g : Nat → BitVec 8) :
    beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g =
    (prepareLog R (BitVec.ofNat 64 D) roots ++
      StringCopy.prefixLog prepare_call.link (frameSp (R 2)) osTypeAddress.toNat osType.length ++
      savedRaLog (frameSp (R 2) - 32#64) StringCopy.size_call.link) ++
    ((DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat, 8,
      BitVec.ofNat 64 Y - 8#64 - StringAllocation.stringSpan (BitVec.ofNat 64 osType.length)) ::
    (StringAllocation.initializationLog
        (StringAllocation.reservedRegisters StringCopy.size_call.link (frameSp (R 2) - 32#64)
          (BitVec.ofNat 64 osType.length)
          (StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) (BitVec.ofNat 64 osType.length)))
        (StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) (BitVec.ofNat 64 osType.length)) ++
      byteCopyLog (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length).toNat osType.length
        (fun i => g (osTypeAddress.toNat + i)) ++
      allocateLog (allocateRegisters R (BitVec.ofNat 64 Y) osType.length)) := by
  simp only [beforeSmallLog, copiedLog, StringCopy.completeLog, StringCopy.allocationLog,
    StringAllocation.constructorLog, StringAllocation.reservationLog, List.append_assoc, List.cons_append,
    List.nil_append]

end OCaml.Vm.Sim
