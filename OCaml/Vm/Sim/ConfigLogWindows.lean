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

end OCaml.Vm.Sim
