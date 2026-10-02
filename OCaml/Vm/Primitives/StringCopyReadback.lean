import OCaml.Vm.Primitives.StringCopyAllocated

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim StringAllocation

/-- The three saved caller words lie outside every later store before memcpy. -/
structure CallerSeparation (ra sp : BitVec 64) (a len : Nat) (domain young : BitVec 64) : Prop where
  returnSlot : OutLRange
    ([((sp - 24#64).toNat, 8, BitVec.ofNat 64 a)] ++ sizeLog (lengthRegisters sp len) ++
      constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young)
    (sp - 8#64).toNat 8
  sourceSlot : OutLRange
    (sizeLog (lengthRegisters sp len) ++
      constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young)
    (sp - 24#64).toNat 8
  lengthSlot : OutLRange
    (constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young)
    (sp - 32#64).toNat 8

structure CallerReadback (ra sp : BitVec 64) (a len : Nat) (c : Config) : Prop where
  returnValue : word c (sp - 8#64).toNat = ra
  sourceValue : word c (sp - 24#64).toNat = BitVec.ofNat 64 a
  lengthValue : word c (sp - 32#64).toNat = BitVec.ofNat 64 len

/-- Observe the native save slots through the computed allocation effect. -/
theorem caller_readback {ra sp a len domain young} {before after : Config}
    (separate : CallerSeparation ra sp a len domain young)
    (memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (allocationLog ra sp a len domain young))) :
    CallerReadback ra sp a len after := by
  have observe := fun x => Vsa.Sim.Boot.bytesT_memEqv memory x 8
  constructor
  · change bytesT after.σ.mem _ 8 = _
    rw [observe]
    rw [show allocationLog ra sp a len domain young = [((sp - 8#64).toNat, 8, ra)] ++
      ([((sp - 24#64).toNat, 8, BitVec.ofNat 64 a)] ++ sizeLog (lengthRegisters sp len) ++
       constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young) from rfl,
      writeLog_append, bytesT_writeLog_out _ separate.returnSlot]
    exact word_writeLog _ _ _
  · change bytesT after.σ.mem _ 8 = _
    rw [observe]
    rw [show allocationLog ra sp a len domain young =
      ([((sp - 8#64).toNat, 8, ra)] ++ [((sp - 24#64).toNat, 8, BitVec.ofNat 64 a)]) ++
      (sizeLog (lengthRegisters sp len) ++
       constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young) from rfl,
      writeLog_append, bytesT_writeLog_out _ separate.sourceSlot, writeLog_append]
    exact word_writeLog _ _ _
  · change bytesT after.σ.mem _ 8 = _
    rw [observe, allocationLog, writeLog_append, bytesT_writeLog_out _ separate.lengthSlot,
      prefixLog, writeLog_append]
    exact word_writeLog _ _ _

theorem source_address (sp : BitVec 64) : sp - 32#64 + 8#64 = sp - 24#64 := by bv_omega
theorem return_address (sp : BitVec 64) : sp - 32#64 + 24#64 = sp - 8#64 := by bv_omega

end OCaml.Vm.Primitives.StringCopy
