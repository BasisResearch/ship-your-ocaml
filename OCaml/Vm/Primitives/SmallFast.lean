import OCaml.Vm.Primitives.SmallAllocation
import OCaml.Vm.Primitives.StringFast

namespace OCaml.Vm.Primitives.SmallAllocation
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

theorem reserve_access (c : Config) (R : Nat → BitVec 64) (bd byoung blimit : List (BitVec 8))
    (young : WriteWindow (DoubleAllocation.youngSlot (bytesVal .ld bd)) 8)
    (limit : ReadWindow (DoubleAllocation.limitSlot (bytesVal .ld bd)) 8)
    (domainPins : LPins8 c.σ.mem DoubleAllocation.domainGlobal.toNat bd)
    (youngPins : LPins8 c.σ.mem (DoubleAllocation.youngSlot (bytesVal .ld bd)).toNat byoung)
    (limitPins : LPins8 c.σ.mem (DoubleAllocation.limitSlot (bytesVal .ld bd)).toNat blimit) :
    AccessPlan c.σ.mem (reserve_input R) [bd, byoung, blimit] reserve_body := by
  simp only [AccessPlan, reserve_body]
  chain_facts True.intro
  · apply DoubleAllocation.domain_read.ld rfl ?_ domainPins
    simp [eaddrM, reserve_input, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of,
      DoubleAllocation.domainGlobal, Layout.sym_Caml_state,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  · apply young.read.ld rfl ?_ youngPins
    simp [eaddrM, reserve_input, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
      DoubleAllocation.youngSlot, Layout.off_young_ptr,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  · apply limit.ld rfl ?_ limitPins
    simp [eaddrM, reserve_input, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
      DoubleAllocation.limitSlot, Layout.off_young_limit,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  · apply young.sd rfl
    simp [eaddrM, reserve_input, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
      DoubleAllocation.youngSlot, Layout.off_young_ptr,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem reserve_log (R : Nat → BitVec 64) (bd byoung blimit : List (BitVec 8)) :
    (evalBlocks reserve_blocks (SegEvalState.init (reserve_input R) [bd, byoung, blimit])).log =
      StringAllocation.reservationLog (bytesVal .ld bd) (bytesVal .ld byoung) (R 10 <<< 3) := by
  simp [evalBlocks, evalBlock, SegEvalState.init, reserve_blocks, reserve_body, reserve_input,
    wlogM, wentryM, widthOfM, stepGM, stepLdsM, wvalM, eaddrM, srcVal, lookupG, eraseG, imm20Of,
    StringAllocation.reservationLog, DoubleAllocation.youngSlot, Layout.off_young_ptr,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.sub_eq_add_neg,
    shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_right, Sail.shift_bits_left]
  bv_omega

/-- The nursery-room guard selects reservation's successful successor. -/
theorem reserve_fast (c : Config) (R : Nat → BitVec 64) (bd byoung blimit : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (reserve_input R))
    (access : AccessPlan c.σ.mem (reserve_input R) [bd, byoung, blimit] reserve_body)
    (outside : ImageOutside (StringAllocation.reservationLog (bytesVal .ld bd) (bytesVal .ld byoung) (R 10 <<< 3)))
    (room : guardB .BLTU (bytesVal .ld byoung - 8#64 - (R 10 <<< 3)) (bytesVal .ld blimit) = false) :
    FnSummary 0x8000c0b8#64 (fun d => d = c)
      (WriteRegistersPost [6, 12, 13, 14, 16, 17]
        (StringAllocation.reservationLog (bytesVal .ld bd) (bytesVal .ld byoung) (R 10 <<< 3)) c
        0x8000c0e4#64 (R 10) (reserve_regs R bd byoung blimit)) := by
  have control : TermFactsO (runGM reserve_body (reserve_input R) [bd, byoung, blimit])
      (some reserve_term) := by
    rw [reserve_eval]
    simpa [TermFactsO, TermFactsT, reserve_term, reserve_regs, srcVal, lookupG] using room
  apply registers_of_blocks h.image outside
    (reserve_summary c (R 1) R _ h regs access control)
  · exact reserve_log R bd byoung blimit
  · rfl
  · exact reserve_eval R bd byoung blimit
  · rfl
  · decide

def initializationLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 14).toNat, 8, (R 10 <<< 10) + tagWord (R 11))]

theorem initialize_log (R : Nat → BitVec 64) (bd byoung : List (BitVec 8)) :
    (evalBlocks initialize_blocks (SegEvalState.init (initialize_input R) [bd, byoung])).log =
      initializationLog R := by
  simp [evalBlocks, evalBlock, SegEvalState.init, initialize_blocks, initialize_body, initialize_input,
    wlogM, wentryM, widthOfM, stepGM, stepLdsM, wvalM, eaddrM, srcVal, lookupG, eraseG,
    initializationLog, tagWord, Functions.sign_extend, Sail.BitVec.signExtend,
    shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_right, Sail.shift_bits_left]

/-- Scalar reads follow the header write; pins refer to that updated memory. -/
theorem initialize_access (c : Config) (R : Nat → BitVec 64) (bd byoung : List (BitVec 8))
    (header : WriteWindow (R 14) 8) (global : ReadWindow (R 17) 8)
    (young : ReadWindow (DoubleAllocation.youngSlot (bytesVal .ld bd)) 8)
    (domainPins : LPins8 (writeLog c.σ.mem (initializationLog R)) (R 17).toNat bd)
    (youngPins : LPins8 (writeLog c.σ.mem (initializationLog R))
      (DoubleAllocation.youngSlot (bytesVal .ld bd)).toNat byoung) :
    AccessPlan c.σ.mem (initialize_input R) [bd, byoung] initialize_body := by
  simp only [AccessPlan, initialize_body]
  chain_facts True.intro
  · apply header.sd rfl
    simp [eaddrM, initialize_input, stepGM, wvalM, srcVal, lookupG, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]
  · apply global.ld rfl
    · simp [eaddrM, initialize_input, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        Functions.sign_extend, Sail.BitVec.signExtend]
    · simpa [stepMemM, stepLdsM, initialize_input, initializationLog, applyW,
        wentryM, widthOfM, eaddrM, stepGM, wvalM, srcVal, lookupG, eraseG,
        tagWord, Functions.sign_extend, Sail.BitVec.signExtend,
        shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_right, Sail.shift_bits_left, writeLog] using domainPins
  · apply young.ld rfl
    · simp [eaddrM, initialize_input, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        DoubleAllocation.youngSlot, Layout.off_young_ptr, Functions.sign_extend, Sail.BitVec.signExtend]
    · simpa [stepMemM, stepLdsM, initialize_input, initializationLog, applyW,
        wentryM, widthOfM, eaddrM, stepGM, wvalM, srcVal, lookupG, eraseG,
        tagWord, Functions.sign_extend, Sail.BitVec.signExtend,
        shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_right, Sail.shift_bits_left, writeLog] using youngPins

theorem initialize_fast (c : Config) (R : Nat → BitVec 64) (bd byoung : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (initialize_input R))
    (access : AccessPlan c.σ.mem (initialize_input R) [bd, byoung] initialize_body)
    (outside : ImageOutside (initializationLog R)) :
    FnSummary 0x8000c0e4#64 (fun d => d = c)
      (WriteRegistersPost [10, 15, 16] (initializationLog R) c
        (R 1) (bytesVal .ld byoung + 8#64) (initialize_regs R bd byoung)) := by
  have control : TermFactsO (runGM initialize_body (initialize_input R) [bd, byoung])
      (some initialize_term) := by
    rw [initialize_eval]
    exact return_facts _ rfl rfl rfl rfl h.aligned
  apply registers_of_blocks h.image outside
    (initialize_summary c (R 1) R _ h regs access control)
  · exact initialize_log R bd byoung
  · change tgtPCT initialize_term (runGM initialize_body (initialize_input R) [bd, byoung]) = R 1
    rw [initialize_eval]
    exact ret_tgt (R 1) h.aligned
  · exact initialize_eval R bd byoung
  · rfl
  · decide

end OCaml.Vm.Primitives.SmallAllocation
