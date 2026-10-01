import OCaml.Vm.Primitives.StringAllocation
import OCaml.Vm.Primitives.NativeStack
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.DoubleFast

namespace OCaml.Vm.Primitives.StringAllocation
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- The saved RA occupies the top word of the 48-byte native frame. -/
theorem prepare_save_address (sp : BitVec 64) : sp - 48#64 + 40#64 = sp - 8#64 := by
  bv_omega

/-- The size-check prefix has exactly one scalar store. -/
theorem prepare_access (c : Config) (R : Nat → BitVec 64) (loads : List (List (BitVec 8)))
    (stack : WriteWindow (R 2 - 8#64) 8) :
    AccessPlan c.σ.mem (prepare_input R) loads prepare_body := by
  simp only [AccessPlan, prepare_body]
  chain_facts True.intro
  apply stack.sd rfl
  simp [eaddrM, prepare_input, stepGM, wvalM, srcVal, lookupG, eraseG,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.sub_eq_add_neg]
  bv_omega

/-- The first block only writes its saved native return address. -/
theorem prepare_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks prepare_blocks (SegEvalState.init (prepare_input R) loads)).log =
      savedRaLog (R 2) (R 1) := by
  change [(((R 2 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfd0#12)) +
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x028#12)).toNat, 8, R 1)] = _
  have down : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfd0#12) = -48#64 := by decide
  have up : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x028#12) = 40#64 := by decide
  rw [down, up, ← BitVec.sub_eq_add_neg, prepare_save_address]
  rfl

/-- Select the nursery size branch and retain its exact stack effect. -/
theorem prepare_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (prepare_input R))
    (stack : WriteWindow (R 2 - 8#64) 8)
    (outside : ImageOutside (savedRaLog (R 2) (R 1)))
    (small : guardB .BLTU 256#64 (stringWords (R 10)) = false) :
    FnSummary 0x8000c174#64 (fun d => d = c)
      (WriteRegistersPost [2, 10, 13, 14, 15] (savedRaLog (R 2) (R 1)) c
        0x8000c194#64 (stringWords (R 10)) (prepare_regs R)) := by
  have control : TermFactsO (runGM prepare_body (prepare_input R) []) (some prepare_term) := by
    rw [prepare_eval]
    simpa [TermFactsO, TermFactsT, prepare_term, prepare_regs, srcVal, lookupG] using small
  apply registers_of_blocks h.image outside
    (prepare_summary c (R 1) R [] h regs (prepare_access c R [] stack) control)
  · exact prepare_log R []
  · rfl
  · exact prepare_eval R []
  · rfl
  · decide

/-- Reserve the header and the rounded payload in the nursery. -/
def reservationLog (domain young span : BitVec 64) : List WEntry :=
  [((DoubleAllocation.youngSlot domain).toNat, 8, young - 8#64 - span)]

/-- The reservation block needs three scalar reads and one metadata store. -/
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

/-- Exact metadata effect of a successful reservation. -/
theorem reserve_log (R : Nat → BitVec 64) (bd byoung blimit : List (BitVec 8)) :
    (evalBlocks reserve_blocks (SegEvalState.init (reserve_input R) [bd, byoung, blimit])).log =
      reservationLog (bytesVal .ld bd) (bytesVal .ld byoung) (R 15) := by
  simp [evalBlocks, evalBlock, SegEvalState.init, reserve_blocks, reserve_body, reserve_input,
    wlogM, wentryM, widthOfM, stepGM, stepLdsM, wvalM, eaddrM, srcVal, lookupG, eraseG, imm20Of,
    reservationLog, DoubleAllocation.youngSlot, Layout.off_young_ptr,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.sub_eq_add_neg]
  bv_omega

/-- The nursery-room guard selects reservation's successful successor. -/
theorem reserve_fast (c : Config) (R : Nat → BitVec 64) (bd byoung blimit : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (reserve_input R))
    (access : AccessPlan c.σ.mem (reserve_input R) [bd, byoung, blimit] reserve_body)
    (outside : ImageOutside (reservationLog (bytesVal .ld bd) (bytesVal .ld byoung) (R 15)))
    (room : guardB .BLTU (bytesVal .ld byoung - 8#64 - R 15) (bytesVal .ld blimit) = false) :
    FnSummary 0x8000c194#64 (fun d => d = c)
      (WriteRegistersPost [11, 12, 13, 16, 17]
        (reservationLog (bytesVal .ld bd) (bytesVal .ld byoung) (R 15)) c
        0x8000c1bc#64 (R 10) (reserve_regs R bd byoung blimit)) := by
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

/-- String initialization writes its header, zeroes the final word, then
stores the byte-count padding marker. -/
def initializationLog (R : Nat → BitVec 64) (young : BitVec 64) : List WEntry :=
  [( (R 13).toNat, 8, (R 10 <<< 10) + 252#64),
   ((young + 8#64 + R 15 - 8#64).toNat, 8, 0#64),
   ((young + 8#64 + (R 15 - 1#64)).toNat, 1, paddingWord (R 15) (R 14))]

/-- Exact first-order log of the generated initialization and epilogue. -/
theorem initialize_log (R : Nat → BitVec 64) (bd byoung bra : List (BitVec 8)) :
    (evalBlocks initialize_blocks (SegEvalState.init (initialize_input R) [bd, byoung, bra])).log =
      initializationLog R (bytesVal .ld byoung) := by
  simp only [evalBlocks, evalBlock, SegEvalState.init, initialize_blocks, initialize_body, initialize_input,
    wlogM, wentryM, widthOfM, stepGM, stepLdsM, wvalM, eaddrM, srcVal, lookupG, eraseG,
    Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some,
    List.headD_cons, List.tail_cons, List.nil_append]
  have h0 : Functions.sign_extend (m := 64) (0#12) = 0#64 := by decide
  have h8 : Functions.sign_extend (m := 64) (8#12) = 8#64 := by decide
  have h252 : Functions.sign_extend (m := 64) (252#12) = 252#64 := by decide
  have hm8 : Functions.sign_extend (m := 64) (4088#12) = -8#64 := by decide
  have hm1 : Functions.sign_extend (m := 64) (4095#12) = -1#64 := by decide
  simp only [h0, h8, h252, hm8, hm1, ← BitVec.sub_eq_add_neg, BitVec.add_zero]
  rfl

/-- Scalar obligations for initializing a string and restoring its native frame.
The two metadata reads follow the header store; the saved RA read follows
all three stores, so its pins explicitly describe that updated memory. -/
theorem initialize_access (c : Config) (R : Nat → BitVec 64) (bd byoung bra : List (BitVec 8))
    (header : WriteWindow (R 13) 8) (global : ReadWindow (R 16) 8)
    (young : ReadWindow (DoubleAllocation.youngSlot (bytesVal .ld bd)) 8)
    (lastWord : WriteWindow (bytesVal .ld byoung + 8#64 + R 15 - 8#64) 8)
    (padding : WriteWindow (bytesVal .ld byoung + 8#64 + (R 15 - 1#64)) 1)
    (saved : ReadWindow (R 2 + 40#64) 8)
    (domainPins : LPins8 (writeLog c.σ.mem [((R 13).toNat, 8, (R 10 <<< 10) + 252#64)])
      (R 16).toNat bd)
    (youngPins : LPins8 (writeLog c.σ.mem [((R 13).toNat, 8, (R 10 <<< 10) + 252#64)])
      (DoubleAllocation.youngSlot (bytesVal .ld bd)).toNat byoung)
    (savedPins : LPins8 (writeLog c.σ.mem (initializationLog R (bytesVal .ld byoung)))
      (R 2 + 40#64).toNat bra) :
    AccessPlan c.σ.mem (initialize_input R) [bd, byoung, bra] initialize_body := by
  have h0 : Functions.sign_extend (m := 64) (0#12) = 0#64 := by decide
  have h8 : Functions.sign_extend (m := 64) (8#12) = 8#64 := by decide
  have h252 : Functions.sign_extend (m := 64) (252#12) = 252#64 := by decide
  have h40 : Functions.sign_extend (m := 64) (40#12) = 40#64 := by decide
  have hm8 : Functions.sign_extend (m := 64) (4088#12) = -8#64 := by decide
  have hm1 : Functions.sign_extend (m := 64) (4095#12) = -1#64 := by decide
  simp only [AccessPlan, initialize_body]
  chain_facts True.intro
  all_goals simp only [initialize_input, stepMemM, wentryM, widthOfM, stepGM, stepLdsM,
    wvalM, eaddrM, srcVal, lookupG, eraseG, Nat.reduceAdd, Nat.reduceEqDiff,
    ite_true, ite_false, Option.getD_some, List.headD_cons, List.tail_cons,
    h0, h8, h252, h40, hm8, hm1, ← BitVec.sub_eq_add_neg, BitVec.add_zero]
  · apply header.sd (m := c.σ.mem) rfl
    simp [eaddrM, srcVal, lookupG, h0]
  · apply global.ld rfl ?_ domainPins
    simp [eaddrM, srcVal, lookupG, h0]
  · exact young.ld rfl rfl youngPins
  · apply lastWord.sd rfl
    simp [eaddrM, srcVal, lookupG, hm8, BitVec.sub_eq_add_neg]
  · apply padding.sb rfl
    simp [eaddrM, srcVal, lookupG, h0]
  · exact saved.ld rfl rfl savedPins

/-- The final block restores the saved return address and exposes all
initialized bytes through its exact log. -/
theorem initialize_fast (c : Config) (R : Nat → BitVec 64) (bd byoung bra : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (initialize_input R))
    (access : AccessPlan c.σ.mem (initialize_input R) [bd, byoung, bra] initialize_body)
    (outside : ImageOutside (initializationLog R (bytesVal .ld byoung)))
    (savedRa : bytesVal .ld bra = R 1) :
    FnSummary 0x8000c1bc#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 10, 13, 14, 15]
        (initializationLog R (bytesVal .ld byoung)) c
        (R 1) (bytesVal .ld byoung + 8#64) (initialize_regs R byoung bra)) := by
  have control : TermFactsO (runGM initialize_body (initialize_input R) [bd, byoung, bra])
      (some initialize_term) := by
    rw [initialize_eval]
    apply return_facts _ rfl rfl rfl ?_ h.aligned
    simpa [initialize_regs, srcVal, lookupG] using savedRa
  apply registers_of_blocks h.image outside
    (initialize_summary c (R 1) R _ h regs access control)
  · exact initialize_log R bd byoung bra
  · change tgtPCT initialize_term (runGM initialize_body (initialize_input R) [bd, byoung, bra]) = R 1
    rw [initialize_eval]
    change Sail.BitVec.update (bytesVal .ld bra + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = R 1
    rw [savedRa]
    exact ret_tgt (R 1) h.aligned
  · exact initialize_eval R bd byoung bra
  · rfl
  · decide

end OCaml.Vm.Primitives.StringAllocation
