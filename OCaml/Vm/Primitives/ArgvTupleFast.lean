import OCaml.Vm.Primitives.ArgvTuple
import OCaml.Vm.Primitives.LibraryEffects

namespace OCaml.Vm.Primitives.ArgvTuple
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

def frameSp (sp : BitVec 64) : BitVec 64 := sp + (-112#64)

/-- Native saves precede all global and local-root reads. -/
def savedLog (R : Nat → BitVec 64) : List WEntry :=
  [(((frameSp (R 2) + 104#64)).toNat, 8, R 1), (((frameSp (R 2) + 88#64)).toNat, 8, R 9),
   (((frameSp (R 2) + 80#64)).toNat, 8, R 18), (((frameSp (R 2) + 96#64)).toNat, 8, R 8)]

/-- Concrete root frame installed before the first allocating call. -/
def prepareLog (R : Nat → BitVec 64) (domain roots : BitVec 64) : List WEntry :=
  savedLog R ++
  [((domain + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, (frameSp (R 2) + 16#64)),
   (((frameSp (R 2) + 0#64)).toNat, 8, 1#64), (((frameSp (R 2) + 8#64)).toNat, 8, 1#64),
   (((frameSp (R 2) + 32#64)).toNat, 8, 1#64), (((frameSp (R 2) + 48#64)).toNat, 8, (frameSp (R 2) + 8#64)),
   (((frameSp (R 2) + 16#64)).toNat, 8, roots), (((frameSp (R 2) + 24#64)).toNat, 8, 2#64),
   (((frameSp (R 2) + 40#64)).toNat, 8, (frameSp (R 2) + 0#64))]

theorem prepare_log (R : Nat → BitVec 64) (bd be br : List (BitVec 8)) :
    (evalBlocks prepare_blocks (SegEvalState.init (prepare_input R) [bd,be,br])).log =
      prepareLog R (bytesVal .ld bd) (bytesVal .ld br) := by
  change wlogM prepare_body (prepare_input R) [bd, be, br] = _
  rw [prepare_log_chunks]
  simp only [prepare_piece0_log, prepare_piece1_log, prepare_piece2_log, prepare_piece3_log,
    prepare_piece4_log, prepareLog, savedLog, frameSp, Layout.off_local_roots,
    List.append, BitVec.add_zero]
  rfl

theorem prepare_fast (c : Config) (R : Nat → BitVec 64) (bd be br : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (prepare_input R))
    (access : AccessPlan c.σ.mem (prepare_input R) [bd,be,br] prepare_body)
    (outside : ImageOutside (prepareLog R (bytesVal .ld bd) (bytesVal .ld br))) :
    FnSummary 0x8001cf08#64 (fun d => d = c)
      (WriteRegistersPost [2,8,9,10,13,14,15,18]
        (prepareLog R (bytesVal .ld bd) (bytesVal .ld br)) c prepare_call.pc
        (bytesVal .ld be) (prepare_regs R [bd,be,br])) := by
  apply registers_of_blocks h.image outside
    (prepare_summary c (R 1) R _ h regs access True.intro)
  · exact prepare_log R bd be br
  · rfl
  · exact prepare_eval R _
  · rfl
  · decide

def allocateLog (R : Nat → BitVec 64) : List WEntry := [( (R 2).toNat, 8, R 10)]

theorem allocate_log (R : Nat → BitVec 64) :
    (evalBlocks allocate_blocks (SegEvalState.init (allocate_input R) [])).log = allocateLog R := by
  simp [evalBlocks, evalBlock, SegEvalState.init, allocate_blocks, allocate_body, allocate_input,
    wlogM, wentryM, widthOfM, stepGM, stepLdsM, wvalM, eaddrM, srcVal, lookupG, eraseG,
    allocateLog, Functions.sign_extend, Sail.BitVec.signExtend]

theorem allocate_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (allocate_input R))
    (slot : WriteWindow (R 2) 8) (outside : ImageOutside (allocateLog R)) :
    FnSummary 0x8001cf68#64 (fun d => d = c)
      (WriteRegistersPost [10,11] (allocateLog R) c allocate_call.pc (R 18) (allocate_regs R [])) := by
  have access : AccessPlan c.σ.mem (allocate_input R) [] allocate_body := by
    simp only [AccessPlan, allocate_body]
    chain_facts True.intro
    apply slot.sd rfl
    simp [eaddrM, allocate_input, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  apply registers_of_blocks h.image outside
    (allocate_summary c (R 1) R [] h regs access True.intro)
  · exact allocate_log R
  · rfl
  · exact allocate_eval R []
  · rfl
  · decide

/-- Stores in the tuple initializer and native epilogue. -/
def finishLog (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) : List WEntry :=
  [((R 2 + 8#64).toNat, 8, R 10),
   ((R 10).toNat, 8, bytesVal .ld (loads.getD 0 [])),
   ((bytesVal .ld (loads.getD 1 []) + 8#64).toNat, 8, bytesVal .ld (loads.getD 2 [])),
   ((bytesVal .ld (loads.getD 3 []) + BitVec.ofNat 64 Layout.off_local_roots).toNat, 8, R 8)]

theorem finish_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks finish_blocks (SegEvalState.init (finish_input R) loads)).log = finishLog R loads := by
  change wlogM finish_body (finish_input R) loads = _
  rw [finish_log_chunks]
  simp [finish_piece0_log, finish_piece1_log, finish_piece2_log, finishLog, Layout.off_local_roots]

theorem finish_fast (c : Config) (ra callRa : BitVec 64) (R : Nat → BitVec 64)
    (loads : List (List (BitVec 8))) (h : LeafInput callRa c)
    (returnAligned : ra.toNat % 4 = 0)
    (regs : GHolds c.σ (finish_input R))
    (access : AccessPlan c.σ.mem (finish_input R) loads finish_body)
    (outside : ImageOutside (finishLog R loads))
    (savedRa : bytesVal .ld (loads.getD 5 []) = ra) :
    FnSummary 0x8001cf78#64 (fun d => d = c)
      (WriteRegistersPost [1,2,8,9,10,14,15,18] (finishLog R loads) c ra
        (bytesVal .ld (loads.getD 4 [])) (finish_regs R loads)) := by
  have control : TermFactsO (runGM finish_body (finish_input R) loads) (some finish_term) := by
    rw [finish_eval]
    apply return_facts _ rfl rfl rfl ?_ returnAligned
    simpa [finish_regs, srcVal, lookupG] using savedRa
  apply registers_of_blocks h.image outside
    (finish_summary c callRa R loads h regs access control)
  · exact finish_log R loads
  · change tgtPCT finish_term (runGM finish_body (finish_input R) loads) = ra
    rw [finish_eval]
    change Sail.BitVec.update (bytesVal .ld (loads.getD 5 []) + Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra
    rw [savedRa]
    exact ret_tgt ra returnAligned
  · exact finish_eval R loads
  · rfl
  · decide

end OCaml.Vm.Primitives.ArgvTuple
