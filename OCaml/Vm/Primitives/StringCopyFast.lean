import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.StringCopy
import OCaml.Vm.Primitives.LibraryEffects

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Native caller frame: saved return address and source C-string pointer. -/
def saveLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 8#64).toNat, 8, R 1), ((R 2 - 24#64).toNat, 8, R 10)]

theorem save_access (c : Config) (R : Nat → BitVec 64) (loads : List (List (BitVec 8)))
    (returnSlot : WriteWindow (R 2 - 8#64) 8)
    (sourceSlot : WriteWindow (R 2 - 24#64) 8) :
    AccessPlan c.σ.mem (save_input R) loads save_body := by
  simp only [AccessPlan, save_body]
  chain_facts True.intro
  · apply returnSlot.sd rfl
    simp [eaddrM, srcVal, lookupG, save_input, stepGM, wvalM,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega
  · apply sourceSlot.sd rfl
    simp [eaddrM, srcVal, lookupG, save_input, stepGM, wvalM,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega

theorem save_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks save_blocks (SegEvalState.init (save_input R) loads)).log = saveLog R := by
  change [((R 2 + Functions.sign_extend (m := 64) (0xfe0#12) + 24#64).toNat, 8, R 1),
    ((R 2 + Functions.sign_extend (m := 64) (0xfe0#12) + 8#64).toNat, 8, R 10)] = saveLog R
  have down : Functions.sign_extend (m := 64) (0xfe0#12) = -32#64 := by decide
  have raAddr : R 2 + -32#64 + 24#64 = R 2 - 8#64 := by bv_omega
  have srcAddr : R 2 + -32#64 + 8#64 = R 2 - 24#64 := by bv_omega
  rw [down, raAddr, srcAddr]
  rfl

/-- Execute the generated prefix up to the strlen call instruction. -/
theorem save_fast (c : Config) (R : Nat → BitVec 64) (h : LeafInput (R 1) c)
    (regs : GHolds c.σ (save_input R))
    (returnSlot : WriteWindow (R 2 - 8#64) 8)
    (sourceSlot : WriteWindow (R 2 - 24#64) 8)
    (outside : ImageOutside (saveLog R)) :
    FnSummary 0x8000c254#64 (fun d => d = c)
      (WriteRegistersPost [2] (saveLog R) c save_call.pc (R 10) (save_regs R [])) := by
  apply registers_of_blocks h.image outside
    (save_summary c (R 1) R [] h regs (save_access c R [] returnSlot sourceSlot) True.intro)
  · exact save_log R []
  · rfl
  · exact save_eval R []
  · rfl
  · decide

/-- The length slot belongs to the already-reserved native caller frame. -/
def sizeLog (R : Nat → BitVec 64) : List WEntry := [((R 2).toNat, 8, R 10)]

theorem size_access (c : Config) (R : Nat → BitVec 64)
    (slot : WriteWindow (R 2) 8) : AccessPlan c.σ.mem (size_input R) [] size_body := by
  simp only [AccessPlan, size_body]
  chain_facts True.intro
  apply slot.sd rfl
  simp [eaddrM, srcVal, lookupG, size_input, Functions.sign_extend, Sail.BitVec.signExtend]

theorem size_log (R : Nat → BitVec 64) :
    (evalBlocks size_blocks (SegEvalState.init (size_input R) [])).log = sizeLog R := by
  change [((R 2 + 0#64).toNat, 8, R 10)] = sizeLog R
  simp [sizeLog]

theorem size_fast (c : Config) (R : Nat → BitVec 64) (h : LeafInput (R 1) c)
    (regs : GHolds c.σ (size_input R)) (slot : WriteWindow (R 2) 8)
    (outside : ImageOutside (sizeLog R)) :
    FnSummary 0x8000c264#64 (fun d => d = c)
      (WriteRegistersPost [] (sizeLog R) c size_call.pc (R 10) (size_regs R [])) := by
  apply registers_of_blocks h.image outside
    (size_summary c (R 1) R [] h regs (size_access c R slot) True.intro)
  · exact size_log R
  · rfl
  · exact size_eval R []
  · rfl
  · decide

theorem arguments_access (c : Config) (R : Nat → BitVec 64) (len src : List (BitVec 8))
    (lengthSlot : ReadWindow (R 2) 8) (sourceSlot : ReadWindow (R 2 + 8#64) 8)
    (lengthPins : LPins8 c.σ.mem (R 2).toNat len)
    (sourcePins : LPins8 c.σ.mem (R 2 + 8#64).toNat src) :
    AccessPlan c.σ.mem (arguments_input R) [len, src] arguments_body := by
  simp only [AccessPlan, arguments_body]
  chain_facts True.intro
  · apply lengthSlot.ld rfl ?_ lengthPins
    simp [eaddrM, srcVal, lookupG, arguments_input, Functions.sign_extend, Sail.BitVec.signExtend]
  · apply sourceSlot.ld rfl ?_ sourcePins
    simp [eaddrM, srcVal, lookupG, arguments_input, stepGM, wvalM, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]

theorem arguments_fast (c : Config) (R : Nat → BitVec 64) (len src : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (arguments_input R))
    (lengthSlot : ReadWindow (R 2) 8) (sourceSlot : ReadWindow (R 2 + 8#64) 8)
    (lengthPins : LPins8 c.σ.mem (R 2).toNat len)
    (sourcePins : LPins8 c.σ.mem (R 2 + 8#64).toNat src) :
    FnSummary 0x8000c26c#64 (fun d => d = c)
      (RegistersPost [11, 12] c.σ.mem c arguments_call.pc (R 10) (arguments_regs R [len, src])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (arguments_summary c (R 1) R [len, src] h regs
      (arguments_access c R len src lengthSlot sourceSlot lengthPins sourcePins) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact arguments_eval R [len, src]
  · rfl
  · decide

theorem restore_access (c : Config) (R : Nat → BitVec 64) (ra : List (BitVec 8))
    (slot : ReadWindow (R 2 + 24#64) 8)
    (pins : LPins8 c.σ.mem (R 2 + 24#64).toNat ra) :
    AccessPlan c.σ.mem (restore_input R) [ra] restore_body := by
  simp only [AccessPlan, restore_body]
  chain_facts True.intro
  apply slot.ld rfl ?_ pins
  simp [eaddrM, srcVal, lookupG, restore_input, Functions.sign_extend, Sail.BitVec.signExtend]

theorem restore_fast (c : Config) (R : Nat → BitVec 64) (ra : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (restore_input R))
    (slot : ReadWindow (R 2 + 24#64) 8)
    (pins : LPins8 c.σ.mem (R 2 + 24#64).toNat ra)
    (aligned : (bytesVal .ld ra).toNat % 4 = 0) :
    FnSummary 0x8000c278#64 (fun d => d = c)
      (RegistersPost [1, 2] c.σ.mem c (bytesVal .ld ra) (R 10) (restore_regs R [ra])) := by
  have control : TermFactsO (runGM restore_body (restore_input R) [ra]) (some restore_term) := by
    rw [restore_eval]
    exact return_facts _ rfl rfl rfl rfl aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (restore_summary c (R 1) R [ra] h regs (restore_access c R ra slot pins) control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change tgtPCT restore_term (runGM restore_body (restore_input R) [ra]) = _
    rw [restore_eval]
    exact ret_tgt _ aligned
  · exact restore_eval R [ra]
  · rfl
  · decide

end OCaml.Vm.Primitives.StringCopy
