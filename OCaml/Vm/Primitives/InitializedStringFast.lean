import OCaml.Vm.Primitives.InitializedStringSteps
import OCaml.Vm.Primitives.StringCopyFinish

namespace OCaml.Vm.Primitives.InitializedString
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- The actual ABI keeps length in a0 and the caller buffer in a1. -/
def entryRegisters (ra sp : BitVec 64) (a len : Nat) : Nat → BitVec 64
  | 1 => ra | 2 => sp | 10 => BitVec.ofNat 64 len | 11 => BitVec.ofNat 64 a | _ => 0

theorem save_access (c : Config) (R : Nat → BitVec 64)
    (returnSlot : WriteWindow (R 2 - 8#64) 8)
    (sourceSlot : WriteWindow (R 2 - 24#64) 8)
    (lengthSlot : WriteWindow (R 2 - 32#64) 8) :
    AccessPlan c.σ.mem (save_input R) [] save_body := by
  simp only [AccessPlan, save_body]
  chain_facts True.intro
  · apply returnSlot.sd rfl
    simp [eaddrM, srcVal, lookupG, save_input, stepGM, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega
  · apply sourceSlot.sd rfl
    simp [eaddrM, srcVal, lookupG, save_input, stepGM, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega
  · apply lengthSlot.sd rfl
    simp [eaddrM, srcVal, lookupG, save_input, stepGM, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega

theorem save_log (ra sp : BitVec 64) (a len : Nat) :
    (evalBlocks save_blocks (SegEvalState.init (save_input (entryRegisters ra sp a len)) [])).log =
      StringCopy.callerLog ra sp a len := by
  change [((sp + Functions.sign_extend (m := 64) (0xfe0#12) + 24#64).toNat, 8, ra),
    ((sp + Functions.sign_extend (m := 64) (0xfe0#12) + 8#64).toNat, 8, BitVec.ofNat 64 a),
    ((sp + Functions.sign_extend (m := 64) (0xfe0#12) + 0#64).toNat, 8, BitVec.ofNat 64 len)] = _
  have down : Functions.sign_extend (m := 64) (0xfe0#12) = -32#64 := by decide
  have raAddr : sp + -32#64 + 24#64 = sp - 8#64 := by bv_omega
  have srcAddr : sp + -32#64 + 8#64 = sp - 24#64 := by bv_omega
  rw [down, raAddr, srcAddr, BitVec.add_zero, ← BitVec.sub_eq_add_neg]
  rfl

theorem save_fast (c : Config) (ra sp : BitVec 64) (a len : Nat)
    (h : LeafInput ra c) (regs : GHolds c.σ (save_input (entryRegisters ra sp a len)))
    (returnSlot : WriteWindow (sp - 8#64) 8)
    (sourceSlot : WriteWindow (sp - 24#64) 8)
    (lengthSlot : WriteWindow (sp - 32#64) 8)
    (outside : ImageOutside (StringCopy.callerLog ra sp a len)) :
    FnSummary 0x8000c284#64 (fun d => d = c)
      (WriteRegistersPost [2] (StringCopy.callerLog ra sp a len) c save_call.pc
        (BitVec.ofNat 64 len) (save_regs (entryRegisters ra sp a len) [])) := by
  apply registers_of_blocks h.image outside
    (save_summary c ra (entryRegisters ra sp a len) [] h regs
      (save_access c _ returnSlot sourceSlot lengthSlot) True.intro)
  · exact save_log ra sp a len
  · rfl
  · exact save_eval _ []
  · rfl
  · decide

/-- Identical load laws are shared with the existing copy producer; only the
checked native instruction addresses and JAL encoding differ. -/
theorem arguments_fast (c : Config) (R : Nat → BitVec 64) (len src : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (StringCopy.arguments_input R))
    (lengthSlot : ReadWindow (R 2) 8) (sourceSlot : ReadWindow (R 2 + 8#64) 8)
    (lengthPins : LPins8 c.σ.mem (R 2).toNat len)
    (sourcePins : LPins8 c.σ.mem (R 2 + 8#64).toNat src) :
    FnSummary 0x8000c298#64 (fun d => d = c)
      (RegistersPost [11, 12] c.σ.mem c arguments_call.pc (R 10) (StringCopy.arguments_regs R [len, src])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (arguments_summary c (R 1) R [len, src] h regs
      (StringCopy.arguments_access c R len src lengthSlot sourceSlot lengthPins sourcePins) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact arguments_eval R [len, src]
  · rfl
  · decide

theorem restore_fast (c : Config) (R : Nat → BitVec 64) (ra : List (BitVec 8))
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (StringCopy.restore_input R))
    (slot : ReadWindow (R 2 + 24#64) 8)
    (pins : LPins8 c.σ.mem (R 2 + 24#64).toNat ra)
    (aligned : (bytesVal .ld ra).toNat % 4 = 0) :
    FnSummary arguments_call.link (fun d => d = c)
      (RegistersPost [1, 2] c.σ.mem c (bytesVal .ld ra) (R 10) (StringCopy.restore_regs R [ra])) := by
  have control : TermFactsO (runGM restore_body (restore_input R) [ra]) (some restore_term) := by
    rw [restore_eval]
    exact return_facts _ rfl rfl rfl rfl aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (restore_summary c (R 1) R [ra] h regs (StringCopy.restore_access c R ra slot pins) control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change tgtPCT restore_term (runGM restore_body (restore_input R) [ra]) = _
    rw [restore_eval]
    exact ret_tgt _ aligned
  · exact restore_eval R [ra]
  · rfl
  · decide

def tailBoundary : StringCopy.TailBoundary :=
  ⟨save_call.link, 0x8000c298#64, arguments_call, arguments_call_shape,
    arguments_call_decode, arguments_call_target, arguments_call_pins,
    arguments_fast, restore_fast⟩

end OCaml.Vm.Primitives.InitializedString
