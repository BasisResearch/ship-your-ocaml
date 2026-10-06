import OCaml.Vm.Primitives.FdWrite.WriteFd
import OCaml.Vm.Primitives.FdWrite.EnterBlocking
import OCaml.Vm.Primitives.FdWrite.Write
import OCaml.Vm.Primitives.FdWrite.WriteR
import OCaml.Vm.Primitives.FdWrite.LeaveBlocking
import OCaml.Vm.Primitives.FdWrite.Errno
import OCaml.Vm.Primitives.FdWrite.EnterDefault
import OCaml.Vm.Primitives.FdWrite.LeaveDefault
import OCaml.Vm.Primitives.ExitPath.Effects
import OCaml.Vm.Primitives.ArgvTupleFinished

/-! Effect wrappers of the console-write path's runtime and newlib blocks. -/
namespace OCaml.Vm.Primitives.FdWrite
open Vsa.Machine Vsa.Sim LeanRV64DExecutable
open ExitPath (ReadWindow.lw read8_pins4 sx16)

def impurePtr : BitVec 64 := 0x800648f8#64
def errnoGlobal : BitVec 64 := 0x80064d48#64
def enterHook : BitVec 64 := 0x80064870#64
def leaveHook : BitVec 64 := 0x80064868#64
def pendingSignals : BitVec 64 := 0x80068690#64

theorem sx80 : BitVec.signExtend 64 4016#12 = -80#64 := by decide

/-- A 32-bit store with its RAM, HTIF and alignment bounds. -/
theorem WriteWindow.sw {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {bs : List (BitVec 8)}
    {a : MInstr} {x : BitVec 64} (h : WriteWindow x 4) (kind : a.kind = .sw) (address : eaddrM a L = x) :
    MemFacts m L bs a := by
  simp only [MemFacts, kind, address]
  refine ⟨h.lower, h.upper, ?_, h.aligned⟩
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using h.htif

namespace WriteFd

def proLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 80#64 + 56#64).toNat, 8, R 9), ((R 2 - 80#64 + 48#64).toNat, 8, R 18),
   ((R 2 - 80#64 + 40#64).toNat, 8, R 19), ((R 2 - 80#64 + 32#64).toNat, 8, R 20),
   ((R 2 - 80#64 + 24#64).toNat, 8, R 21), ((R 2 - 80#64 + 16#64).toNat, 8, R 22),
   ((R 2 - 80#64 + 8#64).toNat, 8, R 23), ((R 2 - 80#64 + 72#64).toNat, 8, R 1),
   ((R 2 - 80#64 + 64#64).toNat, 8, R 8)]

theorem pro_log (R : Nat → BitVec 64) :
    (evalBlocks pro_blocks (SegEvalState.init (pro_input R) [])).log = proLog R := by
  change [] ++ wlogM pro_body (pro_input R) [] = _
  simp only [List.nil_append, pro_body, wlogM, pro_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx80, ← BitVec.sub_eq_add_neg]
  simp only [show BitVec.signExtend 64 56#12 = 56#64 by decide, show BitVec.signExtend 64 48#12 = 48#64 by decide, show BitVec.signExtend 64 40#12 = 40#64 by decide, show BitVec.signExtend 64 32#12 = 32#64 by decide, show BitVec.signExtend 64 24#12 = 24#64 by decide, show BitVec.signExtend 64 16#12 = 16#64 by decide, show BitVec.signExtend 64 8#12 = 8#64 by decide, show BitVec.signExtend 64 72#12 = 72#64 by decide, show BitVec.signExtend 64 64#12 = 64#64 by decide]
  rfl

theorem pro_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (pro_input R))
    (slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72], WriteWindow (R 2 - 80#64 + BitVec.ofNat 64 k) 8)
    (outside : ImageOutside (proLog R)) :
    FnSummary 0x80025274#64 (fun d => d = c)
      (WriteRegistersPost [2, 9, 18, 19, 20, 21, 22, 23] (proLog R) c 0x800252b8#64 (R 10) (pro_regs R [])) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (pro_input R) [] pro_body := by
    simp only [AccessPlan, pro_body]
    chain_facts True.intro
    · apply (w 56 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 48 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 40 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 32 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 24 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 16 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 8 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 72 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]
    · apply (w 64 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, pro_input]

  apply registers_of_blocks h.image outside (pro_summary c (R 1) R [] h regs access True.intro)
  · exact pro_log R
  · rfl
  · exact pro_eval R []
  · rfl
  · decide

theorem enter_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (enter_input R)) :
    FnSummary 0x800252b8#64 (fun d => d = c)
      (WriteRegistersPost [] [] c enter_call.pc (R 10) (enter_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (enter_summary c (R 1) R [] h regs trivial True.intro)
  · rfl
  · rfl
  · exact enter_eval R _
  · rfl
  · decide

theorem call_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (call_input R)) :
    FnSummary 0x800252bc#64 (fun d => d = c)
      (WriteRegistersPost [10, 11, 12] [] c call_call.pc (R 22) (call_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (call_summary c (R 1) R [] h regs (by simp only [AccessPlan, call_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact call_eval R _
  · rfl
  · decide

theorem leave_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leave_input R)) :
    FnSummary 0x800252cc#64 (fun d => d = c)
      (WriteRegistersPost [8] [] c leave_call.pc (R 10) (leave_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leave_summary c (R 1) R [] h regs (by simp only [AccessPlan, leave_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact leave_eval R _
  · rfl
  · decide

theorem check_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (check_input R))
    (ok : R 8 ≠ R 19) :
    FnSummary 0x800252d4#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x80025308#64 (R 10) (check_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (check_summary c (R 1) R [] h regs trivial (by rw [check_eval]; simp [TermFactsO, TermFactsT, check_term, check_regs, srcVal, lookupG, guardB, ok]))
  · rfl
  · rfl
  · exact check_eval R _
  · rfl
  · decide

def epiLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [72, 64, 56, 48, 40, 32, 24, 16, 8].map fun k => read8 m (R 2 + BitVec.ofNat 64 k).toNat

theorem epi_fast (c : Config) (ra : BitVec 64) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (epi_input R))
    (slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72], ReadWindow (R 2 + BitVec.ofNat 64 k) 8)
    (savedRa : bytesVal .ld (read8 c.σ.mem (R 2 + 72#64).toNat) = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80025308#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23] [] c ra (R 8) (epi_regs R (epiLoads c.σ.mem R))) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (epi_input R) (epiLoads c.σ.mem R) epi_body := by
    simp only [AccessPlan, epi_body, epiLoads, List.map]
    chain_facts True.intro
    · apply (w 72 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 64 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 56 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 48 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 40 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 32 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 24 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 16 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]
    · apply (w 8 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, epi_input]

  have control : TermFactsO (runGM epi_body (epi_input R) (epiLoads c.σ.mem R)) (some epi_term) := by
    rw [epi_eval]
    exact return_facts _ rfl rfl rfl (by simpa [epi_regs, srcVal, lookupG, epiLoads] using savedRa) aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (epi_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change tgtPCT epi_term (runGM epi_body (epi_input R) (epiLoads c.σ.mem R)) = ra
    rw [epi_eval]
    change Sail.BitVec.update (bytesVal .ld ((epiLoads c.σ.mem R).getD 0 []) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra
    simp only [epiLoads, List.map, List.getD_cons_zero]
    rw [savedRa]
    exact ret_tgt ra aligned
  · exact epi_eval R _
  · rfl
  · decide

end WriteFd

namespace EnterBlocking

/-- The blocking-section entry tail-jumps through its hook. -/
theorem hook_fast (c : Config) (R : Nat → BitVec 64) (hook : BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (hook_input R))
    (value : bytesVal .ld (read8 c.σ.mem enterHook.toNat) = hook) (aligned : hook.toNat % 4 = 0) :
    FnSummary 0x8000d4ac#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c hook (R 10) (hook_regs R [read8 c.σ.mem enterHook.toNat])) := by
  have access : AccessPlan c.σ.mem (hook_input R) [read8 c.σ.mem enterHook.toNat] hook_body := by
    simp only [AccessPlan, hook_body]
    chain_facts True.intro
    apply (show ReadWindow enterHook 8 from ⟨by decide, by decide, Or.inr (by decide)⟩).ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, hook_input, enterHook]
  have control : TermFactsO (runGM hook_body (hook_input R) [read8 c.σ.mem enterHook.toNat]) (some hook_term) := by
    rw [hook_eval]
    simp only [TermFactsO, TermFactsT, hook_term, hook_regs, srcVal, lookupG, ↓reduceIte, Nat.reduceEqDiff,
      Option.getD_some, List.getD_cons_zero, value]
    rw [ret_tgt hook aligned]
    exact aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (hook_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change tgtPCT hook_term (runGM hook_body (hook_input R) [read8 c.σ.mem enterHook.toNat]) = hook
    rw [hook_eval]
    change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem enterHook.toNat) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1 = hook
    rw [value]
    exact ret_tgt hook aligned
  · exact hook_eval R _
  · rfl
  · decide

end EnterBlocking

namespace Write

/-- `write` loads the reentrancy pointer and tail-jumps to `_write_r`. -/
theorem tail_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (tail_input R)) :
    FnSummary 0x80042628#64 (fun d => d = c)
      (WriteRegistersPost [10, 11, 12, 13, 14] [] c 0x800424b4#64
        (bytesVal .ld (read8 c.σ.mem impurePtr.toNat)) (tail_regs R [read8 c.σ.mem impurePtr.toNat])) := by
  have access : AccessPlan c.σ.mem (tail_input R) [read8 c.σ.mem impurePtr.toNat] tail_body := by
    simp only [AccessPlan, tail_body]
    chain_facts True.intro
    apply (show ReadWindow impurePtr 8 from ⟨by decide, by decide, Or.inr (by decide)⟩).ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, tail_input, impurePtr]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (tail_summary c (R 1) R _ h regs access True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact tail_eval R _
  · rfl
  · decide

end Write

namespace WriteR

def enterLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 16#64).toNat, 8, R 8), ((R 2 - 16#64 + 8#64).toNat, 8, R 1), (errnoGlobal.toNat, 4, 0#64)]

theorem enter_log (R : Nat → BitVec 64) :
    (evalBlocks enter_blocks (SegEvalState.init (enter_input R) [])).log = enterLog R := by
  change [] ++ wlogM enter_body (enter_input R) [] = _
  simp only [List.nil_append, enter_body, wlogM, enter_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx16, ← BitVec.sub_eq_add_neg]
  simp only [show BitVec.signExtend 64 8#12 = 8#64 by decide, show BitVec.signExtend 64 0#12 = 0#64 by decide,
    BitVec.add_zero]
  rfl

theorem enter_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (enter_input R))
    (low : WriteWindow (R 2 - 16#64) 8) (high : WriteWindow (R 2 - 16#64 + 8#64) 8)
    (outside : ImageOutside (enterLog R)) :
    FnSummary 0x800424b4#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 10, 11, 12, 15] (enterLog R) c enter_call.pc (R 11) (enter_regs R [])) := by
  have access : AccessPlan c.σ.mem (enter_input R) [] enter_body := by
    simp only [AccessPlan, enter_body]
    chain_facts True.intro
    · apply low.sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply high.sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · simp [MemFacts, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, enter_input, tohostAddr, LibraryLayout.tohostAddr]
  apply registers_of_blocks h.image outside (enter_summary c (R 1) R [] h regs access True.intro)
  · exact enter_log R
  · rfl
  · exact enter_eval R []
  · rfl
  · decide

theorem check_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (check_input R))
    (ok : R 10 ≠ 18446744073709551615#64) :
    FnSummary 0x800424e0#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x800424e8#64 (R 10) (check_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (check_summary c (R 1) R [] h regs (by simp only [AccessPlan, check_body]; chain_facts True.intro) (by rw [check_eval]; simp [TermFactsO, TermFactsT, check_term, check_regs, srcVal, lookupG, guardB, ok]))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact check_eval R _
  · rfl
  · decide

def retLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (R 2 + 8#64).toNat, read8 m (R 2).toNat]

theorem ret_fast (c : Config) (ra : BitVec 64) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (ret_input R))
    (high : ReadWindow (R 2 + 8#64) 8) (low : ReadWindow (R 2) 8)
    (savedRa : bytesVal .ld (read8 c.σ.mem (R 2 + 8#64).toNat) = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800424e8#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8] [] c ra (R 10) (ret_regs R (retLoads c.σ.mem R))) := by
  have access : AccessPlan c.σ.mem (ret_input R) (retLoads c.σ.mem R) ret_body := by
    simp only [AccessPlan, ret_body, retLoads]
    chain_facts True.intro
    · apply high.ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, ret_input]
    · apply low.ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, ret_input]
  have control : TermFactsO (runGM ret_body (ret_input R) (retLoads c.σ.mem R)) (some ret_term) := by
    rw [ret_eval]
    exact return_facts _ rfl rfl rfl (by simpa [ret_regs, srcVal, lookupG, retLoads] using savedRa) aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (ret_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change tgtPCT ret_term (runGM ret_body (ret_input R) (retLoads c.σ.mem R)) = ra
    rw [ret_eval]
    change Sail.BitVec.update (bytesVal .ld ((retLoads c.σ.mem R).getD 0 []) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra
    simp only [retLoads, List.getD_cons_zero]
    rw [savedRa]
    exact ret_tgt ra aligned
  · exact ret_eval R _
  · rfl
  · decide

end WriteR

namespace EnterDefault
theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x8000d2a4#64 (fun d => d = c)
      (WriteRegistersPost [] [] c (R 1) (R 10) (leaf_regs R [])) := by
  have control : TermFactsO (runGM leaf_body (leaf_input R) []) (some leaf_term) :=
    return_facts _ rfl rfl rfl rfl h.aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leaf_summary c (R 1) R [] h regs trivial control)
  · rfl
  · change Sail.BitVec.update (R 1 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = R 1
    exact ret_tgt (R 1) h.aligned
  · exact leaf_eval R []
  · rfl
  · decide
end EnterDefault

namespace LeaveDefault
theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x8000d2a8#64 (fun d => d = c)
      (WriteRegistersPost [] [] c (R 1) (R 10) (leaf_regs R [])) := by
  have control : TermFactsO (runGM leaf_body (leaf_input R) []) (some leaf_term) :=
    return_facts _ rfl rfl rfl rfl h.aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leaf_summary c (R 1) R [] h regs trivial control)
  · rfl
  · change Sail.BitVec.update (R 1 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = R 1
    exact ret_tgt (R 1) h.aligned
  · exact leaf_eval R []
  · rfl
  · decide
end LeaveDefault

namespace Errno

theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x80042518#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c (R 1) (bytesVal .ld (read8 c.σ.mem impurePtr.toNat))
        (leaf_regs R [read8 c.σ.mem impurePtr.toNat])) := by
  have access : AccessPlan c.σ.mem (leaf_input R) [read8 c.σ.mem impurePtr.toNat] leaf_body := by
    simp only [AccessPlan, leaf_body]
    chain_facts True.intro
    apply (show ReadWindow impurePtr 8 from ⟨by decide, by decide, Or.inr (by decide)⟩).ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leaf_input, impurePtr]
  have control : TermFactsO (runGM leaf_body (leaf_input R) [read8 c.σ.mem impurePtr.toNat]) (some leaf_term) := by
    rw [leaf_eval]
    exact return_facts _ rfl rfl rfl rfl h.aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leaf_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change Sail.BitVec.update (R 1 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = R 1
    exact ret_tgt (R 1) h.aligned
  · exact leaf_eval R _
  · rfl
  · decide

end Errno

namespace LeaveBlocking

def enterLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 16#64 + 8#64).toNat, 8, R 1), ((R 2 - 16#64).toNat, 8, R 8)]

theorem enter_log (R : Nat → BitVec 64) :
    (evalBlocks enter_blocks (SegEvalState.init (enter_input R) [])).log = enterLog R := by
  change [] ++ wlogM enter_body (enter_input R) [] = _
  simp only [List.nil_append, enter_body, wlogM, enter_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx16, ← BitVec.sub_eq_add_neg]
  simp only [show BitVec.signExtend 64 8#12 = 8#64 by decide, show BitVec.signExtend 64 0#12 = 0#64 by decide,
    BitVec.add_zero]
  rfl

theorem enter_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (enter_input R))
    (low : WriteWindow (R 2 - 16#64) 8) (high : WriteWindow (R 2 - 16#64 + 8#64) 8)
    (outside : ImageOutside (enterLog R)) :
    FnSummary 0x8000d4b8#64 (fun d => d = c)
      (WriteRegistersPost [2] (enterLog R) c enter_call.pc (R 10) (enter_regs R [])) := by
  have access : AccessPlan c.σ.mem (enter_input R) [] enter_body := by
    simp only [AccessPlan, enter_body]
    chain_facts True.intro
    · apply high.sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply low.sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
  apply registers_of_blocks h.image outside (enter_summary c (R 1) R [] h regs access True.intro)
  · exact enter_log R
  · rfl
  · exact enter_eval R []
  · rfl
  · decide

/-- Load the leave hook and the saved `errno` (through `__errno`'s result in a0). -/
def hookLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 m leaveHook.toNat, read8 m (R 10).toNat]

theorem hook_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (hook_input R)) (errno : ReadWindow (R 10) 4) :
    FnSummary 0x8000d4c8#64 (fun d => d = c)
      (WriteRegistersPost [8, 15] [] c hook_call.pc (R 10) (hook_regs R (hookLoads c.σ.mem R))) := by
  have access : AccessPlan c.σ.mem (hook_input R) (hookLoads c.σ.mem R) hook_body := by
    simp only [AccessPlan, hook_body, hookLoads]
    chain_facts True.intro
    · apply (show ReadWindow leaveHook 8 from ⟨by decide, by decide, Or.inr (by decide)⟩).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, hook_input, leaveHook]
    · apply ReadWindow.lw errno rfl ?_ (read8_pins4 _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, hook_input]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (hook_summary c (R 1) R _ h regs access True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact hook_eval R _
  · rfl
  · decide

theorem scan_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (scan_input R)) :
    FnSummary 0x8000d4d8#64 (fun d => d = c)
      (WriteRegistersPost [12, 13, 15] [] c 0x8000d4f0#64 (R 10) (scan_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (scan_summary c (R 1) R [] h regs (by simp only [AccessPlan, scan_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact scan_eval R _
  · rfl
  · decide

theorem more_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (more_input R))
    (ne : R 15 ≠ R 12) :
    FnSummary 0x8000d4ec#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x8000d4f0#64 (R 10) (more_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (more_summary c (R 1) R [] h regs trivial (by rw [more_eval]; simp [TermFactsO, TermFactsT, more_term, more_regs, srcVal, lookupG, guardB, ne]))
  · rfl
  · rfl
  · exact more_eval R _
  · rfl
  · decide

theorem last_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (last_input R))
    (eq : R 15 = R 12) :
    FnSummary 0x8000d4ec#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x8000d528#64 (R 10) (last_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (last_summary c (R 1) R [] h regs trivial (by rw [last_eval]; simp [TermFactsO, TermFactsT, last_term, last_regs, srcVal, lookupG, guardB, eq]))
  · rfl
  · rfl
  · exact last_eval R _
  · rfl
  · decide

/-- One pending-signal slot: `caml_pending_signals[i]` is zero. -/
def slotAddress (R : Nat → BitVec 64) : BitVec 64 := R 13 + Sail.shift_bits_left (R 15) 3#6

theorem slot_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (slot_input R)) (window : ReadWindow (slotAddress R) 8)
    (clear : bytesVal .ld (read8 c.σ.mem (slotAddress R).toNat) = 0#64) :
    FnSummary 0x8000d4f0#64 (fun d => d = c)
      (WriteRegistersPost [14, 15] [] c 0x8000d4ec#64 (R 10) (slot_regs R [read8 c.σ.mem (slotAddress R).toNat])) := by
  have access : AccessPlan c.σ.mem (slot_input R) [read8 c.σ.mem (slotAddress R).toNat] slot_body := by
    simp only [AccessPlan, slot_body]
    chain_facts True.intro
    apply window.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, slot_input, slotAddress, shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_left]
  have control : TermFactsO (runGM slot_body (slot_input R) [read8 c.σ.mem (slotAddress R).toNat]) (some slot_term) := by
    rw [slot_eval]
    simp [TermFactsO, TermFactsT, slot_term, slot_regs, srcVal, lookupG, guardB, clear]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (slot_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact slot_eval R _
  · rfl
  · decide

theorem errno_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (errno_input R)) :
    FnSummary 0x8000d528#64 (fun d => d = c)
      (WriteRegistersPost [] [] c errno_call.pc (R 10) (errno_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (errno_summary c (R 1) R [] h regs trivial True.intro)
  · rfl
  · rfl
  · exact errno_eval R _
  · rfl
  · decide

/-- Restore the saved `errno`, reload ra and s0, and return. -/
def retLog (R : Nat → BitVec 64) : List WEntry := [((R 10).toNat, 4, R 8)]

def retLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 (writeLog m (retLog R)) (R 2 + 8#64).toNat, read8 (writeLog m (retLog R)) (R 2).toNat]

theorem ret_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks ret_blocks (SegEvalState.init (ret_input R) loads)).log = retLog R := by
  change [] ++ wlogM ret_body (ret_input R) loads = _
  simp only [List.nil_append, ret_body, wlogM, ret_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  simp only [show BitVec.signExtend 64 0#12 = 0#64 by decide, BitVec.add_zero]
  rfl

theorem ret_fast (c : Config) (ra : BitVec 64) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (ret_input R))
    (errno : WriteWindow (R 10) 4) (high : ReadWindow (R 2 + 8#64) 8) (low : ReadWindow (R 2) 8)
    (outside : ImageOutside (retLog R))
    (savedRa : bytesVal .ld (read8 (writeLog c.σ.mem (retLog R)) (R 2 + 8#64).toNat) = ra)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000d52c#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8] (retLog R) c ra (R 10) (ret_regs R (retLoads c.σ.mem R))) := by
  have access : AccessPlan c.σ.mem (ret_input R) (retLoads c.σ.mem R) ret_body := by
    simp only [AccessPlan, ret_body, retLoads]
    chain_facts True.intro
    · apply WriteWindow.sw errno rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, ret_input]
    · apply high.ld rfl
      · simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
            Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, ret_input]
      · apply ArgvTuple.lpins8_of_view (m' := writeLog c.σ.mem (retLog R))
        · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
            ret_input, Functions.sign_extend, Sail.BitVec.signExtend, writeLog, retLog]
        · rfl
    · apply low.ld rfl
      · simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
            Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, ret_input]
      · apply ArgvTuple.lpins8_of_view (m' := writeLog c.σ.mem (retLog R))
        · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
            ret_input, Functions.sign_extend, Sail.BitVec.signExtend, writeLog, retLog]
        · rfl
  have control : TermFactsO (runGM ret_body (ret_input R) (retLoads c.σ.mem R)) (some ret_term) := by
    rw [ret_eval]
    exact return_facts _ rfl rfl rfl (by simpa [ret_regs, srcVal, lookupG, retLoads] using savedRa) aligned
  apply registers_of_blocks h.image outside (ret_summary c (R 1) R _ h regs access control)
  · exact ret_log R _
  · change tgtPCT ret_term (runGM ret_body (ret_input R) (retLoads c.σ.mem R)) = ra
    rw [ret_eval]
    change Sail.BitVec.update (bytesVal .ld ((retLoads c.σ.mem R).getD 0 []) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra
    simp only [retLoads, List.getD_cons_zero]
    rw [savedRa]
    exact ret_tgt ra aligned
  · exact ret_eval R _
  · rfl
  · decide

end LeaveBlocking

end OCaml.Vm.Primitives.FdWrite
