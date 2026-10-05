import OCaml.Vm.Primitives.ExitPath.SysExit
import OCaml.Vm.Primitives.ExitPath.DoExit
import OCaml.Vm.Primitives.ExitPath.LibcExit
import OCaml.Vm.Primitives.ExitPath.ExitProcs
import OCaml.Vm.Primitives.ExitPath.HtifExit
import OCaml.Vm.Primitives.ExitPath.CamlDebugger
import OCaml.Vm.Primitives.ExitPath.CamlTerminateSignals
import OCaml.Vm.Primitives.ExitPath.RetargetLockAcquireRecursive
import OCaml.Vm.Primitives.ExitPath.RetargetLockReleaseRecursive
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.ArgvTupleFinished

/-! Effect wrappers of the generated exit-path blocks: each block's exact write
log, exit pc, `a0` and register interface, with its scalar accesses discharged
from windows and total-byte pins. -/
namespace OCaml.Vm.Primitives.ExitPath
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- `caml_sys_exit` untags its argument and truncates it to a C `int`. -/
def exitCode (v : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.extractLsb 31 0 (Functions.shift_bits_right_arith v 1#6))


/-- Small sign-extended store and load offsets, one finite certificate each. -/
theorem sx16 : BitVec.signExtend 64 4080#12 = -16#64 := by decide
theorem sx96 : BitVec.signExtend 64 4000#12 = -96#64 := by decide

namespace SysExit

def entryLog (R : Nat → BitVec 64) : List WEntry := [((R 2 - 16#64 + 8#64).toNat, 8, R 1)]

theorem entry_log (R : Nat → BitVec 64) :
    (evalBlocks entry_blocks (SegEvalState.init (entry_input R) [])).log = entryLog R := by
  change [] ++ wlogM entry_body (entry_input R) [] = _
  simp only [List.nil_append, entry_body, wlogM, entry_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx16, ← BitVec.sub_eq_add_neg, show BitVec.signExtend 64 8#12 = 8#64 by decide]
  rfl

theorem entry_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (entry_input R))
    (slot : WriteWindow (R 2 - 16#64 + 8#64) 8) (outside : ImageOutside (entryLog R)) :
    FnSummary 0x8001c7ac#64 (fun d => d = c)
      (WriteRegistersPost [2, 10] (entryLog R) c entry_call.pc (exitCode (R 10)) (entry_regs R [])) := by
  have access : AccessPlan c.σ.mem (entry_input R) [] entry_body := by
    simp only [AccessPlan, entry_body]
    chain_facts True.intro
    apply slot.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, entry_input]
  apply registers_of_blocks h.image outside (entry_summary c (R 1) R [] h regs access True.intro)
  · exact entry_log R
  · rfl
  · exact entry_eval R []
  · rfl
  · decide

end SysExit

/-- A 32-bit total load with its RAM and HTIF bounds. -/
theorem ReadWindow.lw {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : ReadWindow x 4)
    (kind : a.kind = .lw) (address : eaddrM a L = x) (pins : LPins4 m x.toNat bs) :
    MemFacts m L bs a := by
  simp only [MemFacts, kind, address]
  refine ⟨⟨h.lower, h.upper, ?_⟩, pins⟩
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using h.htif

theorem read8_pins4 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : LPins4 m a (read8 m a) := by
  simp [LPins4, read8]

def verbGc : BitVec 64 := BitVec.ofNat 64 Layout.sym_caml_verb_gc
def cleanupOnExit : BitVec 64 := BitVec.ofNat 64 Layout.sym_caml_cleanup_on_exit
def atexitList : BitVec 64 := BitVec.ofNat 64 Layout.sym_atexit
def atexitMutex : BitVec 64 := BitVec.ofNat 64 Layout.sym_atexit_recursive_mutex
def stdioExitHandler : BitVec 64 := BitVec.ofNat 64 Layout.sym_stdio_exit_handler

namespace DoExit

def saveLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 96#64 + 72#64).toNat, 8, R 9), ((R 2 - 96#64 + 88#64).toNat, 8, R 1),
   ((R 2 - 96#64 + 80#64).toNat, 8, R 8), ((R 2 - 96#64 + 64#64).toNat, 8, R 18),
   ((R 2 - 96#64 + 56#64).toNat, 8, R 19), ((R 2 - 96#64 + 48#64).toNat, 8, R 20),
   ((R 2 - 96#64 + 40#64).toNat, 8, R 21), ((R 2 - 96#64 + 32#64).toNat, 8, R 22),
   ((R 2 - 96#64 + 24#64).toNat, 8, R 23), ((R 2 - 96#64 + 16#64).toNat, 8, R 24),
   ((R 2 - 96#64 + 8#64).toNat, 8, R 25), ((R 2 - 96#64).toNat, 8, R 26)]

theorem save_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks save_blocks (SegEvalState.init (save_input R) loads)).log = saveLog R := by
  change [] ++ wlogM save_body (save_input R) loads = _
  simp only [List.nil_append, save_body, wlogM, save_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx96, ← BitVec.sub_eq_add_neg]
  simp only [show BitVec.signExtend 64 72#12 = 72#64 by decide, show BitVec.signExtend 64 88#12 = 88#64 by decide,
    show BitVec.signExtend 64 80#12 = 80#64 by decide, show BitVec.signExtend 64 64#12 = 64#64 by decide,
    show BitVec.signExtend 64 56#12 = 56#64 by decide, show BitVec.signExtend 64 48#12 = 48#64 by decide,
    show BitVec.signExtend 64 40#12 = 40#64 by decide, show BitVec.signExtend 64 32#12 = 32#64 by decide,
    show BitVec.signExtend 64 24#12 = 24#64 by decide, show BitVec.signExtend 64 16#12 = 16#64 by decide,
    show BitVec.signExtend 64 8#12 = 8#64 by decide, show BitVec.signExtend 64 0#12 = 0#64 by decide,
    BitVec.add_zero]
  rfl

theorem save_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (save_input R))
    (gc : ReadWindow verbGc 8)
    (slots : ∀ k ∈ [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88],
      WriteWindow (R 2 - 96#64 + BitVec.ofNat 64 k) 8)
    (outside : ImageOutside (saveLog R))
    (quiet : bytesVal .ld (read8 c.σ.mem verbGc.toNat) &&& 1024#64 = 0#64) :
    FnSummary 0x8001c5c8#64 (fun d => d = c)
      (WriteRegistersPost [2, 9, 15] (saveLog R) c 0x8001c610#64 (R 10)
        (save_regs R [read8 c.σ.mem verbGc.toNat])) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (save_input R) [read8 c.σ.mem verbGc.toNat] save_body := by
    simp only [AccessPlan, save_body]
    chain_facts True.intro
    · apply gc.ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input, verbGc, Layout.sym_caml_verb_gc]
    · apply (w 72 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 88 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 80 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 64 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 56 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 48 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 40 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 32 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 24 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 16 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 8 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
    · apply (w 0 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, save_input]
  have control : TermFactsO (runGM save_body (save_input R) [read8 c.σ.mem verbGc.toNat]) (some save_term) := by
    rw [save_eval]
    simp [TermFactsO, TermFactsT, save_term, save_regs, srcVal, lookupG, guardB, quiet]
  apply registers_of_blocks h.image outside (save_summary c (R 1) R _ h regs access control)
  · exact save_log R _
  · rfl
  · exact save_eval R _
  · rfl
  · decide

theorem debug_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (debug_input R)) :
    FnSummary 0x8001c610#64 (fun d => d = c)
      (WriteRegistersPost [10, 11] [] c debug_call.pc 3#64 (debug_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (debug_summary c (R 1) R [] h regs (by simp only [AccessPlan, debug_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact debug_eval R []
  · rfl
  · decide

theorem cleanup_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (cleanup_input R))
    (flag : ReadWindow cleanupOnExit 4)
    (noCleanup : bytesVal .lw (read8 c.σ.mem cleanupOnExit.toNat) = 0#64) :
    FnSummary 0x8001c61c#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x8001c628#64 (R 10) (cleanup_regs R [read8 c.σ.mem cleanupOnExit.toNat])) := by
  have access : AccessPlan c.σ.mem (cleanup_input R) [read8 c.σ.mem cleanupOnExit.toNat] cleanup_body := by
    simp only [AccessPlan, cleanup_body]
    chain_facts True.intro
    apply ReadWindow.lw flag rfl ?_ (read8_pins4 _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, cleanup_input, cleanupOnExit, Layout.sym_caml_cleanup_on_exit]
  have control : TermFactsO (runGM cleanup_body (cleanup_input R) [read8 c.σ.mem cleanupOnExit.toNat])
      (some cleanup_term) := by
    rw [cleanup_eval]
    simp [TermFactsO, TermFactsT, cleanup_term, cleanup_regs, srcVal, lookupG, guardB, noCleanup]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (cleanup_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact cleanup_eval R _
  · rfl
  · decide

theorem signals_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (signals_input R)) :
    FnSummary 0x8001c628#64 (fun d => d = c)
      (WriteRegistersPost [] [] c signals_call.pc (R 10) (signals_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (signals_summary c (R 1) R [] h regs trivial True.intro)
  · rfl
  · rfl
  · exact signals_eval R []
  · rfl
  · decide

theorem leave_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leave_input R)) :
    FnSummary 0x8001c62c#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c leave_call.pc (R 9) (leave_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leave_summary c (R 1) R [] h regs (by simp only [AccessPlan, leave_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact leave_eval R []
  · rfl
  · decide

end DoExit

namespace LibcExit

def enterLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 16#64).toNat, 8, R 8), ((R 2 - 16#64 + 8#64).toNat, 8, R 1)]

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
    FnSummary 0x800373c8#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 11] (enterLog R) c enter_call.pc (R 10) (enter_regs R [])) := by
  have access : AccessPlan c.σ.mem (enter_input R) [] enter_body := by
    simp only [AccessPlan, enter_body]
    chain_facts True.intro
    · apply low.sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply high.sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
  apply registers_of_blocks h.image outside (enter_summary c (R 1) R [] h regs access True.intro)
  · exact enter_log R
  · rfl
  · exact enter_eval R []
  · rfl
  · decide

theorem handler_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (handler_input R))
    (slot : ReadWindow stdioExitHandler 8)
    (noHandler : bytesVal .ld (read8 c.σ.mem stdioExitHandler.toNat) = 0#64) :
    FnSummary 0x800373e0#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x800373f0#64 (R 10) (handler_regs R [read8 c.σ.mem stdioExitHandler.toNat])) := by
  have access : AccessPlan c.σ.mem (handler_input R) [read8 c.σ.mem stdioExitHandler.toNat] handler_body := by
    simp only [AccessPlan, handler_body]
    chain_facts True.intro
    apply slot.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, handler_input, stdioExitHandler, Layout.sym_stdio_exit_handler]
  have control : TermFactsO (runGM handler_body (handler_input R) [read8 c.σ.mem stdioExitHandler.toNat])
      (some handler_term) := by
    rw [handler_eval]
    simp [TermFactsO, TermFactsT, handler_term, handler_regs, srcVal, lookupG, guardB, noHandler]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (handler_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact handler_eval R _
  · rfl
  · decide

theorem tail_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (tail_input R)) :
    FnSummary 0x800373f0#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c tail_call.pc (R 8) (tail_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (tail_summary c (R 1) R [] h regs (by simp only [AccessPlan, tail_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact tail_eval R []
  · rfl
  · decide

end LibcExit

namespace ExitProcs

def enterLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 96#64 + 24#64).toNat, 8, R 23), ((R 2 - 96#64 + 32#64).toNat, 8, R 22),
   ((R 2 - 96#64 + 48#64).toNat, 8, R 20), ((R 2 - 96#64 + 64#64).toNat, 8, R 18),
   ((R 2 - 96#64 + 16#64).toNat, 8, R 24), ((R 2 - 96#64 + 88#64).toNat, 8, R 1)]

/-- The mutex load follows the first two saves. -/
def enterLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 (writeLog m (enterLog R |>.take 2)) atexitMutex.toNat]

theorem enter_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks enter_blocks (SegEvalState.init (enter_input R) loads)).log = enterLog R := by
  change [] ++ wlogM enter_body (enter_input R) loads = _
  simp only [List.nil_append, enter_body, wlogM, enter_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx96, ← BitVec.sub_eq_add_neg]
  simp only [show BitVec.signExtend 64 24#12 = 24#64 by decide, show BitVec.signExtend 64 32#12 = 32#64 by decide,
    show BitVec.signExtend 64 48#12 = 48#64 by decide, show BitVec.signExtend 64 64#12 = 64#64 by decide,
    show BitVec.signExtend 64 16#12 = 16#64 by decide, show BitVec.signExtend 64 88#12 = 88#64 by decide]
  rfl

theorem enter_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (enter_input R))
    (mutex : ReadWindow atexitMutex 8)
    (slots : ∀ k ∈ [16, 24, 32, 48, 64, 88], WriteWindow (R 2 - 96#64 + BitVec.ofNat 64 k) 8)
    (outside : ImageOutside (enterLog R)) :
    FnSummary 0x80042d28#64 (fun d => d = c)
      (WriteRegistersPost [2, 10, 20, 22, 23, 24] (enterLog R) c enter_call.pc
        (bytesVal .ld (read8 (writeLog c.σ.mem (enterLog R |>.take 2)) atexitMutex.toNat))
        (enter_regs R (enterLoads c.σ.mem R))) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (enter_input R) (enterLoads c.σ.mem R) enter_body := by
    simp only [AccessPlan, enter_body]
    chain_facts True.intro
    · apply (w 24 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply (w 32 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply mutex.ld rfl
      · simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input, atexitMutex, Layout.sym_atexit_recursive_mutex]
      · apply ArgvTuple.lpins8_of_view (m' := writeLog c.σ.mem (enterLog R |>.take 2))
        · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of,
            enter_input, Functions.sign_extend, Sail.BitVec.signExtend, writeLog, enterLog, -BitVec.toNat_add]
          rw [show R 2 + 18446744073709551520#64 = R 2 - 96#64 by bv_omega]
        · rfl
    · apply (w 48 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply (w 64 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply (w 16 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
    · apply (w 88 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, enter_input]
  apply registers_of_blocks h.image outside (enter_summary c (R 1) R _ h regs access True.intro)
  · exact enter_log R _
  · rfl
  · exact enter_eval R _
  · rfl
  · decide


theorem empty_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (empty_input R)) (list : R 20 = atexitList)
    (slot : ReadWindow atexitList 8)
    (noAtexit : bytesVal .ld (read8 c.σ.mem atexitList.toNat) = 0#64) :
    FnSummary 0x80042d64#64 (fun d => d = c)
      (WriteRegistersPost [18] [] c 0x80042e04#64 (R 10) (empty_regs R [read8 c.σ.mem atexitList.toNat])) := by
  have access : AccessPlan c.σ.mem (empty_input R) [read8 c.σ.mem atexitList.toNat] empty_body := by
    simp only [AccessPlan, empty_body]
    chain_facts True.intro
    apply slot.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, empty_input, list]
  have control : TermFactsO (runGM empty_body (empty_input R) [read8 c.σ.mem atexitList.toNat])
      (some empty_term) := by
    rw [empty_eval]
    simp [TermFactsO, TermFactsT, empty_term, empty_regs, srcVal, lookupG, guardB, noAtexit]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (empty_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact empty_eval R _
  · rfl
  · decide

/-- The epilogue reloads the saved registers and tail-jumps to the lock release. -/
def leaveLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (R 23).toNat, read8 m (R 2 + 88#64).toNat, read8 m (R 2 + 64#64).toNat,
   read8 m (R 2 + 48#64).toNat, read8 m (R 2 + 32#64).toNat, read8 m (R 2 + 24#64).toNat,
   read8 m (R 2 + 16#64).toNat]

theorem leave_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leave_input R))
    (mutex : ReadWindow (R 23) 8)
    (slots : ∀ k ∈ [16, 24, 32, 48, 64, 88], ReadWindow (R 2 + BitVec.ofNat 64 k) 8) :
    FnSummary 0x80042e04#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 10, 18, 20, 22, 23, 24] [] c 0x80042550#64
        (bytesVal .ld (read8 c.σ.mem (R 23).toNat)) (leave_regs R (leaveLoads c.σ.mem R))) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (leave_input R) (leaveLoads c.σ.mem R) leave_body := by
    simp only [AccessPlan, leave_body]
    chain_facts True.intro
    · apply mutex.ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 88 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 64 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 48 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 32 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 24 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 16 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leave_summary c (R 1) R _ h regs access True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact leave_eval R _
  · rfl
  · decide

end ExitProcs

namespace HtifExit

theorem store_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (store_input R)) :
    FnSummary 0x800008a0#64 (fun d => d = c)
      (WriteRegistersPost [14, 15] [] c 0x800008b0#64 (R 10) (store_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (store_summary c (R 1) R [] h regs (by simp only [AccessPlan, store_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact store_eval R []
  · rfl
  · decide

end HtifExit

namespace CamlDebugger

/-- A one-instruction `ret` leaf returns with every register and all memory unchanged. -/
theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x80021618#64 (fun d => d = c)
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

end CamlDebugger

namespace CamlTerminateSignals

/-- A one-instruction `ret` leaf returns with every register and all memory unchanged. -/
theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x8000dbe8#64 (fun d => d = c)
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

end CamlTerminateSignals

namespace RetargetLockAcquireRecursive

/-- A one-instruction `ret` leaf returns with every register and all memory unchanged. -/
theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x80042538#64 (fun d => d = c)
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

end RetargetLockAcquireRecursive

namespace RetargetLockReleaseRecursive

/-- A one-instruction `ret` leaf returns with every register and all memory unchanged. -/
theorem leaf_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leaf_input R)) :
    FnSummary 0x80042550#64 (fun d => d = c)
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

end RetargetLockReleaseRecursive

end OCaml.Vm.Primitives.ExitPath
