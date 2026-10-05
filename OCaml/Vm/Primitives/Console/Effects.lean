import OCaml.Vm.Primitives.Console.Putchar
import OCaml.Vm.Primitives.ExitPath.Effects

/-! Effect wrappers of `_write`'s console-path blocks. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open Vsa.Machine Vsa.Sim LeanRV64DExecutable
open ExitPath (ReadWindow.lw read8_pins4 sx96)

def fsReady : BitVec 64 := BitVec.ofNat 64 Layout.sym_fs_ready

/-- `fds[fd].kind`: the first word of the 24-byte descriptor entry. -/
def kindAddress (fd : BitVec 64) : BitVec 64 := 2147896728#64 + (fd <<< 4 + fd <<< 3)

def entryLog (R : Nat → BitVec 64) : List WEntry :=
  [((R 2 - 96#64 + 80#64).toNat, 8, R 8), ((R 2 - 96#64 + 72#64).toNat, 8, R 9),
   ((R 2 - 96#64 + 64#64).toNat, 8, R 18), ((R 2 - 96#64 + 88#64).toNat, 8, R 1)]

theorem entry_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks entry_blocks (SegEvalState.init (entry_input R) loads)).log = entryLog R := by
  change [] ++ wlogM entry_body (entry_input R) loads = _
  simp only [List.nil_append, entry_body, wlogM, entry_input, wentryM, widthOfM, eaddrM, srcVal, stepGM, lookupG, eraseG, stepLdsM,
      Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,
      Functions.sign_extend, Sail.BitVec.signExtend]
  rw [sx96, ← BitVec.sub_eq_add_neg]
  simp only [show BitVec.signExtend 64 80#12 = 80#64 by decide, show BitVec.signExtend 64 72#12 = 72#64 by decide,
    show BitVec.signExtend 64 64#12 = 64#64 by decide, show BitVec.signExtend 64 88#12 = 88#64 by decide]
  rfl

theorem entry_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (entry_input R))
    (flag : ReadWindow fsReady 4)
    (slots : ∀ k ∈ [64, 72, 80, 88], WriteWindow (R 2 - 96#64 + BitVec.ofNat 64 k) 8)
    (outside : ImageOutside (entryLog R))
    (ready : bytesVal .lw (read8 c.σ.mem fsReady.toNat) ≠ 0#64) :
    FnSummary 0x80000d54#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 9, 15, 18] (entryLog R) c 0x80000d84#64 (R 10)
        (entry_regs R [read8 c.σ.mem fsReady.toNat])) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (entry_input R) [read8 c.σ.mem fsReady.toNat] entry_body := by
    simp only [AccessPlan, entry_body]
    chain_facts True.intro
    · apply ReadWindow.lw flag rfl ?_ (read8_pins4 _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, entry_input, fsReady, Layout.sym_fs_ready]
    · apply (w 80 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, entry_input]
    · apply (w 72 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, entry_input]
    · apply (w 64 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, entry_input]
    · apply (w 88 (by simp)).sd rfl
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, entry_input]
  have control : TermFactsO (runGM entry_body (entry_input R) [read8 c.σ.mem fsReady.toNat]) (some entry_term) := by
    rw [entry_eval]
    simp [TermFactsO, TermFactsT, entry_term, entry_regs, srcVal, lookupG, guardB, ready]
  apply registers_of_blocks h.image outside (entry_summary c (R 1) R _ h regs access control)
  · exact entry_log R _
  · rfl
  · exact entry_eval R _
  · rfl
  · decide

theorem range_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (range_input R))
    (fd : guardB .BLTU 31#64 (R 8) = false) :
    FnSummary 0x80000d84#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x80000d8c (R 10) (range_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (range_summary c (R 1) R [] h regs (by simp only [AccessPlan, range_body]; chain_facts True.intro) (by rw [range_eval]; simpa [TermFactsO, TermFactsT, range_term, range_regs, srcVal, lookupG] using fd))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact range_eval R _
  · rfl
  · decide

theorem kind_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (kind_input R))
    (slot : ReadWindow (kindAddress (R 8)) 4)
    (valid : guardB .BGEU 1#64 (bytesVal .lw (read8 c.σ.mem (kindAddress (R 8)).toNat)) = false) :
    FnSummary 0x80000d8c#64 (fun d => d = c)
      (WriteRegistersPost [11, 13, 14, 15, 16] [] c 0x80000db0#64 (R 10)
        (kind_regs R [read8 c.σ.mem (kindAddress (R 8)).toNat])) := by
  have access : AccessPlan c.σ.mem (kind_input R) [read8 c.σ.mem (kindAddress (R 8)).toNat] kind_body := by
    simp only [AccessPlan, kind_body]
    chain_facts True.intro
    apply ReadWindow.lw slot rfl ?_ (read8_pins4 _ _)
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, kind_input, kindAddress, shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_left]
  have control : TermFactsO (runGM kind_body (kind_input R) [read8 c.σ.mem (kindAddress (R 8)).toNat])
      (some kind_term) := by
    rw [kind_eval]
    simpa [TermFactsO, TermFactsT, kind_term, kind_regs, srcVal, lookupG] using valid
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (kind_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact kind_eval R _
  · rfl
  · decide

theorem console_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (console_input R))
    (notFile : guardB .BNE (R 13) 4#64 = true) :
    FnSummary 0x80000db0#64 (fun d => d = c)
      (WriteRegistersPost [12] [] c 0x80000f58 (R 10) (console_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (console_summary c (R 1) R [] h regs (by simp only [AccessPlan, console_body]; chain_facts True.intro) (by rw [console_eval]; simpa [TermFactsO, TermFactsT, console_term, console_regs, srcVal, lookupG] using notFile))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact console_eval R _
  · rfl
  · decide

theorem empty_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (empty_input R))
    (zero : R 9 = 0#64) :
    FnSummary 0x80000f58#64 (fun d => d = c)
      (WriteRegistersPost [11, 13, 14] [] c 0x80000f3c (R 10) (empty_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (empty_summary c (R 1) R [] h regs (by simp only [AccessPlan, empty_body]; chain_facts True.intro) (by rw [empty_eval]; simp [TermFactsO, TermFactsT, empty_term, empty_regs, srcVal, lookupG, guardB, zero]))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact empty_eval R _
  · rfl
  · decide

theorem start_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (start_input R))
    (nonzero : R 9 ≠ 0#64) :
    FnSummary 0x80000f58#64 (fun d => d = c)
      (WriteRegistersPost [11, 13, 14] [] c 0x80000f6c (R 10) (start_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (start_summary c (R 1) R [] h regs (by simp only [AccessPlan, start_body]; chain_facts True.intro) (by rw [start_eval]; simp [TermFactsO, TermFactsT, start_term, start_regs, srcVal, lookupG, guardB, nonzero]))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact start_eval R _
  · rfl
  · decide

theorem byte_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (byte_input R)) (slot : ReadWindow (R 11) 1) :
    FnSummary 0x80000f6c#64 (fun d => d = c)
      (WriteRegistersPost [11, 12, 15] [] c 0x80000f7c#64 (R 10)
        (byte_regs R [[(c.σ.mem[(R 11).toNat]?).getD 0]])) := by
  have access : AccessPlan c.σ.mem (byte_input R) [[(c.σ.mem[(R 11).toNat]?).getD 0]] byte_body := by
    simp only [AccessPlan, byte_body]
    chain_facts True.intro
    apply slot.lbu rfl ?_ rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, byte_input]
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (byte_summary c (R 1) R _ h regs access True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact byte_eval R _
  · rfl
  · decide

theorem again_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (again_input R))
    (more : R 13 ≠ R 11) :
    FnSummary 0x80000f80#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x80000f6c (R 10) (again_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (again_summary c (R 1) R [] h regs trivial (by rw [again_eval]; simp [TermFactsO, TermFactsT, again_term, again_regs, srcVal, lookupG, guardB, more]))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact again_eval R _
  · rfl
  · decide

theorem done_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (done_input R))
    (finished : R 13 = R 11) :
    FnSummary 0x80000f80#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x80000f84 (R 10) (done_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (done_summary c (R 1) R [] h regs trivial (by rw [done_eval]; simp [TermFactsO, TermFactsT, done_term, done_regs, srcVal, lookupG, guardB, finished]))
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact done_eval R _
  · rfl
  · decide

theorem jump_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (jump_input R)) :
    FnSummary 0x80000f84#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x80000f3c (R 10) (jump_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (jump_summary c (R 1) R [] h regs trivial True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact jump_eval R _
  · rfl
  · decide

theorem result_fast (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (result_input R)) :
    FnSummary 0x80000f3c#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c 0x80000f40 (R 9) (result_regs R [])) := by
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (result_summary c (R 1) R [] h regs (by simp only [AccessPlan, result_body]; chain_facts True.intro) True.intro)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · rfl
  · exact result_eval R _
  · rfl
  · decide

/-- The epilogue reloads the saved registers and returns. -/
def leaveLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (R 2 + 88#64).toNat, read8 m (R 2 + 80#64).toNat, read8 m (R 2 + 72#64).toNat,
   read8 m (R 2 + 64#64).toNat]

theorem leave_fast (c : Config) (ra : BitVec 64) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (leave_input R))
    (slots : ∀ k ∈ [64, 72, 80, 88], ReadWindow (R 2 + BitVec.ofNat 64 k) 8)
    (savedRa : bytesVal .ld (read8 c.σ.mem (R 2 + 88#64).toNat) = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80000f40#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 18] [] c ra (R 10) (leave_regs R (leaveLoads c.σ.mem R))) := by
  have w := fun k hk => slots k hk
  have access : AccessPlan c.σ.mem (leave_input R) (leaveLoads c.σ.mem R) leave_body := by
    simp only [AccessPlan, leave_body]
    chain_facts True.intro
    · apply (w 88 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 80 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 72 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
    · apply (w 64 (by simp)).ld rfl ?_ (read8_pins _ _)
      simp [eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.sub_eq_add_neg, leave_input]
  have control : TermFactsO (runGM leave_body (leave_input R) (leaveLoads c.σ.mem R)) (some leave_term) := by
    rw [leave_eval]
    exact return_facts _ rfl rfl rfl (by simpa [leave_regs, srcVal, lookupG, leaveLoads] using savedRa) aligned
  apply registers_of_blocks h.image (log := []) ⟨True.intro, True.intro⟩
    (leave_summary c (R 1) R _ h regs access control)
  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _
  · change tgtPCT leave_term (runGM leave_body (leave_input R) (leaveLoads c.σ.mem R)) = ra
    rw [leave_eval]
    change Sail.BitVec.update (bytesVal .ld ((leaveLoads c.σ.mem R).getD 0 []) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra
    simp only [leaveLoads, List.getD_cons_zero]
    rw [savedRa]
    exact ret_tgt ra aligned
  · exact leave_eval R _
  · rfl
  · decide

end OCaml.Vm.Primitives.ConsoleWrite
