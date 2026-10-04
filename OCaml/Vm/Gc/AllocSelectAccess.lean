import OCaml.Vm.Gc.Generated.AllocSelect
import OCaml.Vm.Primitives.Word32Access

namespace OCaml.Vm.Gc.AllocSelect
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def early (phase : BitVec 64) := decide (phase.toNat ≤ Layout.phase_clean)
def sweeping (phase : BitVec 64) := decide (phase = BitVec.ofNat 64 Layout.phase_sweep)
def beforeSweep (hp sweep : BitVec 64) := decide (hp.toNat < sweep.toNat)

theorem entry_access (R : Nat → BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8))
    (a : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (window : ReadWindow (R 2 + BitVec.ofNat 64 AllocEntry.tagOffset) 8)
    (pins : LPins8 mem (R 2 + BitVec.ofNat 64 AllocEntry.tagOffset).toNat a) :
    AccessPlan mem (regs R) (a::rest) entryBlock.body := by
  simp only [entryBlock,caml_alloc_shr_for_minor_gcXb79cFSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  exact window.ld rfl rfl pins

theorem entry_control (R : Nat → BitVec 64) (a : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (nonnull : R 10 ≠ 0) :
    TermFactsO (runGM entryBlock.body (regs R) (a::rest)) entryBlock.term := by
  rw [entry_regs]
  simpa [entryBlock,caml_alloc_shr_for_minor_gcXb79cFSeg,TermFactsO,TermFactsT,tagged,srcVal,lookupG,guardB] using nonnull

theorem phase_window : ReadWindow (BitVec.ofNat 64 Layout.sym_caml_gc_phase) 4 := by constructor <;> decide

theorem phase_access (flag : Bool) (R : Nat → BitVec 64) (tag : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (a : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (pins : LPins4 mem Layout.sym_caml_gc_phase a) :
    AccessPlan mem (tagged R tag) (a::rest) (phaseBlock flag).body := by
  cases flag
  all_goals simp only [phaseBlock,Bool.false_eq_true,eq_self,ite_false,ite_true,
    caml_alloc_shr_for_minor_gcXb7a4FSeg,caml_alloc_shr_for_minor_gcXb7a4TSeg,List.getD_cons_zero,AccessPlan]
  all_goals chain_facts True.intro
  all_goals apply phase_window.lw rfl ?_ pins
  all_goals simp [eaddrM,mkLine,decodeM,tagged,srcVal,lookupG,eraseG,stepGM,wvalM,imm20Of,
    Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_gc_phase]

theorem phase_control (R : Nat → BitVec 64) (tag : BitVec 64)
    (a : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    TermFactsO (runGM (phaseBlock (early (bytesVal .lw a))).body (tagged R tag) (a::rest))
      (phaseBlock (early (bytesVal .lw a))).term := by
  rw [phase_regs]
  generalize he : early (bytesVal .lw a) = flag
  cases flag
  · have h : ¬ (bytesVal .lw a).toNat ≤ Layout.phase_clean := of_decide_eq_false he
    simp [phaseBlock,caml_alloc_shr_for_minor_gcXb7a4FSeg,TermFactsO,TermFactsT,phased,
      srcVal,lookupG,guardB,Functions.zopz0zKzJ_u,Sail.BitVec.toNatInt]
    change ¬ (bytesVal .lw a).toNat ≤ 1 at h
    omega
  · have h : (bytesVal .lw a).toNat ≤ Layout.phase_clean := of_decide_eq_true he
    simp [phaseBlock,caml_alloc_shr_for_minor_gcXb7a4TSeg,TermFactsO,TermFactsT,phased,
      srcVal,lookupG,guardB,Functions.zopz0zKzJ_u,Sail.BitVec.toNatInt]
    change (bytesVal .lw a).toNat ≤ 1 at h
    omega

theorem test_access (flag : Bool) (R : Nat → BitVec 64) (tag phase : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (lds : List (List (BitVec 8))) :
    AccessPlan mem (phased R tag phase) lds (testBlock flag).body := by
  cases flag
  all_goals simp only [testBlock,Bool.false_eq_true,eq_self,ite_false,ite_true,
    caml_alloc_shr_for_minor_gcXb7b4FSeg,caml_alloc_shr_for_minor_gcXb7b4TSeg,List.getD_cons_zero,AccessPlan]
  all_goals chain_facts True.intro

theorem test_control (R : Nat → BitVec 64) (tag phase : BitVec 64) (lds : List (List (BitVec 8))) :
    TermFactsO (runGM (testBlock (sweeping phase)).body (phased R tag phase) lds) (testBlock (sweeping phase)).term := by
  rw [test_regs]
  generalize he : sweeping phase = flag
  cases flag
  · have h : phase ≠ BitVec.ofNat 64 Layout.phase_sweep := of_decide_eq_false he
    simpa [testBlock,caml_alloc_shr_for_minor_gcXb7b4FSeg,TermFactsO,TermFactsT,tested,srcVal,lookupG,guardB,Layout.phase_sweep] using h
  · have h : phase = BitVec.ofNat 64 Layout.phase_sweep := of_decide_eq_true he
    simpa [testBlock,caml_alloc_shr_for_minor_gcXb7b4FSeg,caml_alloc_shr_for_minor_gcXb7b4TSeg,
    TermFactsO,TermFactsT,tested,srcVal,lookupG,guardB,Layout.phase_sweep] using h

theorem sweep_window : ReadWindow (BitVec.ofNat 64 Layout.sym_caml_gc_sweep_hp) 8 := by constructor <;> decide

theorem sweep_access (flag : Bool) (R : Nat → BitVec 64) (tag phase : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (a : List (BitVec 8))
    (pins : LPins8 mem Layout.sym_caml_gc_sweep_hp a) :
    AccessPlan mem (tested R tag phase) [a] (sweepBlock flag).body := by
  cases flag
  all_goals simp only [sweepBlock,Bool.false_eq_true,eq_self,ite_false,ite_true,
    caml_alloc_shr_for_minor_gcXb82cFSeg,caml_alloc_shr_for_minor_gcXb82cTSeg,List.getD_cons_zero,AccessPlan]
  all_goals chain_facts True.intro
  all_goals apply sweep_window.ld rfl ?_ pins
  all_goals simp [eaddrM,mkLine,decodeM,tested,srcVal,lookupG,eraseG,stepGM,wvalM,imm20Of,
    Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_gc_sweep_hp]

theorem sweep_control (R : Nat → BitVec 64) (tag phase : BitVec 64) (a : List (BitVec 8)) :
    TermFactsO (runGM (sweepBlock (beforeSweep (R 10) (bytesVal .ld a))).body (tested R tag phase) [a])
      (sweepBlock (beforeSweep (R 10) (bytesVal .ld a))).term := by
  rw [sweep_regs]
  generalize he : beforeSweep (R 10) (bytesVal .ld a) = flag
  have choice := he
  simp only [beforeSweep] at choice
  cases flag
  all_goals simp [sweepBlock,caml_alloc_shr_for_minor_gcXb82cFSeg,caml_alloc_shr_for_minor_gcXb82cTSeg,
    TermFactsO,TermFactsT,swept,srcVal,lookupG,guardB,Functions.zopz0zI_u,Sail.BitVec.toNatInt]
  all_goals simp only [decide_eq_false_iff_not,decide_eq_true_eq] at choice
  all_goals omega

end OCaml.Vm.Gc.AllocSelect
