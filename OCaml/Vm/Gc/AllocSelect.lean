import OCaml.Vm.Gc.AllocSelectAccess
import OCaml.Vm.Gc.AllocColor

namespace OCaml.Vm.Gc.AllocSelect
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def tagAddr (R : Nat → BitVec 64) := R 2 + BitVec.ofNat 64 AllocEntry.tagOffset
def tag (R : Nat → BitVec 64) (c : Config) := word c (tagAddr R).toNat
def phase (c : Config) := bytesVal .lw (read4 c.σ.mem Layout.sym_caml_gc_phase)
def sweep (c : Config) := word c Layout.sym_caml_gc_sweep_hp

def loads (R : Nat → BitVec 64) (c : Config) :=
  [read8 c.σ.mem (tagAddr R).toNat,read4 c.σ.mem Layout.sym_caml_gc_phase,read8 c.σ.mem Layout.sym_caml_gc_sweep_hp]
def selected (R : Nat → BitVec 64) (c : Config) := blocks (early (phase c)) (sweeping (phase c)) (beforeSweep (R 10) (sweep c))
def isBlack (R : Nat → BitVec 64) (c : Config) := black (early (phase c)) (sweeping (phase c)) (beforeSweep (R 10) (sweep c))
def withTag (R : Nat → BitVec 64) (c : Config) (n : Nat) := if n = 11 then tag R c else R n

structure Input (R : Nat → BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  registers : GHolds c.σ (regs R)
  tagRead : ReadWindow (tagAddr R) 8
  nonnull : R 10 ≠ 0

theorem access {R c} (input : Input R c) : ChainAccess c.σ.mem (regs R) (loads R c) (selected R c) := by
  unfold selected blocks
  simp only [List.cons_append,List.nil_append]
  apply ChainAccess.cons ⟨entry_access _ _ _ _ input.tagRead (read8_pins _ _),entry_control _ _ _ input.nonnull⟩
  simp only [entry_regs,entry_loads,entry_log,writeLog,read8_value]
  apply ChainAccess.cons ⟨phase_access _ _ _ _ _ _ (read4_pins _ _),phase_control _ _ _ _⟩
  simp only [phase_regs,phase_loads,phase_log,writeLog]
  by_cases fast : early (phase c) = true
  · simp only [fast,ite_true]
    exact ChainAccess.nil
  · have slow : early (phase c) = false := Bool.eq_false_iff.mpr fast
    simp only [slow,ite_false,List.cons_append,List.nil_append]
    apply ChainAccess.cons ⟨test_access _ _ _ _ _ _,test_control _ _ _ _⟩
    simp only [test_regs,test_loads,test_log,writeLog]
    by_cases sweepingNow : sweeping (phase c) = true
    · simp only [sweepingNow,ite_true]
      apply ChainAccess.cons ⟨sweep_access _ _ _ _ _ _ (read8_pins _ _),?_⟩ ChainAccess.nil
      simpa only [phase,sweep,word,read8_value,tag,tagAddr,List.foldl] using sweep_control R (tag R c) (phase c)
        (read8 c.σ.mem Layout.sym_caml_gc_sweep_hp)
    · have idle : sweeping (phase c) = false := Bool.eq_false_iff.mpr sweepingNow
      simp only [idle,ite_false]
      exact ChainAccess.nil

/-- Only the selected tag pin is needed from the branch scratch registers. -/
theorem final_registers {R} {before after : Config} (holds : GHolds after.σ
    (evalBlocks (selected R before) (SegEvalState.init (regs R) (loads R before))).regs) :
    GHolds after.σ (AllocColor.regs (withTag R before)) := by
  unfold selected at holds
  generalize he : early (phase before) = e at holds
  generalize hs : sweeping (phase before) = s at holds
  generalize hb : beforeSweep (R 10) (sweep before) = b at holds
  cases e <;> cases s <;> cases b
  all_goals simp only [blocks,Bool.false_eq_true,eq_self,ite_false,ite_true,List.cons_append,List.nil_append,
    loads,evalBlocks,evalBlock,SegEvalState.init,entry_regs,entry_loads,phase_regs,phase_loads,
    test_regs,test_loads,sweep_regs,read8_value] at holds
  all_goals exact ⟨gholds_lookup _ holds rfl,gholds_lookup _ holds rfl,
    gholds_lookup _ holds rfl,gholds_lookup _ holds rfl,True.intro⟩

/-- The actual phase/sweep path selects the header builder and restores
the tag saved across the free-list call, without writing memory. -/
structure Post (R : Nat → BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (selected R before) pc (regs R) (loads R before) before after
  pc : PCAt (AllocColor.pc (isBlack R before)) after
  memory : after.σ.mem = before.σ.mem
  registers : GHolds after.σ (AllocColor.regs (withTag R before))
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem

theorem select {R c} (input : Input R c) : FnSummary pc (fun d => d = c) (Post R c) := by
  have facts := chainPlan_facts (code_facts _ _ _ input.code) (access input)
  have summary := block_summary (selected R c) pc (regs R) (loads R c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [2,8,10]; decide,
      facts,chain_ok _ _ _,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory,selected,no_stores]; rfl
  refine ⟨post,?_,memory,final_registers post.regs,memory ▸ input.code⟩
  rw [PCAt,post.pc,selected,endpoint]
  rfl

end OCaml.Vm.Gc.AllocSelect
