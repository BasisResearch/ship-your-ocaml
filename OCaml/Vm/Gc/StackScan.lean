import OCaml.Vm.Gc.Generated.LocalRoots
import OCaml.Vm.Gc.Generated.LocalRootsSites
import OCaml.Vm.Gc.ChainPlan
import Vsa.Sim.ChainFactsTac

/-! # The VM-stack loop of `caml_oldify_local_roots`

`for (sp = extern_sp; sp < stack_high; sp++) caml_oldify_one(*sp, sp);`
One iteration from the loop head `0x8000c7b0`: the argument setup
(`a0 = *s0`, `a1 = s0`, `s0 += 8`), the `jal caml_oldify_one` site
(`LocalRootsSites.stackSite`), and the bound test (`Caml_state`, then
`stack_high`, then `bltu s0, stack_high`). -/
namespace OCaml.Vm.Gc.StackScan
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def bodyBlock : BBlock := caml_oldify_local_rootsXc7b0Seg.getD 0 {body := [], term := none}
def bodyPc : BitVec 64 := 0x8000c7b0#64

def bodyRegs (p : BitVec 64) : GRegs := [(8, p)]
def bodyLoads (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) := [read8 m p.toNat]

theorem body_chain_ok : ChainOK bodyPc [8] [bodyBlock] := by decide

theorem body_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_oldify_local_rootsLoaded mem) :
    ChainCode mem [bodyBlock] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  constructor
  all_goals simp only [bodyBlock, caml_oldify_local_rootsXc7b0Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_oldify_local_roots_at_"

theorem body_access (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (window : ReadWindow p 8) :
    ChainAccess m (bodyRegs p) (bodyLoads p m) [bodyBlock] := by
  apply ChainAccess.cons ⟨?_, by simp [bodyBlock, caml_oldify_local_rootsXc7b0Seg, TermFactsO]⟩ ChainAccess.nil
  simp only [bodyBlock, caml_oldify_local_rootsXc7b0Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  refine window.ld rfl ?_ (read8_pins _ _)
  simp [bodyRegs, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]

/-- After the setup: `a0 = *p`, `a1 = p`, `s0 = p + 8`. -/
def setRegs (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(8, p + 8#64), (11, p), (10, bytesT m p.toNat 8)]

theorem body_regs (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks [bodyBlock] (SegEvalState.init (bodyRegs p) (bodyLoads p m))).regs = setRegs p m := by
  simp [evalBlocks, evalBlock, SegEvalState.init, bodyBlock, caml_oldify_local_rootsXc7b0Seg, bodyRegs,
    bodyLoads, setRegs, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, read8_value,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem body_log (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks [bodyBlock] (SegEvalState.init (bodyRegs p) (bodyLoads p m))).log = [] := rfl

theorem body_endpoint (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    evalBlocksPC bodyPc (SegEvalState.init (bodyRegs p) (bodyLoads p m)) [bodyBlock] =
      LocalRootsSites.stackCall.pc := rfl

theorem body_written : ∀ n ∈ wrChain [bodyBlock], n ∈ [8, 10, 11] := by decide

/-! ## The bound test at `0x8000c7c0` -/

def testPc : BitVec 64 := 0x8000c7c0#64
def exitPc : BitVec 64 := 0x8000c7cc#64

/-- The address of the `Caml_state` global, held in `s1`. -/
def statePtr : BitVec 64 := BitVec.ofNat 64 Layout.sym_Caml_state

def testBlock (taken : Bool) : BBlock :=
  if taken then caml_oldify_local_rootsXc7c0TSeg.getD 0 {body := [], term := none}
  else caml_oldify_local_rootsXc7c0FSeg.getD 0 {body := [], term := none}

def testRegs (s0 : BitVec 64) : GRegs := [(9, statePtr), (8, s0)]

/-- The domain record, then `stack_high`. -/
def testLoads (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m Layout.sym_Caml_state,
   read8 m (bytesT m Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high).toNat]

def stackHigh (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 :=
  bytesT m (bytesT m Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high).toNat 8

/-- The loop continues while `s0 < stack_high` (unsigned). -/
def continues (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Bool :=
  decide (s0.toNat < (stackHigh m).toNat)

theorem test_chain_ok (taken : Bool) : ChainOK testPc [9, 8] [testBlock taken] := by
  cases taken <;> decide

theorem test_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_oldify_local_rootsLoaded mem)
    (taken : Bool) : ChainCode mem [testBlock taken] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  cases taken <;> constructor
  all_goals simp only [testBlock, caml_oldify_local_rootsXc7c0TSeg, caml_oldify_local_rootsXc7c0FSeg,
    List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_oldify_local_roots_at_"

/-- After the loads: `a5 = Caml_state`, `a4 = stack_high`. -/
def testedRegs (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(14, stackHigh m), (15, bytesT m Layout.sym_Caml_state 8), (9, statePtr), (8, s0)]

theorem test_regs (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (taken : Bool) :
    runGM (testBlock taken).body (testRegs s0) (testLoads m) = testedRegs s0 m := by
  cases taken <;>
  simp [testBlock, caml_oldify_local_rootsXc7c0TSeg, caml_oldify_local_rootsXc7c0FSeg, testRegs, testLoads,
    testedRegs, stackHigh, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    read8_value, Functions.sign_extend, Sail.BitVec.signExtend]

theorem test_control (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    TermFactsO (runGM (testBlock (continues s0 m)).body (testRegs s0) (testLoads m))
      (testBlock (continues s0 m)).term := by
  rw [test_regs]
  generalize chosen : continues s0 m = taken
  cases taken
  · have no : ¬ s0.toNat < (stackHigh m).toNat := of_decide_eq_false chosen
    simp [testBlock, caml_oldify_local_rootsXc7c0FSeg, TermFactsO, TermFactsT, testedRegs, srcVal, lookupG,
      guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt, no]
  · have yes : s0.toNat < (stackHigh m).toNat := of_decide_eq_true chosen
    simp [testBlock, caml_oldify_local_rootsXc7c0TSeg, TermFactsO, TermFactsT, testedRegs, srcVal, lookupG,
      guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt, yes]

theorem test_access (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (stateRead : ReadWindow statePtr 8)
    (highRead : ReadWindow (bytesT m Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high) 8) :
    ChainAccess m (testRegs s0) (testLoads m) [testBlock (continues s0 m)] := by
  apply ChainAccess.cons ⟨?_, test_control s0 m⟩ ChainAccess.nil
  generalize continues s0 m = taken
  cases taken <;>
  simp only [testBlock, caml_oldify_local_rootsXc7c0TSeg, caml_oldify_local_rootsXc7c0FSeg,
    List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true] <;>
  chain_facts True.intro
  all_goals first
    | refine stateRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend,
        Sail.BitVec.signExtend]
    | refine highRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, testLoads, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, stepLdsM, wvalM,
        eraseG, read8_value, Layout.off_stack_high, Functions.sign_extend, Sail.BitVec.signExtend]

theorem test_endpoint (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    evalBlocksPC testPc (SegEvalState.init (testRegs s0) (testLoads m)) [testBlock (continues s0 m)] =
      if continues s0 m then bodyPc else exitPc := by
  generalize chosen : continues s0 m = taken
  cases taken <;> rfl

theorem test_log (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (taken : Bool) :
    (evalBlocks [testBlock taken] (SegEvalState.init (testRegs s0) (testLoads m))).log = [] := by
  cases taken <;> rfl

theorem test_written (taken : Bool) : ∀ n ∈ wrChain [testBlock taken], n ∈ [14, 15] := by
  cases taken <;> decide

/-! ## One iteration -/

/-- The loop's registers at the head: `sp`, `s0 = p`, `s1 = &Caml_state`, and
the callee-saved `s2`–`s9` (`R`). -/
def headRegs (R : Nat → BitVec 64) (p : BitVec 64) : GRegs :=
  [(2, R 2), (8, p), (9, statePtr), (18, R 18), (19, R 19), (20, R 20), (21, R 21),
   (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

/-- The callee's argument view for slot `p` (`a0 = *p`, `a1 = p`, `s0 = p + 8`). -/
def calleeR (R : Nat → BitVec 64) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) : BitVec 64 :=
  if n = 8 then p + 8#64 else if n = 9 then statePtr else if n = 10 then bytesT m p.toNat 8
  else if n = 11 then p else R n

structure HeadInput (R : Nat → BitVec 64) (p : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Code.Caml_oldify_local_rootsLoaded c.σ.mem
  pc : PCAt bodyPc c
  registers : GHolds c.σ (headRegs R p)
  window : ReadWindow p 8

/-- The callee's state at its entry, as the caller sees it. -/
structure Jumped (R : Nat → BitVec 64) (p : BitVec 64) (c e : Config) : Prop where
  memory : e.σ.mem = c.σ.mem
  registers : GHolds e.σ (OldifyEntry.regs (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)))
  good : GoodState e.σ
  tick : e.tick < 2
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w

/-- What the loop needs of the callee's effect: its code and the domain's
`stack_high` read stay in place. -/
structure CalleeFrame (c mid : Config) : Prop where
  code : Code.Caml_oldify_local_rootsLoaded mid.σ.mem
  stateRead : ReadWindow statePtr 8
  highRead : ReadWindow (bytesT mid.σ.mem Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high) 8

/-- One iteration returned: the slot call's result `mid`, then the bound test. -/
structure Iterated (R : Nat → BitVec 64) (p : BitVec 64) (copies : List PendingCopy) (pl : Place)
    (c after : Config) : Prop where
  slot : ∃ e copies' mid, Jumped R p c e ∧
    SlotDone (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid ∧
    after.σ.mem = mid.σ.mem ∧ PCAt (if continues (p + 8#64) mid.σ.mem then bodyPc else exitPc) after
  registers : GHolds after.σ (headRegs R (p + 8#64))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w

/-- The head registers other than `s0`, untouched by the setup block. -/
def keptRegs (R : Nat → BitVec 64) : GRegs :=
  [(2, R 2), (9, statePtr), (18, R 18), (19, R 19), (20, R 20), (21, R 21),
   (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

theorem kept_of_head {R p} {σ : MState} (h : GHolds σ (headRegs R p)) : GHolds σ (keptRegs R) := by
  apply gholds_select h
  intro n v member
  simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem body_frame {R : Nat → BitVec 64} {before after : MState}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ wrChain [bodyBlock], (gprReg n == r) = false) → after.regs.get? r = before.regs.get? r)
    (holds : GHolds before (keptRegs R)) : GHolds after (keptRegs R) := by
  apply gholds_of_frame frame _ (by change KeysOK [2,9,18,19,20,21,22,23,24,25]; decide) ?_ ?_ holds
  · change ∀ n ∈ [2,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · intro n hn m hm
    have small := body_written m hm
    simp only [keptRegs, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn small
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases small with rfl | rfl | rfl <;> decide

theorem carried_at_call {R p} {m : Std.ExtHashMap Nat (BitVec 8)} {σ : MState}
    (set : GHolds σ (setRegs p m)) (kept : GHolds σ (keptRegs R)) :
    GHolds σ (OldifyBridge.carried (calleeR R p m)) := by
  have both : GHolds σ (setRegs p m ++ keptRegs R) := (gholds_append _ _).mpr ⟨set, kept⟩
  apply gholds_select both
  intro n v member
  simp only [OldifyBridge.carried, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    simp [setRegs, keptRegs, calleeR, lookupG]

theorem head_of_returned {R p} {m : Std.ExtHashMap Nat (BitVec 8)} {σ : MState}
    (holds : GHolds σ (OldifyEntry.callerRegs (LocalRootsSites.stackSite.linked (calleeR R p m)))) :
    GHolds σ (testRegs (p + 8#64)) ∧ GHolds σ (keptRegs R) := by
  constructor
  all_goals
    apply gholds_select holds
    intro n v member
    simp only [testRegs, keptRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  · rcases member with h | h <;> cases h <;>
      simp [OldifyEntry.callerRegs, OldifyReturn.slots, SlotSite.linked, calleeR, lookupG]
  · rcases member with h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [OldifyEntry.callerRegs, OldifyReturn.slots, SlotSite.linked, calleeR, lookupG]

theorem test_frame {R : Nat → BitVec 64} {q : BitVec 64} {taken : Bool} {before after : MState}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ wrChain [testBlock taken], (gprReg n == r) = false) → after.regs.get? r = before.regs.get? r)
    (holds : GHolds before (headRegs R q)) : GHolds after (headRegs R q) := by
  apply gholds_of_frame frame _ (by change KeysOK [2,8,9,18,19,20,21,22,23,24,25]; decide) ?_ ?_ holds
  · change ∀ n ∈ [2,8,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · intro n hn m hm
    have small := test_written taken m hm
    simp only [headRegs, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn small
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases small with rfl | rfl <;> decide

/-- **One iteration of the VM-stack loop**, from the head at `p` to the next
head (`p + 8`) or the loop exit. The callee is any `caml_oldify_one` route the
caller supplies (`supply`); `frame` is the callee effect the loop needs. -/
theorem iteration {R : Nat → BitVec 64} {p : BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (input : HeadInput R p c)
    (supply : ∀ e, Jumped R p c e → SlotCall (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies pl e)
    (frame : ∀ e copies' mid, Jumped R p c e →
      SlotDone (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid → CalleeFrame c mid) :
    FnSummary bodyPc (fun d => d = c) (Iterated R p copies pl c) := by
  have bodyHolds : GHolds c.σ (bodyRegs p) := ⟨gholds_lookup _ input.registers rfl, True.intro⟩
  have body := block_summary [bodyBlock] bodyPc (bodyRegs p) (bodyLoads p c.σ.mem) c
    ⟨input.good, input.minstret, bodyHolds, by change KeysOK [8]; decide,
      chainPlan_facts (body_code input.code) (body_access p c.σ.mem input.window), body_chain_ok, input.tick⟩
  constructor
  apply Vsa.Logic.Triple.seq body.run
  intro b bp
  have bmem : b.σ.mem = c.σ.mem := by rw [bp.memory, body_log]; rfl
  have set : GHolds b.σ (setRegs p c.σ.mem) := by simpa only [body_regs] using bp.regs
  have kept := body_frame bp.frame (kept_of_head input.registers)
  have carried := carried_at_call set kept
  have bpc : PCAt LocalRootsSites.stackSite.call.pc b := by
    rw [PCAt, bp.pc, body_endpoint]; rfl
  have call := LocalRootsSites.stackSite.slot (copies := copies) (pl := pl) (bmem ▸ input.code) bp.good bp.tick
    bp.minstret carried fun e called => supply e
      ⟨by rw [called.mem, bmem]; rfl, LocalRootsSites.stackSite.linked_regs called, called.good, called.tick,
        called.minstret⟩
  obtain ⟨mid, run2, ret⟩ := call.run b ⟨bpc, rfl⟩
  obtain ⟨e, copies', called, done⟩ := ret.entered
  have jumped : Jumped R p c e :=
    ⟨by rw [called.mem, bmem]; rfl, LocalRootsSites.stackSite.linked_regs called, called.good, called.tick,
      called.minstret⟩
  have fr := frame e copies' mid jumped done
  obtain ⟨log, returned⟩ := done.returned
  obtain ⟨testHolds, keptMid⟩ := head_of_returned returned.registers
  have test := block_summary [testBlock (continues (p + 8#64) mid.σ.mem)] testPc (testRegs (p + 8#64))
    (testLoads mid.σ.mem) mid
    ⟨returned.good, returned.minstret, testHolds, by change KeysOK [9, 8]; decide,
      chainPlan_facts (test_code fr.code _) (test_access (p + 8#64) mid.σ.mem fr.stateRead fr.highRead),
      test_chain_ok _, returned.tick⟩
  have midPc : PCAt testPc mid := by
    have h := returned.pc
    simp only [SlotSite.linked, ite_true] at h
    exact h
  obtain ⟨after, run3, tp⟩ := test.run mid ⟨midPc, rfl⟩
  have headMid : GHolds mid.σ (headRegs R (p + 8#64)) := by
    have both : GHolds mid.σ (testRegs (p + 8#64) ++ keptRegs R) := (gholds_append _ _).mpr ⟨testHolds, keptMid⟩
    apply gholds_select both
    intro n v member
    simp only [headRegs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [testRegs, keptRegs, lookupG]
  refine ⟨after, run2.trans run3, ⟨⟨e, copies', mid, jumped, done, ?_, ?_⟩,
    test_frame tp.frame headMid, tp.good, tp.tick, tp.minstret⟩⟩
  · rw [tp.memory, test_log]; rfl
  · rw [PCAt, tp.pc, test_endpoint]

end OCaml.Vm.Gc.StackScan
