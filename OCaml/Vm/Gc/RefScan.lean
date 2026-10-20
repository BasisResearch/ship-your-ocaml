import OCaml.Vm.Gc.Generated.EmptyMinorRefs
import OCaml.Vm.Gc.Generated.EmptyMinorRefsSites
import OCaml.Vm.Gc.ChainPlan
import OCaml.Vm.Gc.StackScan
import OCaml.Vm.Gc.LoopFold
import Vsa.Sim.ChainFactsTac

/-! # The remembered-set loop of `caml_empty_minor_heap`

`for (r = ref_table->base; r < ref_table->ptr; r++) caml_oldify_one(**r, *r);`
One iteration from the loop head `0x80009f90`: the argument setup
(`a1 = *s0`, `s0 += 8`, `a0 = *a1`), the `jal caml_oldify_one` site
(`EmptyMinorRefsSites.refsSite`), and the bound test (`Caml_state`, then its
`ref_table`, then `ptr`; `bltu s0, ptr`). As `StackScan`, with the slot read
through the table entry. -/
namespace OCaml.Vm.Gc.RefScan
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open StackScan (statePtr headRegs)

def bodyBlock : BBlock := caml_empty_minor_heapX9f90Seg.getD 0 {body := [], term := none}
def bodyPc : BitVec 64 := 0x80009f90#64

/-- The table entry at `e` (the slot's address). -/
def entry (m : Std.ExtHashMap Nat (BitVec 8)) (e : BitVec 64) : BitVec 64 := bytesT m e.toNat 8

def bodyRegs (e : BitVec 64) : GRegs := [(8, e)]
def bodyLoads (e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m e.toNat, read8 m (entry m e).toNat]

theorem body_chain_ok : ChainOK bodyPc [8] [bodyBlock] := by decide

theorem body_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_empty_minor_heapLoaded mem) :
    ChainCode mem [bodyBlock] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  constructor
  all_goals simp only [bodyBlock, caml_empty_minor_heapX9f90Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_empty_minor_heap_at_"

theorem body_access (e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (window : ReadWindow e 8)
    (slot : ReadWindow (entry m e) 8) : ChainAccess m (bodyRegs e) (bodyLoads e m) [bodyBlock] := by
  apply ChainAccess.cons ⟨?_, by simp [bodyBlock, caml_empty_minor_heapX9f90Seg, TermFactsO]⟩ ChainAccess.nil
  simp only [bodyBlock, caml_empty_minor_heapX9f90Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · refine window.ld rfl ?_ (read8_pins _ _)
    simp [bodyRegs, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · refine slot.ld rfl ?_ (read8_pins _ _)
    simp [bodyRegs, bodyLoads, entry, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, stepLdsM, wvalM, eraseG,
      read8_value, Functions.sign_extend, Sail.BitVec.signExtend]

/-- After the setup: `a0 = **e`, `s0 = e + 8`, `a1 = *e`. -/
def setRegs (e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(10, bytesT m (entry m e).toNat 8), (8, e + 8#64), (11, entry m e)]

theorem body_regs (e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks [bodyBlock] (SegEvalState.init (bodyRegs e) (bodyLoads e m))).regs = setRegs e m := by
  simp [evalBlocks, evalBlock, SegEvalState.init, bodyBlock, caml_empty_minor_heapX9f90Seg, bodyRegs,
    bodyLoads, setRegs, entry, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, read8_value,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem body_log (e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks [bodyBlock] (SegEvalState.init (bodyRegs e) (bodyLoads e m))).log = [] := rfl

theorem body_endpoint (e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    evalBlocksPC bodyPc (SegEvalState.init (bodyRegs e) (bodyLoads e m)) [bodyBlock] =
      EmptyMinorRefsSites.refsCall.pc := rfl

theorem body_written : ∀ n ∈ wrChain [bodyBlock], n ∈ [8, 10, 11] := by decide

/-! ## The bound test at `0x80009fa0` -/

def testPc : BitVec 64 := 0x80009fa0#64
def exitPc : BitVec 64 := 0x80009fb0#64

def testBlock (taken : Bool) : BBlock :=
  if taken then caml_empty_minor_heapX9fa0TSeg.getD 0 {body := [], term := none}
  else caml_empty_minor_heapX9fa0FSeg.getD 0 {body := [], term := none}

def testRegs (s0 : BitVec 64) : GRegs := [(9, statePtr), (8, s0)]

/-- `Caml_state->ref_table` and its `ptr`. -/
def refTable (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 :=
  bytesT m (bytesT m Layout.sym_Caml_state 8 + 104#64).toNat 8
def tablePtr (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (refTable m + 24#64).toNat 8

def testLoads (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m Layout.sym_Caml_state, read8 m (bytesT m Layout.sym_Caml_state 8 + 104#64).toNat,
   read8 m (refTable m + 24#64).toNat]

/-- The loop continues while `s0 < ptr` (unsigned). -/
def continues (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Bool := decide (s0.toNat < (tablePtr m).toNat)

theorem test_chain_ok (taken : Bool) : ChainOK testPc [9, 8] [testBlock taken] := by cases taken <;> decide

theorem test_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_empty_minor_heapLoaded mem)
    (taken : Bool) : ChainCode mem [testBlock taken] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  cases taken <;> constructor
  all_goals simp only [testBlock, caml_empty_minor_heapX9fa0TSeg, caml_empty_minor_heapX9fa0FSeg,
    List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_empty_minor_heap_at_"

def testedRegs (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(15, tablePtr m), (9, statePtr), (8, s0)]

theorem test_regs (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (taken : Bool) :
    runGM (testBlock taken).body (testRegs s0) (testLoads m) = testedRegs s0 m := by
  cases taken <;>
  simp [testBlock, caml_empty_minor_heapX9fa0TSeg, caml_empty_minor_heapX9fa0FSeg, testRegs, testLoads,
    testedRegs, tablePtr, refTable, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    read8_value, Functions.sign_extend, Sail.BitVec.signExtend]

theorem test_control (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    TermFactsO (runGM (testBlock (continues s0 m)).body (testRegs s0) (testLoads m))
      (testBlock (continues s0 m)).term := by
  rw [test_regs]
  generalize chosen : continues s0 m = taken
  cases taken
  · have no : ¬ s0.toNat < (tablePtr m).toNat := of_decide_eq_false chosen
    simp [testBlock, caml_empty_minor_heapX9fa0FSeg, TermFactsO, TermFactsT, testedRegs, srcVal, lookupG,
      guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt, no]
  · have yes : s0.toNat < (tablePtr m).toNat := of_decide_eq_true chosen
    simp [testBlock, caml_empty_minor_heapX9fa0TSeg, TermFactsO, TermFactsT, testedRegs, srcVal, lookupG,
      guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt, yes]

theorem test_access (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (stateRead : ReadWindow statePtr 8)
    (fieldRead : ReadWindow (bytesT m Layout.sym_Caml_state 8 + 104#64) 8)
    (ptrRead : ReadWindow (refTable m + 24#64) 8) :
    ChainAccess m (testRegs s0) (testLoads m) [testBlock (continues s0 m)] := by
  apply ChainAccess.cons ⟨?_, test_control s0 m⟩ ChainAccess.nil
  generalize continues s0 m = taken
  cases taken
  · simp only [testBlock, caml_empty_minor_heapX9fa0FSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true]
    chain_facts True.intro
    · refine stateRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend,
        Sail.BitVec.signExtend]
    · refine fieldRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, testLoads, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, stepLdsM, wvalM,
        eraseG, read8_value, Functions.sign_extend, Sail.BitVec.signExtend]
    · refine ptrRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, testLoads, refTable, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, stepLdsM,
        wvalM, eraseG, read8_value, Functions.sign_extend, Sail.BitVec.signExtend]
  · simp only [testBlock, caml_empty_minor_heapX9fa0TSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true]
    chain_facts True.intro
    · refine stateRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend,
        Sail.BitVec.signExtend]
    · refine fieldRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, testLoads, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, stepLdsM, wvalM,
        eraseG, read8_value, Functions.sign_extend, Sail.BitVec.signExtend]
    · refine ptrRead.ld rfl ?_ (read8_pins _ _)
      simp [testRegs, testLoads, refTable, statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, stepLdsM,
        wvalM, eraseG, read8_value, Functions.sign_extend, Sail.BitVec.signExtend]

theorem test_endpoint (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    evalBlocksPC testPc (SegEvalState.init (testRegs s0) (testLoads m)) [testBlock (continues s0 m)] =
      if continues s0 m then bodyPc else exitPc := by
  generalize continues s0 m = taken
  cases taken <;> rfl

theorem test_log (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (taken : Bool) :
    (evalBlocks [testBlock taken] (SegEvalState.init (testRegs s0) (testLoads m))).log = [] := by
  cases taken <;> rfl

theorem test_written (taken : Bool) : ∀ n ∈ wrChain [testBlock taken], n ∈ [15] := by
  cases taken <;> decide

/-! ## One iteration -/

/-- The callee's argument view for entry `p` (`a0 = **p`, `a1 = *p`, `s0 = p + 8`). -/
def calleeR (R : Nat → BitVec 64) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) : BitVec 64 :=
  if n = 8 then p + 8#64 else if n = 9 then statePtr else if n = 10 then bytesT m (entry m p).toNat 8
  else if n = 11 then entry m p else R n

structure HeadInput (R : Nat → BitVec 64) (p : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Code.Caml_empty_minor_heapLoaded c.σ.mem
  pc : PCAt bodyPc c
  registers : GHolds c.σ (StackScan.headRegs R p)
  window : ReadWindow p 8
  slotRead : ReadWindow (entry c.σ.mem p) 8

/-- The callee's state at its entry, as the caller sees it. -/
structure Jumped (R : Nat → BitVec 64) (p : BitVec 64) (c e : Config) : Prop where
  memory : e.σ.mem = c.σ.mem
  registers : GHolds e.σ (OldifyEntry.regs (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)))
  good : GoodState e.σ
  tick : e.tick < 2
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w

/-- What the loop needs of the callee's effect: its code and the bound
test's reads stay in place. -/
structure CalleeFrame (c mid : Config) : Prop where
  code : Code.Caml_empty_minor_heapLoaded mid.σ.mem
  stateRead : ReadWindow statePtr 8
  fieldRead : ReadWindow (bytesT mid.σ.mem Layout.sym_Caml_state 8 + 104#64) 8
  ptrRead : ReadWindow (refTable mid.σ.mem + 24#64) 8

/-- One iteration returned: the slot call's result `mid`, then the bound test. -/
structure Iterated (R : Nat → BitVec 64) (p : BitVec 64) (copies : List PendingCopy) (pl : Place)
    (c after : Config) : Prop where
  slot : ∃ e copies' mid, Jumped R p c e ∧
    SlotDone (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid ∧
    after.σ.mem = mid.σ.mem ∧ PCAt (if continues (p + 8#64) mid.σ.mem then bodyPc else exitPc) after
  registers : GHolds after.σ (StackScan.headRegs R (p + 8#64))
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
    (holds : GHolds σ (OldifyEntry.callerRegs (EmptyMinorRefsSites.refsSite.linked (calleeR R p m)))) :
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
      rcases small with rfl <;> decide

/-- **One iteration of the VM-stack loop**, from the head at `p` to the next
head (`p + 8`) or the loop exit. The callee is any `caml_oldify_one` route the
caller supplies (`supply`); `frame` is the callee effect the loop needs. -/
theorem iteration {R : Nat → BitVec 64} {p : BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (input : HeadInput R p c)
    (supply : ∀ e, Jumped R p c e → SlotCall (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies pl e)
    (frame : ∀ e copies' mid, Jumped R p c e →
      SlotDone (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid → CalleeFrame c mid) :
    FnSummary bodyPc (fun d => d = c) (Iterated R p copies pl c) := by
  have bodyHolds : GHolds c.σ (bodyRegs p) := ⟨gholds_lookup _ input.registers rfl, True.intro⟩
  have body := block_summary [bodyBlock] bodyPc (bodyRegs p) (bodyLoads p c.σ.mem) c
    ⟨input.good, input.minstret, bodyHolds, by change KeysOK [8]; decide,
      chainPlan_facts (body_code input.code) (body_access p c.σ.mem input.window input.slotRead), body_chain_ok,
      input.tick⟩
  constructor
  apply Vsa.Logic.Triple.seq body.run
  intro b bp
  have bmem : b.σ.mem = c.σ.mem := by rw [bp.memory, body_log]; rfl
  have set : GHolds b.σ (setRegs p c.σ.mem) := by simpa only [body_regs] using bp.regs
  have kept := body_frame bp.frame (kept_of_head input.registers)
  have carried := carried_at_call set kept
  have bpc : PCAt EmptyMinorRefsSites.refsSite.call.pc b := by
    rw [PCAt, bp.pc, body_endpoint]; rfl
  have call := EmptyMinorRefsSites.refsSite.slot (copies := copies) (pl := pl) (bmem ▸ input.code) bp.good bp.tick
    bp.minstret carried fun e called => supply e
      ⟨by rw [called.mem, bmem]; rfl, EmptyMinorRefsSites.refsSite.linked_regs called, called.good, called.tick,
        called.minstret⟩
  obtain ⟨mid, run2, ret⟩ := call.run b ⟨bpc, rfl⟩
  obtain ⟨e, copies', called, done⟩ := ret.entered
  have jumped : Jumped R p c e :=
    ⟨by rw [called.mem, bmem]; rfl, EmptyMinorRefsSites.refsSite.linked_regs called, called.good, called.tick,
      called.minstret⟩
  have fr := frame e copies' mid jumped done
  obtain ⟨log, returned⟩ := done.returned
  obtain ⟨testHolds, keptMid⟩ := head_of_returned returned.registers
  have test := block_summary [testBlock (continues (p + 8#64) mid.σ.mem)] testPc (testRegs (p + 8#64))
    (testLoads mid.σ.mem) mid
    ⟨returned.good, returned.minstret, testHolds, by change KeysOK [9, 8]; decide,
      chainPlan_facts (test_code fr.code _) (test_access (p + 8#64) mid.σ.mem fr.stateRead fr.fieldRead fr.ptrRead),
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

/-! ## The whole loop -/

open Vsa.Logic in
/-- **The loop's obligations** for a caller invariant `Inv` and exit condition `Done`. -/
structure ScanStep (R : Nat → BitVec 64) (limit : BitVec 64) (pl : Place)
    (Inv : BitVec 64 → List PendingCopy → Config → Prop) (Done : Config → Prop) : Prop where
  head : ∀ p copies c, Inv p copies c → HeadInput R p c ∧ p.toNat + 8 ≤ limit.toNat
  supply : ∀ p copies c, Inv p copies c → ∀ e, Jumped R p c e →
    SlotCall (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies pl e
  frame : ∀ p copies c, Inv p copies c → ∀ e copies' mid, Jumped R p c e →
    SlotDone (EmptyMinorRefsSites.refsSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid → CalleeFrame c mid
  next : ∀ p copies c after, Inv p copies c → Iterated R p copies pl c after → PCAt bodyPc after →
    ∃ copies', Inv (p + 8#64) copies' after
  done : ∀ p copies c after, Inv p copies c → Iterated R p copies pl c after → PCAt exitPc after → Done after
  donePc : ∀ c, Done c → PCAt exitPc c

/-- The distance from `s0` to the table's end. -/
def rank (limit : BitVec 64) (c : Config) : Nat := limit.toNat - ((gprGet c.σ 8).getD 0).toNat

theorem exit_ne_body : exitPc ≠ bodyPc := by decide

/-- **The VM-stack loop**, from any invariant state at the head to `Done`. -/
theorem loop {R : Nat → BitVec 64} {limit : BitVec 64} {pl : Place}
    {Inv : BitVec 64 → List PendingCopy → Config → Prop} {Done : Config → Prop}
    (step : ScanStep R limit pl Inv Done) :
    Vsa.Logic.Triple (fun c => ∃ p copies, Inv p copies c) Done := by
  apply loop_to_exit (entry := bodyPc) (rank limit)
  · rintro c ⟨p, copies, inv⟩
    exact (step.head p copies c inv).1.pc
  · intro c done onBody
    have exitAt := step.donePc c done
    rw [PCAt] at exitAt onBody
    rw [exitAt] at onBody
    exact exit_ne_body (Option.some.inj onBody)
  · rintro c ⟨p, copies, inv⟩
    obtain ⟨input, room⟩ := step.head p copies c inv
    obtain ⟨after, run, post⟩ := (iteration input (step.supply p copies c inv) (step.frame p copies c inv)).run
      c ⟨input.pc, rfl⟩
    refine ⟨after, run, ?_, ?_⟩
    · obtain ⟨e, copies', mid, jumped, done, memory, pc⟩ := post.slot
      by_cases more : continues (p + 8#64) mid.σ.mem = true
      · rw [if_pos more] at pc
        obtain ⟨copies'', inv'⟩ := step.next p copies c after inv post pc
        exact Or.inl ⟨_, _, inv'⟩
      · rw [if_neg more] at pc
        exact Or.inr (step.done p copies c after inv post pc)
    · have before : gprGet c.σ 8 = some p := gholds_lookup _ input.registers rfl
      have now : gprGet after.σ 8 = some (p + 8#64) := gholds_lookup _ post.registers rfl
      have sum : (p + 8#64).toNat = p.toNat + 8 := by
        rw [BitVec.toNat_add]
        have bound := limit.isLt
        simp only [BitVec.toNat_ofNat]
        omega
      simp only [rank, before, now, Option.getD_some, sum]
      omega


end OCaml.Vm.Gc.RefScan
