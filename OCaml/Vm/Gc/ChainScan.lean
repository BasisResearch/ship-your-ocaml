import OCaml.Vm.Gc.IndirectSlot
import OCaml.Vm.Gc.LoopFold
import OCaml.Vm.Gc.ChainPlan
import OCaml.Vm.Gc.StackArithmetic
import Vsa.Sim.ChainFactsTac

/-! # Walking a skiplist's level-0 chain with `caml_oldify_one`

`caml_scan_global_young_roots` walks `caml_global_roots` and then
`caml_global_roots_young` the same way:
`for (e = list->forward[0]; e != NULL; e = e->forward[0]) f(*(value *) e->key, (value *) e->key);`
compiled as a body block at the loop head (`a1 = e->key`, `s0 = e->forward[0]`,
`a0 = *a1`), a `jalr s1` site, and `bnez s0`. A cell's key is at `+0` and its
level-0 link at `+16`.

`ChainLoop Loaded` collects one such loop's generated facts; `iteration` and
`loop` are proved once over it, for both instances (`GlobalScanLoops`). -/
namespace OCaml.Vm.Gc.ChainScan
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A cell's key (the root's address). -/
def key (m : Std.ExtHashMap Nat (BitVec 8)) (cell : BitVec 64) : BitVec 64 := bytesT m cell.toNat 8

/-- A cell's level-0 successor. -/
def next (m : Std.ExtHashMap Nat (BitVec 8)) (cell : BitVec 64) : BitVec 64 := bytesT m (cell + 16#64).toNat 8

def bodyLoads (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m cell.toNat, read8 m (cell + 16#64).toNat, read8 m (key m cell).toNat]

/-- After the body: `a0 = *key`, `s0 = next`, `a1 = key`. -/
def setRegs (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(10, bytesT m (key m cell).toNat 8), (8, next m cell), (11, key m cell)]

/-- The loop's facts, from the generated rows of one instance. -/
structure ChainLoop (Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop) where
  bodyPc : BitVec 64
  exitPc : BitVec 64
  bodyBlock : BBlock
  testBlock : Bool → BBlock
  site : IndirectSlotSite Loaded
  source : site.call.source = 9
  exit_ne_body : exitPc ≠ bodyPc
  body_chain_ok : ChainOK bodyPc [8] [bodyBlock]
  body_code : ∀ {m}, Loaded m → ChainCode m [bodyBlock]
  body_regs : ∀ cell m, (evalBlocks [bodyBlock] (SegEvalState.init [(8, cell)] (bodyLoads cell m))).regs =
    setRegs cell m
  body_log : ∀ cell m, (evalBlocks [bodyBlock] (SegEvalState.init [(8, cell)] (bodyLoads cell m))).log = []
  body_endpoint : ∀ cell m, evalBlocksPC bodyPc (SegEvalState.init [(8, cell)] (bodyLoads cell m)) [bodyBlock] =
    site.call.pc
  body_access : ∀ cell m, ReadWindow cell 8 → ReadWindow (cell + 16#64) 8 → ReadWindow (key m cell) 8 →
    ChainAccess m [(8, cell)] (bodyLoads cell m) [bodyBlock]
  body_written : ∀ n ∈ wrChain [bodyBlock], n ∈ [8, 10, 11]
  test_chain_ok : ∀ t, ChainOK site.call.link [8] [testBlock t]
  test_code : ∀ {m}, Loaded m → ∀ t, ChainCode m [testBlock t]
  test_access : ∀ (s0 : BitVec 64) m, ChainAccess m [(8, s0)] [] [testBlock (s0 != 0#64)]
  test_endpoint : ∀ (s0 : BitVec 64), evalBlocksPC site.call.link (SegEvalState.init [(8, s0)] []) [testBlock (s0 != 0#64)] =
    if s0 != 0#64 then bodyPc else exitPc
  test_log : ∀ (s0 : BitVec 64) t, (evalBlocks [testBlock t] (SegEvalState.init [(8, s0)] [])).log = []
  test_written : ∀ t, wrChain [testBlock t] = []

namespace ChainLoop
variable {Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop} (L : ChainLoop Loaded)

/-- The loop's registers at the head: `sp`, `s0 = cell`, `s1 = f`, and the
callee-saved `s2`–`s9` (`R`). -/
def headRegs (R : Nat → BitVec 64) (cell : BitVec 64) : GRegs :=
  [(2, R 2), (8, cell), (9, R 9), (18, R 18), (19, R 19), (20, R 20), (21, R 21),
   (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

def keptRegs (R : Nat → BitVec 64) : GRegs :=
  [(2, R 2), (9, R 9), (18, R 18), (19, R 19), (20, R 20), (21, R 21),
   (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

/-- The callee's argument view for `cell` (`a0 = *key`, `a1 = key`, `s0 = next`). -/
def calleeR (R : Nat → BitVec 64) (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) : BitVec 64 :=
  if n = 8 then next m cell else if n = 10 then bytesT m (key m cell).toNat 8
  else if n = 11 then key m cell else R n

structure HeadInput (R : Nat → BitVec 64) (cell : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Loaded c.σ.mem
  pc : PCAt L.bodyPc c
  registers : GHolds c.σ (headRegs R cell)
  cellRead : ReadWindow cell 8
  linkRead : ReadWindow (cell + 16#64) 8
  rootRead : ReadWindow (key c.σ.mem cell) 8
  /-- `s1` holds `caml_oldify_one` -/
  action : R 9 = OldifyEntry.pc

/-- The callee's state at its entry, as the caller sees it. -/
structure Jumped (R : Nat → BitVec 64) (cell : BitVec 64) (c e : Config) : Prop where
  memory : e.σ.mem = c.σ.mem
  registers : GHolds e.σ (OldifyEntry.regs (L.site.linked (calleeR R cell c.σ.mem)))
  good : GoodState e.σ
  tick : e.tick < 2
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w

/-- One iteration returned: the slot call's result `mid`, then the link test. -/
structure Iterated (R : Nat → BitVec 64) (cell : BitVec 64) (copies : List PendingCopy) (pl : Place)
    (c after : Config) : Prop where
  slot : ∃ e copies' mid, L.Jumped R cell c e ∧
    SlotDone (L.site.linked (calleeR R cell c.σ.mem)) copies copies' pl e mid ∧
    after.σ.mem = mid.σ.mem ∧ PCAt (if next c.σ.mem cell != 0#64 then L.bodyPc else L.exitPc) after
  registers : GHolds after.σ (headRegs R (next c.σ.mem cell))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w

theorem kept_of_head {R cell} {σ : MState} (h : GHolds σ (headRegs R cell)) : GHolds σ (keptRegs R) := by
  apply gholds_select h
  intro n v member
  simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem body_frame {R : Nat → BitVec 64} {before after : MState}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ wrChain [L.bodyBlock], (gprReg n == r) = false) → after.regs.get? r = before.regs.get? r)
    (holds : GHolds before (keptRegs R)) : GHolds after (keptRegs R) := by
  apply gholds_of_frame frame _ (by change KeysOK [2,9,18,19,20,21,22,23,24,25]; decide) ?_ ?_ holds
  · change ∀ n ∈ [2,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · intro n hn m hm
    have small := L.body_written m hm
    simp only [keptRegs, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn small
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases small with rfl | rfl | rfl <;> decide

theorem carried_at_call {R cell} {m : Std.ExtHashMap Nat (BitVec 8)} {σ : MState}
    (set : GHolds σ (setRegs cell m)) (kept : GHolds σ (keptRegs R)) :
    GHolds σ (OldifyBridge.carried (calleeR R cell m)) := by
  have both : GHolds σ (setRegs cell m ++ keptRegs R) := (gholds_append _ _).mpr ⟨set, kept⟩
  apply gholds_select both
  intro n v member
  simp only [OldifyBridge.carried, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    simp [setRegs, keptRegs, calleeR, lookupG]

theorem head_of_returned {R cell} {m : Std.ExtHashMap Nat (BitVec 8)} {σ : MState}
    (holds : GHolds σ (OldifyEntry.callerRegs (L.site.linked (calleeR R cell m)))) :
    GHolds σ (headRegs R (next m cell)) := by
  apply gholds_select holds
  intro n v member
  simp only [headRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    simp [OldifyEntry.callerRegs, OldifyReturn.slots, IndirectSlotSite.linked, calleeR, lookupG]

/-- **One iteration of a chain walk**, from the head at `cell` to the next head
or the exit. The callee is any `caml_oldify_one` route the caller supplies. -/
theorem iteration {R : Nat → BitVec 64} {cell : BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (input : L.HeadInput R cell c)
    (supply : ∀ e, L.Jumped R cell c e → SlotCall (L.site.linked (calleeR R cell c.σ.mem)) copies pl e)
    (frame : ∀ e copies' mid, L.Jumped R cell c e →
      SlotDone (L.site.linked (calleeR R cell c.σ.mem)) copies copies' pl e mid → Loaded mid.σ.mem) :
    FnSummary L.bodyPc (fun d => d = c) (L.Iterated R cell copies pl c) := by
  have bodyHolds : GHolds c.σ [(8, cell)] := ⟨gholds_lookup _ input.registers rfl, True.intro⟩
  have body := block_summary [L.bodyBlock] L.bodyPc [(8, cell)] (bodyLoads cell c.σ.mem) c
    ⟨input.good, input.minstret, bodyHolds, by change KeysOK [8]; decide,
      chainPlan_facts (L.body_code input.code)
        (L.body_access cell c.σ.mem input.cellRead input.linkRead input.rootRead),
      L.body_chain_ok, input.tick⟩
  constructor
  apply Vsa.Logic.Triple.seq body.run
  intro b bp
  have bmem : b.σ.mem = c.σ.mem := by rw [bp.memory, L.body_log]; rfl
  have set : GHolds b.σ (setRegs cell c.σ.mem) := by simpa only [L.body_regs] using bp.regs
  have kept := L.body_frame bp.frame (kept_of_head input.registers)
  have carried := carried_at_call set kept
  have bpc : PCAt L.site.call.pc b := by rw [PCAt, bp.pc, L.body_endpoint]
  have target : calleeR R cell c.σ.mem L.site.call.source = OldifyEntry.pc := by
    rw [L.source]; simpa [calleeR] using input.action
  have call := L.site.slot (copies := copies) (pl := pl) (bmem ▸ input.code) bp.good bp.tick bp.minstret carried
    target fun e called => supply e
      ⟨by rw [called.mem, bmem]; rfl, L.site.linked_regs called, called.good, called.tick, called.minstret⟩
  obtain ⟨mid, run2, ret⟩ := call.run b ⟨bpc, rfl⟩
  obtain ⟨e, copies', called, done⟩ := ret.entered
  have jumped : L.Jumped R cell c e :=
    ⟨by rw [called.mem, bmem]; rfl, L.site.linked_regs called, called.good, called.tick, called.minstret⟩
  have code := frame e copies' mid jumped done
  obtain ⟨log, returned⟩ := done.returned
  have headMid := L.head_of_returned returned.registers
  have testHolds : GHolds mid.σ [(8, next c.σ.mem cell)] := ⟨gholds_lookup _ headMid rfl, True.intro⟩
  have test := block_summary [L.testBlock (next c.σ.mem cell != 0#64)] L.site.call.link
    [(8, next c.σ.mem cell)] [] mid
    ⟨returned.good, returned.minstret, testHolds, by change KeysOK [8]; decide,
      chainPlan_facts (L.test_code code _) (L.test_access _ mid.σ.mem), L.test_chain_ok _, returned.tick⟩
  have midPc : PCAt L.site.call.link mid := by
    have h := returned.pc
    simp only [IndirectSlotSite.linked, ite_true] at h
    exact h
  obtain ⟨after, run3, tp⟩ := test.run mid ⟨midPc, rfl⟩
  have headAfter : GHolds after.σ (headRegs R (next c.σ.mem cell)) := by
    apply gholds_of_frame tp.frame _ (by change KeysOK [2,8,9,18,19,20,21,22,23,24,25]; decide) ?_ ?_ headMid
    · change ∀ n ∈ [2,8,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · intro n _ m hm
      rw [L.test_written] at hm
      cases hm
  refine ⟨after, run2.trans run3, ⟨⟨e, copies', mid, jumped, done, ?_, ?_⟩, headAfter, tp.good, tp.tick,
    tp.minstret⟩⟩
  · rw [tp.memory, L.test_log]; rfl
  · rw [PCAt, tp.pc, L.test_endpoint]

/-- **The walk's obligations** for a caller invariant `Inv` (current cell and
published table), exit condition `Done`, and a rank the iterations decrease
(the remaining chain's length). -/
structure WalkStep (R : Nat → BitVec 64) (pl : Place) (Inv : BitVec 64 → List PendingCopy → Config → Prop)
    (Done : Config → Prop) (rank : Config → Nat) : Prop where
  head : ∀ cell copies c, Inv cell copies c → L.HeadInput R cell c
  supply : ∀ cell copies c, Inv cell copies c → ∀ e, L.Jumped R cell c e →
    SlotCall (L.site.linked (calleeR R cell c.σ.mem)) copies pl e
  frame : ∀ cell copies c, Inv cell copies c → ∀ e copies' mid, L.Jumped R cell c e →
    SlotDone (L.site.linked (calleeR R cell c.σ.mem)) copies copies' pl e mid → Loaded mid.σ.mem
  next : ∀ cell copies c after, Inv cell copies c → L.Iterated R cell copies pl c after → PCAt L.bodyPc after →
    ∃ copies', Inv (next c.σ.mem cell) copies' after
  done : ∀ cell copies c after, Inv cell copies c → L.Iterated R cell copies pl c after → PCAt L.exitPc after →
    Done after
  donePc : ∀ c, Done c → PCAt L.exitPc c
  progress : ∀ cell copies c after, Inv cell copies c → L.Iterated R cell copies pl c after → rank after < rank c

/-- **The whole chain walk**, from any invariant state at the head to `Done`. -/
theorem walk {R : Nat → BitVec 64} {pl : Place} {Inv : BitVec 64 → List PendingCopy → Config → Prop}
    {Done : Config → Prop} {rank : Config → Nat} (step : L.WalkStep R pl Inv Done rank) :
    Vsa.Logic.Triple (fun c => ∃ cell copies, Inv cell copies c) Done := by
  apply loop_to_exit (entry := L.bodyPc) rank
  · rintro c ⟨cell, copies, inv⟩
    exact (step.head cell copies c inv).pc
  · intro c done onBody
    have exitAt := step.donePc c done
    rw [PCAt] at exitAt onBody
    rw [exitAt] at onBody
    exact L.exit_ne_body (Option.some.inj onBody)
  · rintro c ⟨cell, copies, inv⟩
    have input := step.head cell copies c inv
    obtain ⟨after, run, post⟩ := (L.iteration input (step.supply cell copies c inv) (step.frame cell copies c inv)).run
      c ⟨input.pc, rfl⟩
    refine ⟨after, run, ?_, step.progress cell copies c after inv post⟩
    obtain ⟨e, copies', mid, jumped, done, memory, pc⟩ := post.slot
    by_cases more : (next c.σ.mem cell != 0#64) = true
    · rw [if_pos more] at pc
      obtain ⟨copies'', inv'⟩ := step.next cell copies c after inv post pc
      exact Or.inl ⟨_, _, inv'⟩
    · rw [if_neg more] at pc
      exact Or.inr (step.done cell copies c after inv post pc)

end ChainLoop

end OCaml.Vm.Gc.ChainScan
