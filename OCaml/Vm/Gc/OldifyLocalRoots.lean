import OCaml.Vm.Gc.RootLoops
import OCaml.Vm.Gc.LocalRootsTail
import OCaml.Vm.Primitives.SymbolicAppend

/-! # `caml_oldify_local_roots`: the prologue

Saves `s1`, `ra`, `s0`, `s2` in a 48-byte frame, sets `s1 = &Caml_state`, loads
the domain record into `a5`, `extern_sp` into `s0` and `stack_high` into `a4`,
and enters the VM-stack loop (`StackScan`) unless the stack is empty
(`bgeu s0, a4` to the loop exit). -/
namespace OCaml.Vm.Gc.OldifyLocalRoots
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable StackScan

def headBlock (t : Bool) : BBlock :=
  if t then caml_oldify_local_rootsXc784TSeg.getD 0 {body := [], term := none}
  else caml_oldify_local_rootsXc784FSeg.getD 0 {body := [], term := none}

def pc : BitVec 64 := 0x8000c784#64

def frame (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551568#64

def regs (sp s0 s1 s2 ra : BitVec 64) : GRegs := [(2, sp), (9, s1), (1, ra), (8, s0), (18, s2)]

def saveLog (sp s0 s1 s2 ra : BitVec 64) : List WEntry :=
  [((frame sp + 24#64).toNat, 8, s1), ((frame sp + 40#64).toNat, 8, ra), ((frame sp + 32#64).toNat, 8, s0),
   ((frame sp + 16#64).toNat, 8, s2)]

def afterHead (fsp ra s2 : BitVec 64) (l1 l2 l3 : List (BitVec 8)) : GRegs :=
  [(14, bytesVal .ld l3), (8, bytesVal .ld l2), (15, bytesVal .ld l1), (9, statePtr), (2, fsp), (1, ra), (18, s2)]

theorem head_regs (sp s0 s1 s2 ra : BitVec 64) (l1 l2 l3 : List (BitVec 8)) (t : Bool) :
    runGM (headBlock t).body (regs sp s0 s1 s2 ra) [l1, l2, l3] = afterHead (frame sp) ra s2 l1 l2 l3 := by
  cases t <;>
  simp [headBlock, caml_oldify_local_rootsXc784TSeg, caml_oldify_local_rootsXc784FSeg, regs, afterHead, frame,
    statePtr, Layout.sym_Caml_state, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

theorem head_log (sp s0 s1 s2 ra : BitVec 64) (lds : List (List (BitVec 8))) (t : Bool) :
    wlogM (headBlock t).body (regs sp s0 s1 s2 ra) lds = saveLog sp s0 s1 s2 ra := by
  cases t <;> rfl

theorem prefix7_regs (sp s0 s1 s2 ra : BitVec 64) (lds : List (List (BitVec 8))) (t : Bool) :
    runGM ((headBlock t).body.take 7) (regs sp s0 s1 s2 ra) lds =
      [(9, statePtr), (2, frame sp), (1, ra), (8, s0), (18, s2)] := by
  cases t <;>
  simp [headBlock, caml_oldify_local_rootsXc784TSeg, caml_oldify_local_rootsXc784FSeg, regs, frame,
    statePtr, Layout.sym_Caml_state, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

theorem prefix8_regs (sp s0 s1 s2 ra : BitVec 64) (l1 : List (BitVec 8)) (rest : List (List (BitVec 8))) (t : Bool) :
    runGM ((headBlock t).body.take 8) (regs sp s0 s1 s2 ra) (l1 :: rest) =
      [(15, bytesVal .ld l1), (9, statePtr), (2, frame sp), (1, ra), (8, s0), (18, s2)] := by
  cases t <;>
  simp [headBlock, caml_oldify_local_rootsXc784TSeg, caml_oldify_local_rootsXc784FSeg, regs, frame,
    statePtr, Layout.sym_Caml_state, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

theorem prefix9_regs (sp s0 s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (t : Bool) : runGM ((headBlock t).body.take 9) (regs sp s0 s1 s2 ra) (l1 :: l2 :: rest) =
      [(8, bytesVal .ld l2), (15, bytesVal .ld l1), (9, statePtr), (2, frame sp), (1, ra), (18, s2)] := by
  cases t <;>
  simp [headBlock, caml_oldify_local_rootsXc784TSeg, caml_oldify_local_rootsXc784FSeg, regs, frame,
    statePtr, Layout.sym_Caml_state, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

/-- The domain record after the saves. -/
def domain (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m Layout.sym_Caml_state 8

def headLoads (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m Layout.sym_Caml_state, read8 m (domain m + 160#64).toNat, read8 m (domain m + 144#64).toNat]

theorem head_access (sp s0 s1 s2 ra : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (t : Bool)
    (saves : ∀ off ∈ [24, 40, 32, 16], WriteWindow (frame sp + BitVec.ofNat 64 off) 8)
    (stateRead : ReadWindow statePtr 8)
    (externRead : ReadWindow (domain (writeLog m (saveLog sp s0 s1 s2 ra)) + 160#64) 8)
    (highRead : ReadWindow (domain (writeLog m (saveLog sp s0 s1 s2 ra)) + 144#64) 8) :
    AccessPlan m (regs sp s0 s1 s2 ra) (headLoads (writeLog m (saveLog sp s0 s1 s2 ra))) (headBlock t).body := by
  cases t
  · simp only [headBlock, caml_oldify_local_rootsXc784FSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true]
    chain_facts True.intro
    · exact (saves 24 (by decide)).sd rfl rfl
    · exact (saves 40 (by decide)).sd rfl rfl
    · exact (saves 32 (by decide)).sd rfl rfl
    · exact (saves 16 (by decide)).sd rfl rfl
    · refine stateRead.ld rfl ?_ ?_
      · change eaddrM _ (runGM ((headBlock false).body.take 7) (regs sp s0 s1 s2 ra) _) = _
        rw [prefix7_regs]
        simp [statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
      · change LPins8 (memAfter m ((headBlock false).body.take 7) (regs sp s0 s1 s2 ra) _) _ _
        rw [memAfter_eq, show wlogM ((headBlock false).body.take 7) (regs sp s0 s1 s2 ra) _ = saveLog sp s0 s1 s2 ra
          from rfl]
        exact read8_pins _ _
    · refine externRead.ld rfl ?_ ?_
      · change eaddrM _ (runGM ((headBlock false).body.take 8) (regs sp s0 s1 s2 ra) (_ :: _)) = _
        rw [prefix8_regs]
        simp [domain, eaddrM, mkLine, decodeM, srcVal, lookupG, read8_value, Layout.off_extern_sp, Functions.sign_extend,
          Sail.BitVec.signExtend]
      · change LPins8 (memAfter m ((headBlock false).body.take 8) (regs sp s0 s1 s2 ra) _) _ _
        rw [memAfter_eq, show wlogM ((headBlock false).body.take 8) (regs sp s0 s1 s2 ra) _ = saveLog sp s0 s1 s2 ra
          from rfl]
        exact read8_pins _ _
    · refine highRead.ld rfl ?_ ?_
      · change eaddrM _ (runGM ((headBlock false).body.take 9) (regs sp s0 s1 s2 ra) (_ :: _ :: _)) = _
        rw [prefix9_regs]
        simp [domain, eaddrM, mkLine, decodeM, srcVal, lookupG, read8_value, Layout.off_stack_high, Functions.sign_extend,
          Sail.BitVec.signExtend]
      · change LPins8 (memAfter m ((headBlock false).body.take 9) (regs sp s0 s1 s2 ra) _) _ _
        rw [memAfter_eq, show wlogM ((headBlock false).body.take 9) (regs sp s0 s1 s2 ra) _ = saveLog sp s0 s1 s2 ra
          from rfl]
        exact read8_pins _ _
  · simp only [headBlock, caml_oldify_local_rootsXc784TSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true]
    chain_facts True.intro
    · exact (saves 24 (by decide)).sd rfl rfl
    · exact (saves 40 (by decide)).sd rfl rfl
    · exact (saves 32 (by decide)).sd rfl rfl
    · exact (saves 16 (by decide)).sd rfl rfl
    · refine stateRead.ld rfl ?_ ?_
      · change eaddrM _ (runGM ((headBlock true).body.take 7) (regs sp s0 s1 s2 ra) _) = _
        rw [prefix7_regs]
        simp [statePtr, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
      · change LPins8 (memAfter m ((headBlock true).body.take 7) (regs sp s0 s1 s2 ra) _) _ _
        rw [memAfter_eq, show wlogM ((headBlock true).body.take 7) (regs sp s0 s1 s2 ra) _ = saveLog sp s0 s1 s2 ra
          from rfl]
        exact read8_pins _ _
    · refine externRead.ld rfl ?_ ?_
      · change eaddrM _ (runGM ((headBlock true).body.take 8) (regs sp s0 s1 s2 ra) (_ :: _)) = _
        rw [prefix8_regs]
        simp [domain, eaddrM, mkLine, decodeM, srcVal, lookupG, read8_value, Layout.off_extern_sp, Functions.sign_extend,
          Sail.BitVec.signExtend]
      · change LPins8 (memAfter m ((headBlock true).body.take 8) (regs sp s0 s1 s2 ra) _) _ _
        rw [memAfter_eq, show wlogM ((headBlock true).body.take 8) (regs sp s0 s1 s2 ra) _ = saveLog sp s0 s1 s2 ra
          from rfl]
        exact read8_pins _ _
    · refine highRead.ld rfl ?_ ?_
      · change eaddrM _ (runGM ((headBlock true).body.take 9) (regs sp s0 s1 s2 ra) (_ :: _ :: _)) = _
        rw [prefix9_regs]
        simp [domain, eaddrM, mkLine, decodeM, srcVal, lookupG, read8_value, Layout.off_stack_high, Functions.sign_extend,
          Sail.BitVec.signExtend]
      · change LPins8 (memAfter m ((headBlock true).body.take 9) (regs sp s0 s1 s2 ra) _) _ _
        rw [memAfter_eq, show wlogM ((headBlock true).body.take 9) (regs sp s0 s1 s2 ra) _ = saveLog sp s0 s1 s2 ra
          from rfl]
        exact read8_pins _ _

/-- `extern_sp` and `stack_high` after the saves. -/
def externSp (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (domain m + 160#64).toNat 8
def stackHigh' (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (domain m + 144#64).toNat 8

/-- The prologue takes the exit branch when the VM stack is empty. -/
def empty (m : Std.ExtHashMap Nat (BitVec 8)) : Bool := decide ((stackHigh' m).toNat ≤ (externSp m).toNat)

theorem head_control (sp s0 s1 s2 ra : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    TermFactsO (runGM (headBlock (empty m)).body (regs sp s0 s1 s2 ra) (headLoads m)) (headBlock (empty m)).term := by
  rw [show headLoads m = [read8 m Layout.sym_Caml_state, read8 m (domain m + 160#64).toNat,
    read8 m (domain m + 144#64).toNat] from rfl, head_regs]
  generalize chosen : empty m = t
  cases t
  · have no : ¬ (stackHigh' m).toNat ≤ (externSp m).toNat := of_decide_eq_false chosen
    simp [headBlock, caml_oldify_local_rootsXc784FSeg, TermFactsO, TermFactsT, afterHead, srcVal, lookupG,
      guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, read8_value, externSp, stackHigh'] at no ⊢
    omega
  · have yes : (stackHigh' m).toNat ≤ (externSp m).toNat := of_decide_eq_true chosen
    simp [headBlock, caml_oldify_local_rootsXc784TSeg, TermFactsO, TermFactsT, afterHead, srcVal, lookupG,
      guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, read8_value, externSp, stackHigh'] at yes ⊢
    exact yes

theorem head_chain_ok (t : Bool) : ChainOK pc [2, 9, 1, 8, 18] [headBlock t] := by cases t <;> decide

theorem head_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_oldify_local_rootsLoaded mem) (t : Bool) :
    ChainCode mem [headBlock t] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  cases t <;> constructor
  all_goals simp only [headBlock, caml_oldify_local_rootsXc784TSeg, caml_oldify_local_rootsXc784FSeg,
    List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_oldify_local_roots_at_"

/-- The caller's registers as a function: `sp` the frame, `s2`–`s9` kept. -/
def loopR (R : Nat → BitVec 64) (sp : BitVec 64) (n : Nat) : BitVec 64 := if n = 2 then frame sp else R n

def calleeSaved (R : Nat → BitVec 64) : GRegs :=
  [(19, R 19), (20, R 20), (21, R 21), (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

/-- `caml_oldify_local_roots`' input. -/
structure Input (R : Nat → BitVec 64) (sp ra : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_local_rootsLoaded c.σ.mem
  pc : PCAt pc c
  registers : GHolds c.σ (regs sp (R 8) (R 9) (R 18) ra)
  callee : GHolds c.σ (calleeSaved R)
  saves : ∀ off ∈ [24, 40, 32, 16], WriteWindow (frame sp + BitVec.ofNat 64 off) 8
  stateRead : ReadWindow statePtr 8
  externRead : ReadWindow (domain (writeLog c.σ.mem (saveLog sp (R 8) (R 9) (R 18) ra)) + 160#64) 8
  highRead : ReadWindow (domain (writeLog c.σ.mem (saveLog sp (R 8) (R 9) (R 18) ra)) + 144#64) 8

/-- After the prologue, at the loop head or (empty stack) the loop exit. -/
structure Prologued (R : Nat → BitVec 64) (sp ra : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  code : Code.Caml_oldify_local_rootsLoaded d.σ.mem
  memory : d.σ.mem = writeLog c.σ.mem (saveLog sp (R 8) (R 9) (R 18) ra)
  pc : PCAt (if empty d.σ.mem then exitPc else bodyPc) d
  head : GHolds d.σ (headRegs (loopR R sp) (externSp d.σ.mem))
  domainReg : gprGet d.σ 15 = some (domain d.σ.mem)
  output : d.σ.sailOutput = c.σ.sailOutput

theorem stage_head {R sp ra c} (input : Input R sp ra c) :
    ∃ d, Steps c d ∧ Prologued R sp ra c d := by
  let m := writeLog c.σ.mem (saveLog sp (R 8) (R 9) (R 18) ra)
  have access : ChainAccess c.σ.mem (regs sp (R 8) (R 9) (R 18) ra) (headLoads m) [headBlock (empty m)] :=
    ChainAccess.cons ⟨head_access sp (R 8) (R 9) (R 18) ra c.σ.mem _ input.saves input.stateRead input.externRead
      input.highRead, by
        have h := head_control sp (R 8) (R 9) (R 18) ra m
        exact h⟩ ChainAccess.nil
  have facts := chainPlan_facts (head_code input.code _) access
  obtain ⟨d, run, post⟩ := (block_summary _ pc (regs sp (R 8) (R 9) (R 18) ra) (headLoads m) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2, 9, 1, 8, 18]; decide, facts,
      head_chain_ok _, input.tick⟩).run c ⟨input.pc, rfl⟩
  have mem : d.σ.mem = m := by
    rw [post.memory]
    simp only [evalBlocks, evalBlock, SegEvalState.init, head_log, List.append_nil, List.nil_append]
    rfl
  have holds := post.regs
  simp only [evalBlocks, evalBlock, SegEvalState.init] at holds
  rw [show headLoads m = [read8 m Layout.sym_Caml_state, read8 m (domain m + 160#64).toNat,
    read8 m (domain m + 144#64).toNat] from rfl, head_regs] at holds
  unfold afterHead at holds
  rw [read8_value, read8_value, read8_value] at holds
  have callee : GHolds d.σ (calleeSaved R) := by
    apply gholds_of_frame post.frame _ (by change KeysOK [19, 20, 21, 22, 23, 24, 25]; decide) ?_ ?_ input.callee
    · change ∀ n ∈ [19, 20, 21, 22, 23, 24, 25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · intro n hn k hk
      have hk' : k ∈ [2, 9, 15, 8, 14] := by revert k hk; generalize empty m = t; cases t <;> decide
      simp only [calleeSaved, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn hk'
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨d, run, post.good, post.minstret, post.tick, ?_, mem, ?_, ?_, ?_, post.output⟩
  · exact image_after Code.caml_oldify_local_roots_transport (by decide) input.code facts post
  · rw [PCAt, post.pc, mem]
    generalize chosen : empty m = t
    cases t <;> rfl
  · rw [mem]
    have both := (gholds_append _ _).mpr ⟨holds, callee⟩
    apply gholds_select both
    intro n v member
    simp only [headRegs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [loopR, calleeSaved, externSp, domain, lookupG, m]
  · rw [mem]; exact gholds_lookup _ holds rfl

end OCaml.Vm.Gc.OldifyLocalRoots
