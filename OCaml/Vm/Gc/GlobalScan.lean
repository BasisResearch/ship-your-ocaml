import OCaml.Vm.Gc.Generated.GlobalScanLoops
import OCaml.Vm.Gc.Skiplist
import OCaml.Vm.Gc.SaveBank
import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Primitives.Control
import OCaml.Vm.Primitives.Call
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.SymbolicAppend
import Vsa.Sim.GRegsFrame
import Vsa.Sim.ChainFactsTac

/-! # `caml_scan_global_young_roots(f)`: the blocks around the walks

```
for (e = caml_global_roots.forward[0]; e; e = e->forward[0]) f(*e->key, e->key);
for (e = caml_global_roots_young.forward[0]; e; e = e->forward[0]) f(*e->key, e->key);
for (e = caml_global_roots_young.forward[0]; e; e = e->forward[0])
  caml_skiplist_insert(&caml_global_roots_old, e->key, 0);
caml_skiplist_empty(&caml_global_roots_young);    /* tail call */
```
The walks are `GlobalScanLoops.allLoop`/`youngLoop` (`ChainScan`); here are
the prologue (`0x8000cd00`), the two young-list tests (`0x8000cd3c`,
`0x8000cd58`), the insert loop's body (`0x8000cd60`) and test (`0x8000cd78`),
and the epilogue's tail jump (`0x8000cd7c`). -/
namespace OCaml.Vm.Gc.GlobalScan
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady)

def headBlock (t : Bool) : BBlock :=
  if t then caml_scan_global_young_rootsXcd00TSeg.getD 0 {body := [], term := none}
  else caml_scan_global_young_rootsXcd00FSeg.getD 0 {body := [], term := none}
def youngTest (t : Bool) : BBlock :=
  if t then caml_scan_global_young_rootsXcd3cTSeg.getD 0 {body := [], term := none}
  else caml_scan_global_young_rootsXcd3cFSeg.getD 0 {body := [], term := none}
def youngRetest (t : Bool) : BBlock :=
  if t then caml_scan_global_young_rootsXcd58TSeg.getD 0 {body := [], term := none}
  else caml_scan_global_young_rootsXcd58FSeg.getD 0 {body := [], term := none}
def insertBody : BBlock := caml_scan_global_young_rootsXcd60Seg.getD 0 {body := [], term := none}
def insertTest (t : Bool) : BBlock :=
  if t then caml_scan_global_young_rootsXcd78TSeg.getD 0 {body := [], term := none}
  else caml_scan_global_young_rootsXcd78FSeg.getD 0 {body := [], term := none}
def tailBlock : BBlock := caml_scan_global_young_rootsXcd7cSeg.getD 0 {body := [], term := none}

def pc : BitVec 64 := 0x8000cd00#64
def youngTestPc : BitVec 64 := 0x8000cd3c#64
def youngRetestPc : BitVec 64 := 0x8000cd58#64
def insertPc : BitVec 64 := 0x8000cd60#64
def tailPc : BitVec 64 := 0x8000cd7c#64

def roots : BitVec 64 := BitVec.ofNat 64 Skiplist.globalRoots
def oldRoots : BitVec 64 := BitVec.ofNat 64 Skiplist.globalRootsOld
def youngRoots : BitVec 64 := BitVec.ofNat 64 Skiplist.globalRootsYoung

/-- The scan's frame. -/
def frame (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551584#64

/-! ## The prologue -/

def regs (sp s0 s1 s2 ra a0 : BitVec 64) : GRegs := [(2, sp), (9, s1), (18, s2), (1, ra), (8, s0), (10, a0)]

def afterHead (fsp ra a0 : BitVec 64) (l : List (BitVec 8)) : GRegs :=
  [(9, a0), (8, bytesVal .ld l), (18, roots), (2, fsp), (1, ra), (10, a0)]

def headLog (sp s0 s1 s2 ra : BitVec 64) : List WEntry :=
  [((frame sp + 8#64).toNat, 8, s1), ((frame sp + 0#64).toNat, 8, s2), ((frame sp + 24#64).toNat, 8, ra),
   ((frame sp + 16#64).toNat, 8, s0)]

theorem head_regs (sp s0 s1 s2 ra a0 : BitVec 64) (l : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (t : Bool) : runGM (headBlock t).body (regs sp s0 s1 s2 ra a0) (l :: rest) = afterHead (frame sp) ra a0 l := by
  cases t <;>
  simp [headBlock, caml_scan_global_young_rootsXcd00TSeg, caml_scan_global_young_rootsXcd00FSeg, regs, afterHead,
    frame, roots, Skiplist.globalRoots, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

theorem head_log (sp s0 s1 s2 ra a0 : BitVec 64) (lds : List (List (BitVec 8))) (t : Bool) :
    wlogM (headBlock t).body (regs sp s0 s1 s2 ra a0) lds = headLog sp s0 s1 s2 ra := by
  cases t <;> rfl

/-- The registers before the root-list load (`s2 = &caml_global_roots`). -/
theorem prefix7_regs (sp s0 s1 s2 ra a0 : BitVec 64) (lds : List (List (BitVec 8))) (t : Bool) :
    runGM ((headBlock t).body.take 7) (regs sp s0 s1 s2 ra a0) lds =
      [(18, roots), (2, frame sp), (9, s1), (1, ra), (8, s0), (10, a0)] := by
  cases t <;>
  simp [headBlock, caml_scan_global_young_rootsXcd00TSeg, caml_scan_global_young_rootsXcd00FSeg, regs,
    frame, roots, Skiplist.globalRoots, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

/-! ## The young-list tests -/

def testRegs : GRegs := [(18, roots)]

theorem youngTest_regs (l : List (BitVec 8)) (rest : List (List (BitVec 8))) (t : Bool) :
    runGM (youngTest t).body testRegs (l :: rest) = [(8, bytesVal .ld l), (18, roots)] := by
  cases t <;>
  simp [youngTest, caml_scan_global_young_rootsXcd3cTSeg, caml_scan_global_young_rootsXcd3cFSeg, testRegs,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, Functions.sign_extend,
    Sail.BitVec.signExtend]

theorem youngRetest_regs (l : List (BitVec 8)) (rest : List (List (BitVec 8))) (t : Bool) :
    runGM (youngRetest t).body testRegs (l :: rest) = [(8, bytesVal .ld l), (18, roots)] := by
  cases t <;>
  simp [youngRetest, caml_scan_global_young_rootsXcd58TSeg, caml_scan_global_young_rootsXcd58FSeg, testRegs,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, Functions.sign_extend,
    Sail.BitVec.signExtend]

/-! ## The insert loop and the epilogue -/

def insertArgs (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(10, oldRoots), (12, 0#64), (8, ChainScan.next m cell), (11, ChainScan.key m cell)]

theorem insert_regs (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    runGM insertBody.body [(8, cell)] [read8 m cell.toNat, read8 m (cell + 16#64).toNat] = insertArgs cell m := by
  simp [insertBody, caml_scan_global_young_rootsXcd60Seg, insertArgs, oldRoots, Skiplist.globalRootsOld,
    ChainScan.key, ChainScan.next, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    imm20Of, read8_value, Functions.sign_extend, Sail.BitVec.signExtend]

def restored (fsp : BitVec 64) (r1 r2 r3 r4 : List (BitVec 8)) : GRegs :=
  [(2, fsp + 32#64), (10, youngRoots), (18, bytesVal .ld r4), (9, bytesVal .ld r3), (1, bytesVal .ld r2),
   (8, bytesVal .ld r1)]

theorem tail_regs (fsp : BitVec 64) (r1 r2 r3 r4 : List (BitVec 8)) :
    runGM tailBlock.body [(2, fsp)] [r1, r2, r3, r4] = restored fsp r1 r2 r3 r4 := by
  simp [tailBlock, caml_scan_global_young_rootsXcd7cSeg, restored, youngRoots, Skiplist.globalRootsYoung,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

/-! ## The prologue as a piece -/

/-- The register view of the walks: the scan's frame in `sp`, `f` in `s1`,
`&caml_global_roots` in `s2`, the caller's `s3`–`s9`. -/
def scanR (R : Nat → BitVec 64) (sp f : BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 2 then frame sp else if n = 9 then f else if n = 18 then roots else R n

def calleeSaved (R : Nat → BitVec 64) : GRegs :=
  [(19, R 19), (20, R 20), (21, R 21), (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

/-- The registers the scan may change before its tail call. -/
def writes : List Nat := [1, 2, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 5, 6, 7, 28, 29, 30, 31]

def saveSlots : List (Nat × Nat) := [(9, 8), (18, 0), (1, 24), (8, 16)]

/-- The scan's input at its entry. -/
structure Input (R : Nat → BitVec 64) (sp ra f : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_scan_global_young_rootsLoaded c.σ.mem
  image : ExecutableImage c
  pc : PCAt pc c
  registers : GHolds c.σ (regs sp (R 8) (R 9) (R 18) ra f)
  callee : GHolds c.σ (calleeSaved R)
  saves : ∀ off ∈ [8, 0, 24, 16], WriteWindow (frame sp + BitVec.ofNat 64 off) 8
  rootsRead : ReadWindow roots 8
  rootsApart : OutLRange (headLog sp (R 8) (R 9) (R 18) ra) Skiplist.globalRoots 8
  aligned : ra.toNat % 4 = 0

/-- A state between the scan's pieces. -/
structure GStage (c0 : Config) (here : BitVec 64) (L : GRegs) (mem : Std.ExtHashMap Nat (BitVec 8)) (d : Config) :
    Prop where
  good : GoodState d.σ
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  code : Code.Caml_scan_global_young_rootsLoaded d.σ.mem
  pc : PCAt here d
  regs : GHolds d.σ L
  memory : d.σ.mem = mem
  output : d.σ.sailOutput = c0.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) → d.σ.regs.get? r = c0.σ.regs.get? r

def first (m : Std.ExtHashMap Nat (BitVec 8)) (sk : Nat) : BitVec 64 := bytesT m sk 8

theorem head_chain_ok (t : Bool) : ChainOK pc [2, 9, 18, 1, 8, 10] [headBlock t] := by cases t <;> decide

theorem head_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_scan_global_young_rootsLoaded mem) (t : Bool) :
    ChainCode mem [headBlock t] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  cases t <;> constructor
  all_goals simp only [headBlock, caml_scan_global_young_rootsXcd00TSeg, caml_scan_global_young_rootsXcd00FSeg,
    List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_scan_global_young_roots_at_"

theorem head_access (sp s0 s1 s2 ra f : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (saves : ∀ off ∈ [8, 0, 24, 16], WriteWindow (frame sp + BitVec.ofNat 64 off) 8)
    (read : ReadWindow roots 8) (apart : OutLRange (headLog sp s0 s1 s2 ra) Skiplist.globalRoots 8) :
    ChainAccess m (regs sp s0 s1 s2 ra f) [read8 (writeLog m (headLog sp s0 s1 s2 ra)) Skiplist.globalRoots]
      [headBlock (first (writeLog m (headLog sp s0 s1 s2 ra)) Skiplist.globalRoots == 0#64)] := by
  refine ChainAccess.cons ⟨?_, ?_⟩ ChainAccess.nil
  · generalize (first (writeLog m (headLog sp s0 s1 s2 ra)) Skiplist.globalRoots == 0#64) = t
    cases t
    · simp only [headBlock, caml_scan_global_young_rootsXcd00FSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true]
      chain_facts True.intro
      · exact (saves 8 (by decide)).sd rfl rfl
      · exact (saves 0 (by decide)).sd rfl rfl
      · exact (saves 24 (by decide)).sd rfl rfl
      · exact (saves 16 (by decide)).sd rfl rfl
      · refine read.ld rfl ?_ ?_
        · change eaddrM _ (runGM ((headBlock false).body.take 7) (regs sp s0 s1 s2 ra f) _) = _
          rw [prefix7_regs]
          simp [roots, Skiplist.globalRoots, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend,
            Sail.BitVec.signExtend]
        · change LPins8 (memAfter m ((headBlock false).body.take 7) (regs sp s0 s1 s2 ra f) _) _ _
          rw [memAfter_eq, show wlogM ((headBlock false).body.take 7) (regs sp s0 s1 s2 ra f) _ =
            headLog sp s0 s1 s2 ra from rfl]
          exact read8_pins _ _
    · simp only [headBlock, caml_scan_global_young_rootsXcd00TSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true]
      chain_facts True.intro
      · exact (saves 8 (by decide)).sd rfl rfl
      · exact (saves 0 (by decide)).sd rfl rfl
      · exact (saves 24 (by decide)).sd rfl rfl
      · exact (saves 16 (by decide)).sd rfl rfl
      · refine read.ld rfl ?_ ?_
        · change eaddrM _ (runGM ((headBlock true).body.take 7) (regs sp s0 s1 s2 ra f) _) = _
          rw [prefix7_regs]
          simp [roots, Skiplist.globalRoots, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend,
            Sail.BitVec.signExtend]
        · change LPins8 (memAfter m ((headBlock true).body.take 7) (regs sp s0 s1 s2 ra f) _) _ _
          rw [memAfter_eq, show wlogM ((headBlock true).body.take 7) (regs sp s0 s1 s2 ra f) _ =
            headLog sp s0 s1 s2 ra from rfl]
          exact read8_pins _ _
  · rw [head_regs]
    generalize h : (first (writeLog m (headLog sp s0 s1 s2 ra)) Skiplist.globalRoots == 0#64) = t
    cases t
    · have : first (writeLog m (headLog sp s0 s1 s2 ra)) Skiplist.globalRoots ≠ 0#64 := by simpa using h
      simp [headBlock, caml_scan_global_young_rootsXcd00FSeg, TermFactsO, TermFactsT, afterHead, srcVal, lookupG,
        guardB, read8_value, first] at this ⊢
      exact this
    · have : first (writeLog m (headLog sp s0 s1 s2 ra)) Skiplist.globalRoots = 0#64 := by simpa using h
      simp [headBlock, caml_scan_global_young_rootsXcd00TSeg, TermFactsO, TermFactsT, afterHead, srcVal, lookupG,
        guardB, read8_value, first] at this ⊢
      exact this

theorem head_endpoint (sp s0 s1 s2 ra f : BitVec 64) (l : List (BitVec 8)) :
    evalBlocksPC pc (SegEvalState.init (regs sp s0 s1 s2 ra f) [l]) [headBlock (bytesVal .ld l == 0#64)] =
      if bytesVal .ld l == 0#64 then youngTestPc else GlobalScanLoops.allLoop.bodyPc := by
  generalize (bytesVal .ld l == 0#64) = t
  cases t <;> rfl

theorem head_eval_regs (sp s0 s1 s2 ra f : BitVec 64) (l : List (BitVec 8)) (t : Bool) :
    (evalBlocks [headBlock t] (SegEvalState.init (regs sp s0 s1 s2 ra f) [l])).regs = afterHead (frame sp) ra f l := by
  simp only [evalBlocks, evalBlock, SegEvalState.init]
  exact head_regs sp s0 s1 s2 ra f l [] t

theorem head_eval_log (sp s0 s1 s2 ra f : BitVec 64) (l : List (BitVec 8)) (t : Bool) :
    (evalBlocks [headBlock t] (SegEvalState.init (regs sp s0 s1 s2 ra f) [l])).log = headLog sp s0 s1 s2 ra := by
  simp only [evalBlocks, evalBlock, SegEvalState.init, head_log, List.append_nil, List.nil_append]

/-- **The prologue**: saves, `s2 = &caml_global_roots`, `s1 = f`, `s0` the
first cell, then the first walk's head (or the young test when empty). -/
theorem stage_head {R sp ra f c} (input : Input R sp ra f c) :
    ∃ d, Steps c d ∧ GStage c (if first c.σ.mem Skiplist.globalRoots == 0#64 then youngTestPc
        else GlobalScanLoops.allLoop.bodyPc)
      (ChainScan.ChainLoop.headRegs (scanR R sp f) (first c.σ.mem Skiplist.globalRoots))
      (writeLog c.σ.mem (headLog sp (R 8) (R 9) (R 18) ra)) d := by
  have same : first (writeLog c.σ.mem (headLog sp (R 8) (R 9) (R 18) ra)) Skiplist.globalRoots =
      first c.σ.mem Skiplist.globalRoots := bytesT_writeLog_out _ input.rootsApart
  have access := head_access sp (R 8) (R 9) (R 18) ra f c.σ.mem input.saves input.rootsRead input.rootsApart
  have facts := chainPlan_facts (head_code input.code _) access
  obtain ⟨d, run, post⟩ := (block_summary _ pc (regs sp (R 8) (R 9) (R 18) ra f) _ c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2, 9, 18, 1, 8, 10]; decide, facts,
      head_chain_ok _, input.tick⟩).run c ⟨input.pc, rfl⟩
  have value : bytesVal .ld (read8 (writeLog c.σ.mem (headLog sp (R 8) (R 9) (R 18) ra)) Skiplist.globalRoots) =
      first c.σ.mem Skiplist.globalRoots := by rw [read8_value]; exact same
  have holds := post.regs
  rw [head_eval_regs] at holds
  unfold afterHead at holds
  rw [value] at holds
  have callee : GHolds d.σ (calleeSaved R) := by
    apply gholds_of_frame post.frame _ (by change KeysOK [19, 20, 21, 22, 23, 24, 25]; decide) ?_ ?_ input.callee
    · change ∀ n ∈ [19, 20, 21, 22, 23, 24, 25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · intro n hn m hm
      have hm' : m ∈ [2, 18, 8, 9] := by revert m hm; generalize (_ == 0#64) = t; cases t <;> decide
      simp only [calleeSaved, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn hm'
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hm' with rfl | rfl | rfl | rfl <;> decide
  refine ⟨d, run, post.good, post.minstret, post.tick, ?_, ?_, ?_, ?_, post.output, ?_⟩
  · exact image_after Code.caml_scan_global_young_roots_transport (by decide) input.code facts post
  · rw [PCAt, post.pc, show first (writeLog c.σ.mem (headLog sp (R 8) (R 9) (R 18) ra)) Skiplist.globalRoots =
      bytesVal .ld (read8 (writeLog c.σ.mem (headLog sp (R 8) (R 9) (R 18) ra)) Skiplist.globalRoots) from
      (read8_value _ _).symm, head_endpoint, value]
  · have both := (gholds_append _ _).mpr ⟨holds, callee⟩
    apply gholds_select both
    intro n v member
    simp only [ChainScan.ChainLoop.headRegs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [scanR, calleeSaved, lookupG]
  · rw [post.memory, head_eval_log]
  · intro r noise out
    exact post.frame r noise (fun n hn => out n (by revert n hn; generalize (_ == 0#64) = t; cases t <;> decide))

/-! ## The young-list tests as pieces -/

/-- One of the two `s0 = caml_global_roots_young.forward[0]; beqz s0` tests. -/
structure TestSite where
  here : BitVec 64
  onCell : BitVec 64
  block : Bool → BBlock
  chain_ok : ∀ t, ChainOK here [18] [block t]
  code : ∀ {m}, Code.Caml_scan_global_young_rootsLoaded m → ∀ t, ChainCode m [block t]
  regs : ∀ l t, runGM (block t).body testRegs [l] = [(8, bytesVal .ld l), (18, roots)]
  log : ∀ l t, wlogM (block t).body testRegs [l] = []
  written : ∀ t, ∀ n ∈ wrChain [block t], n = 8
  access : ∀ m, ReadWindow youngRoots 8 →
    ChainAccess m testRegs [read8 m Skiplist.globalRootsYoung] [block (first m Skiplist.globalRootsYoung == 0#64)]
  endpoint : ∀ l, evalBlocksPC here (SegEvalState.init testRegs [l]) [block (bytesVal .ld l == 0#64)] =
    if bytesVal .ld l == 0#64 then tailPc else onCell

theorem test_access_of {block : Bool → BBlock} (m : Std.ExtHashMap Nat (BitVec 8)) (read : ReadWindow youngRoots 8)
    (plan : ∀ t, AccessPlan m testRegs [read8 m Skiplist.globalRootsYoung] (block t).body)
    (control : ∀ l t, (bytesVal .ld l == 0#64) = t → TermFactsO (runGM (block t).body testRegs [l]) (block t).term) :
    ChainAccess m testRegs [read8 m Skiplist.globalRootsYoung] [block (first m Skiplist.globalRootsYoung == 0#64)] :=
  ChainAccess.cons ⟨plan _, control _ _ (by rw [read8_value]; rfl)⟩ ChainAccess.nil

/-- **A young-list test**: from the exit of a walk to the next walk's head (or
the epilogue when the young list is empty). -/
theorem stage_test {R sp f c0 d z} {mem : Std.ExtHashMap Nat (BitVec 8)} (T : TestSite)
    (st : GStage c0 T.here (ChainScan.ChainLoop.headRegs (scanR R sp f) z) mem d)
    (read : ReadWindow youngRoots 8) :
    ∃ e, Steps d e ∧ GStage c0 (if first mem Skiplist.globalRootsYoung == 0#64 then tailPc else T.onCell)
      (ChainScan.ChainLoop.headRegs (scanR R sp f) (first mem Skiplist.globalRootsYoung)) mem e := by
  have holds : GHolds d.σ testRegs := ⟨by
    have h : gprGet d.σ 18 = some (scanR R sp f 18) := gholds_lookup _ st.regs rfl
    simpa [scanR] using h, trivial⟩
  have facts := chainPlan_facts (T.code st.code _) (T.access d.σ.mem read)
  obtain ⟨e, run, post⟩ := (block_summary _ T.here testRegs _ d
    ⟨st.good, st.minstret, holds, by change KeysOK [18]; decide, facts, T.chain_ok _, st.tick⟩).run d ⟨st.pc, rfl⟩
  have value : bytesVal .ld (read8 d.σ.mem Skiplist.globalRootsYoung) = first mem Skiplist.globalRootsYoung := by
    rw [read8_value, st.memory]; rfl
  have regsEq : (evalBlocks [T.block (first d.σ.mem Skiplist.globalRootsYoung == 0#64)]
      (SegEvalState.init testRegs [read8 d.σ.mem Skiplist.globalRootsYoung])).regs =
      [(8, bytesVal .ld (read8 d.σ.mem Skiplist.globalRootsYoung)), (18, roots)] := by
    simp only [evalBlocks, evalBlock, SegEvalState.init]
    exact T.regs _ _
  have holdsE := post.regs
  rw [regsEq, value] at holdsE
  have rest : GHolds e.σ (ChainScan.ChainLoop.keptRegs (scanR R sp f)) := by
    apply gholds_of_frame post.frame _ (by change KeysOK [2,9,18,19,20,21,22,23,24,25]; decide) ?_ ?_
      (ChainScan.ChainLoop.kept_of_head st.regs)
    · change ∀ n ∈ [2,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · intro n hn m hm
      rw [T.written _ m hm]
      simp only [ChainScan.ChainLoop.keptRegs, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨e, run, post.good, post.minstret, post.tick, ?_, ?_, ?_, ?_, post.output.trans st.output, ?_⟩
  · exact image_after Code.caml_scan_global_young_roots_transport (by decide) st.code facts post
  · rw [PCAt, post.pc, show first d.σ.mem Skiplist.globalRootsYoung =
      bytesVal .ld (read8 d.σ.mem Skiplist.globalRootsYoung) from (read8_value _ _).symm, T.endpoint, value]
  · have both := (gholds_append _ _).mpr ⟨holdsE, rest⟩
    apply gholds_select both
    intro n v member
    simp only [ChainScan.ChainLoop.headRegs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [ChainScan.ChainLoop.keptRegs, scanR, lookupG]
  · rw [post.memory, st.memory]
    simp only [evalBlocks, evalBlock, SegEvalState.init, T.log, List.append_nil]
    rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by rw [T.written _ n hn]; decide))]
    exact st.frame r noise out

theorem youngTest_plan (m : Std.ExtHashMap Nat (BitVec 8)) (read : ReadWindow youngRoots 8) (t : Bool) :
    AccessPlan m testRegs [read8 m Skiplist.globalRootsYoung] (youngTest t).body := by
  cases t <;>
  simp only [youngTest, caml_scan_global_young_rootsXcd3cTSeg, caml_scan_global_young_rootsXcd3cFSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true] <;>
  chain_facts True.intro <;>
  refine read.ld rfl ?_ (read8_pins _ _) <;>
  simp [testRegs, roots, youngRoots, Skiplist.globalRoots, Skiplist.globalRootsYoung, eaddrM, mkLine, decodeM,
    srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]

theorem youngTest_control (l : List (BitVec 8)) (t : Bool) (h : (bytesVal .ld l == 0#64) = t) :
    TermFactsO (runGM (youngTest t).body testRegs [l]) (youngTest t).term := by
  rw [youngTest_regs l [] t]
  cases t
  · have : bytesVal .ld l ≠ 0#64 := by simpa using h
    simp [youngTest, caml_scan_global_young_rootsXcd3cFSeg, TermFactsO, TermFactsT, srcVal, lookupG, guardB, this]
  · have : bytesVal .ld l = 0#64 := by simpa using h
    simp [youngTest, caml_scan_global_young_rootsXcd3cTSeg, TermFactsO, TermFactsT, srcVal, lookupG, guardB, this]

def youngTestSite : TestSite where
  here := 0x8000cd3c#64
  onCell := 0x8000cd44#64
  block := youngTest
  chain_ok := fun t => by cases t <;> decide
  code := fun hc t => by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst b
    cases t <;> constructor
    all_goals simp only [youngTest, caml_scan_global_young_rootsXcd3cTSeg, caml_scan_global_young_rootsXcd3cFSeg, List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
    all_goals chain_facts hc with "Vsa.Sim.Code.caml_scan_global_young_roots_at_"
  regs := fun l t => youngTest_regs l [] t
  log := fun l t => by cases t <;> rfl
  written := fun t => by cases t <;> decide
  access := fun m read => test_access_of m read (youngTest_plan m read) youngTest_control
  endpoint := fun l => by
    generalize (bytesVal .ld l == 0#64) = t
    cases t <;> rfl

theorem youngRetest_plan (m : Std.ExtHashMap Nat (BitVec 8)) (read : ReadWindow youngRoots 8) (t : Bool) :
    AccessPlan m testRegs [read8 m Skiplist.globalRootsYoung] (youngRetest t).body := by
  cases t <;>
  simp only [youngRetest, caml_scan_global_young_rootsXcd58TSeg, caml_scan_global_young_rootsXcd58FSeg, List.getD_cons_zero, AccessPlan, if_true, if_false, Bool.false_eq_true] <;>
  chain_facts True.intro <;>
  refine read.ld rfl ?_ (read8_pins _ _) <;>
  simp [testRegs, roots, youngRoots, Skiplist.globalRoots, Skiplist.globalRootsYoung, eaddrM, mkLine, decodeM,
    srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]

theorem youngRetest_control (l : List (BitVec 8)) (t : Bool) (h : (bytesVal .ld l == 0#64) = t) :
    TermFactsO (runGM (youngRetest t).body testRegs [l]) (youngRetest t).term := by
  rw [youngRetest_regs l [] t]
  cases t
  · have : bytesVal .ld l ≠ 0#64 := by simpa using h
    simp [youngRetest, caml_scan_global_young_rootsXcd58FSeg, TermFactsO, TermFactsT, srcVal, lookupG, guardB, this]
  · have : bytesVal .ld l = 0#64 := by simpa using h
    simp [youngRetest, caml_scan_global_young_rootsXcd58TSeg, TermFactsO, TermFactsT, srcVal, lookupG, guardB, this]

def youngRetestSite : TestSite where
  here := 0x8000cd58#64
  onCell := 0x8000cd60#64
  block := youngRetest
  chain_ok := fun t => by cases t <;> decide
  code := fun hc t => by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst b
    cases t <;> constructor
    all_goals simp only [youngRetest, caml_scan_global_young_rootsXcd58TSeg, caml_scan_global_young_rootsXcd58FSeg, List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
    all_goals chain_facts hc with "Vsa.Sim.Code.caml_scan_global_young_roots_at_"
  regs := fun l t => youngRetest_regs l [] t
  log := fun l t => by cases t <;> rfl
  written := fun t => by cases t <;> decide
  access := fun m read => test_access_of m read (youngRetest_plan m read) youngRetest_control
  endpoint := fun l => by
    generalize (bytesVal .ld l == 0#64) = t
    cases t <;> rfl

/-! ## The insert loop's blocks -/

def insertLoads (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m cell.toNat, read8 m (cell + 16#64).toNat]

theorem insert_chain_ok : ChainOK insertPc [8] [insertBody] := by decide

theorem insert_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_scan_global_young_rootsLoaded mem) :
    ChainCode mem [insertBody] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  constructor
  all_goals simp only [insertBody, caml_scan_global_young_rootsXcd60Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_scan_global_young_roots_at_"

theorem insert_access (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (w0 : ReadWindow cell 8)
    (w16 : ReadWindow (cell + 16#64) 8) : ChainAccess m [(8, cell)] (insertLoads cell m) [insertBody] := by
  apply ChainAccess.cons ⟨?_, by simp [insertBody, caml_scan_global_young_rootsXcd60Seg, TermFactsO]⟩ ChainAccess.nil
  simp only [insertBody, caml_scan_global_young_rootsXcd60Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · refine w0.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · refine w16.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG, Functions.sign_extend,
      Sail.BitVec.signExtend]

theorem insert_eval_regs (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks [insertBody] (SegEvalState.init [(8, cell)] (insertLoads cell m))).regs = insertArgs cell m := by
  simp only [evalBlocks, evalBlock, SegEvalState.init, insertLoads]
  exact insert_regs cell m

theorem insert_eval_log (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks [insertBody] (SegEvalState.init [(8, cell)] (insertLoads cell m))).log = [] := rfl

theorem insert_endpoint (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    evalBlocksPC insertPc (SegEvalState.init [(8, cell)] (insertLoads cell m)) [insertBody] =
      GlobalRootsSites.insertCall.pc := rfl

theorem insert_written : ∀ n ∈ wrChain [insertBody], n ∈ [8, 10, 11, 12] := by decide

def insertLink : BitVec 64 := 0x8000cd78#64

theorem insertTest_chain_ok (t : Bool) : ChainOK insertLink [8] [insertTest t] := by cases t <;> decide

theorem insertTest_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_scan_global_young_rootsLoaded mem)
    (t : Bool) : ChainCode mem [insertTest t] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  cases t <;> constructor
  all_goals simp only [insertTest, caml_scan_global_young_rootsXcd78TSeg, caml_scan_global_young_rootsXcd78FSeg,
    List.getD_cons_zero, CodeFacts, if_true, if_false, Bool.false_eq_true]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_scan_global_young_roots_at_"

theorem insertTest_access (s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    ChainAccess m [(8, s0)] [] [insertTest (s0 != 0#64)] := by
  apply ChainAccess.cons ⟨?_, ?_⟩ ChainAccess.nil
  · generalize (s0 != 0#64) = t
    cases t <;> simp [insertTest, caml_scan_global_young_rootsXcd78TSeg, caml_scan_global_young_rootsXcd78FSeg,
      AccessPlan]
  · generalize h : (s0 != 0#64) = t
    cases t
    · have : s0 = 0#64 := by simpa using h
      simp [insertTest, caml_scan_global_young_rootsXcd78FSeg, TermFactsO, TermFactsT, runGM, srcVal, lookupG,
        guardB, this]
    · have : s0 ≠ 0#64 := by simpa using h
      simp [insertTest, caml_scan_global_young_rootsXcd78TSeg, TermFactsO, TermFactsT, runGM, srcVal, lookupG,
        guardB, this]

theorem insertTest_endpoint (s0 : BitVec 64) :
    evalBlocksPC insertLink (SegEvalState.init [(8, s0)] []) [insertTest (s0 != 0#64)] =
      if s0 != 0#64 then insertPc else tailPc := by
  generalize (s0 != 0#64) = t
  cases t <;> rfl

theorem insertTest_log (s0 : BitVec 64) (t : Bool) :
    (evalBlocks [insertTest t] (SegEvalState.init [(8, s0)] [])).log = [] := by cases t <;> rfl

theorem insertTest_written (t : Bool) : wrChain [insertTest t] = [] := by cases t <;> rfl

/-! ## One iteration of the insert loop -/

section Insert
variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}

/-- At the insert loop's head: `s0 = cell`, the walk's register view. -/
structure InsertHead (R : Nat → BitVec 64) (sp f cell : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Code.Caml_scan_global_young_rootsLoaded c.σ.mem
  pc : PCAt insertPc c
  registers : GHolds c.σ (ChainScan.ChainLoop.headRegs (scanR R sp f) cell)
  cellRead : ReadWindow cell 8
  linkRead : ReadWindow (cell + 16#64) 8

/-- What the call needs from the caller, at any state with the head's memory. -/
structure InsertReady (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (H : List (Nat × Nat)) (cap : Nat) (cells : List (BitVec 64)) (sp : BitVec 64) (e : Config) : Prop where
  image : ExecutableImage e
  heap : HeapReady H cap e
  shape : Shape e.σ.mem Skiplist.globalRootsOld cells
  frame : NativeFrame (frame sp) Skiplist.opStack

def insertCallRegs (R : Nat → BitVec 64) (sp f cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs :=
  [(10, oldRoots), (11, ChainScan.key m cell), (12, 0#64), (2, frame sp), (8, ChainScan.next m cell), (9, f),
   (18, roots)] ++ calleeSaved R

/-- One insert iteration returned. -/
structure InsertIterated (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (R : Nat → BitVec 64) (sp f cell : BitVec 64) (c after : Config) : Prop where
  call : ∃ e d H cap cells, e.σ.mem = c.σ.mem ∧ InsertReady Shape H cap cells sp e ∧
    Skiplist.Returned H (foot e.σ.mem Skiplist.globalRootsOld cells) (frame sp) insertLink e d ∧
    (∃ cells', Shape d.σ.mem Skiplist.globalRootsOld cells' ∧
      ChainScan.key c.σ.mem cell ∈ Skiplist.keys d.σ.mem cells' ∧
      (∀ k ∈ Skiplist.keys e.σ.mem cells, k ∈ Skiplist.keys d.σ.mem cells') ∧
      (∀ k ∈ Skiplist.keys d.σ.mem cells', k = ChainScan.key c.σ.mem cell ∨ k ∈ Skiplist.keys e.σ.mem cells) ∧
      (∀ a, foot d.σ.mem Skiplist.globalRootsOld cells' a →
        foot e.σ.mem Skiplist.globalRootsOld cells a ∨ VsaIris.VsaHeap.vsaFoot H a)) ∧
    after.σ.mem = d.σ.mem ∧
    PCAt (if ChainScan.next c.σ.mem cell != 0#64 then insertPc else tailPc) after
  registers : GHolds after.σ (ChainScan.ChainLoop.headRegs (scanR R sp f) (ChainScan.next c.σ.mem cell))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  image : ExecutableImage after

theorem insert_iteration {R sp f cell c} (ops : Skiplist.Ops Shape foot) (input : InsertHead R sp f cell c)
    (ready : ∀ e, e.σ.mem = c.σ.mem → ∃ H cap cells, InsertReady Shape H cap cells sp e) :
    FnSummary insertPc (fun d => d = c) (InsertIterated Shape foot R sp f cell c) := by
  have bodyHolds : GHolds c.σ [(8, cell)] := ⟨gholds_lookup _ input.registers rfl, True.intro⟩
  have facts := chainPlan_facts (insert_code input.code) (insert_access cell c.σ.mem input.cellRead input.linkRead)
  constructor
  rintro c0 ⟨pc0, rfl⟩
  obtain ⟨b, run1, bp⟩ := (block_summary [insertBody] insertPc [(8, cell)] (insertLoads cell c0.σ.mem) c0
    ⟨input.good, input.minstret, bodyHolds, by change KeysOK [8]; decide, facts, insert_chain_ok,
      input.tick⟩).run c0 ⟨pc0, rfl⟩
  have bmem : b.σ.mem = c0.σ.mem := by rw [bp.memory, insert_eval_log]; rfl
  have set := bp.regs
  rw [insert_eval_regs] at set
  have kept : GHolds b.σ ((2, frame sp) :: (9, f) :: (18, roots) :: calleeSaved R) := by
    have k := ChainScan.ChainLoop.kept_of_head input.registers
    apply gholds_select (gholds_of_frame bp.frame _ (by change KeysOK [2,9,18,19,20,21,22,23,24,25]; decide)
      (by change ∀ n ∈ [2,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false; decide)
      (fun n hn m hm => by
        have small := insert_written m hm
        simp only [ChainScan.ChainLoop.keptRegs, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn small
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases small with rfl | rfl | rfl | rfl <;> decide) k)
    intro n v member
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [ChainScan.ChainLoop.keptRegs, scanR, lookupG]
  have callHolds : GHolds b.σ (insertCallRegs R sp f cell c0.σ.mem) := by
    have both := (gholds_append _ _).mpr ⟨set, kept⟩
    apply gholds_select both
    intro n v member
    simp only [insertCallRegs, calleeSaved, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
      simp [insertArgs, calleeSaved, lookupG]
  have bpc : PCAt GlobalRootsSites.insertCall.pc b := by rw [PCAt, bp.pc, insert_endpoint]
  obtain ⟨e, run2, called⟩ := (call_summary GlobalRootsSites.insertCall_shape GlobalRootsSites.insertCall_decode b
    (GlobalRootsSites.insertCall_pins (bmem ▸ input.code)) bp.good bp.tick bp.minstret _ callHolds
    (by change KeysOK [10, 11, 12, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]; decide)
    (by change ∀ n ∈ [10, 11, 12, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25], n ≠ 1; decide)).run b ⟨bpc, rfl⟩
  have emem : e.σ.mem = c0.σ.mem := by rw [called.mem, ← bmem]; rfl
  obtain ⟨H, cap, cells, rd⟩ := ready e emem
  have eHolds : GHolds e.σ ((1, insertLink) :: insertCallRegs R sp f cell c0.σ.mem) := ⟨called.ra, called.registers⟩
  have callInput : Skiplist.CallInput H cap [(10, BitVec.ofNat 64 Skiplist.globalRootsOld),
      (11, ChainScan.key c0.σ.mem cell), (12, 0#64)] (frame sp) insertLink e := by
    refine ⟨⟨called.good, rd.image, called.minstret, gholds_lookup _ eHolds rfl, by decide, called.tick⟩, rd.heap,
      ?_, rd.frame⟩
    apply gholds_select eHolds
    intro n v member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h <;> cases h <;> rfl
  have target : GlobalRootsSites.insertCall.target = Skiplist.insertPc := by decide
  obtain ⟨d, run3, ret, cells', shape', mem', old', only', foot'⟩ :=
    (ops.insert H cap Skiplist.globalRootsOld cells _ (frame sp) insertLink e rd.shape callInput).run e
      ⟨by rw [← target]; exact called.pc, rfl⟩
  have next : gprGet d.σ 8 = some (ChainScan.next c0.σ.mem cell) := by
    rw [ret.saved 8 (by decide)]; exact gholds_lookup _ eHolds rfl
  have dHead : GHolds d.σ (ChainScan.ChainLoop.headRegs (scanR R sp f) (ChainScan.next c0.σ.mem cell)) := by
    apply gholds_select (show GHolds d.σ ((8, ChainScan.next c0.σ.mem cell) :: (2, frame sp) :: (9, f) ::
      (18, roots) :: calleeSaved R) from ?_)
    · intro n v member
      simp only [ChainScan.ChainLoop.headRegs, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> simp [scanR, calleeSaved, lookupG]
    · refine ⟨next, ret.stack, ?_, ?_, ?_⟩
      · rw [ret.saved 9 (by decide)]; exact gholds_lookup _ eHolds rfl
      · rw [ret.saved 18 (by decide)]; exact gholds_lookup _ eHolds rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
        all_goals first
          | (rw [ret.saved 19 (by decide)]; exact gholds_lookup _ eHolds rfl)
          | (rw [ret.saved 20 (by decide)]; exact gholds_lookup _ eHolds rfl)
          | (rw [ret.saved 21 (by decide)]; exact gholds_lookup _ eHolds rfl)
          | (rw [ret.saved 22 (by decide)]; exact gholds_lookup _ eHolds rfl)
          | (rw [ret.saved 23 (by decide)]; exact gholds_lookup _ eHolds rfl)
          | (rw [ret.saved 24 (by decide)]; exact gholds_lookup _ eHolds rfl)
          | (rw [ret.saved 25 (by decide)]; exact gholds_lookup _ eHolds rfl)
  have dcode := GlobalRootsSites.image_loaded ret.image
  have dpc : PCAt insertLink d := ret.pc
  have testHolds : GHolds d.σ [(8, ChainScan.next c0.σ.mem cell)] := ⟨next, True.intro⟩
  obtain ⟨after, run4, tp⟩ := (block_summary [insertTest (ChainScan.next c0.σ.mem cell != 0#64)] insertLink
    [(8, ChainScan.next c0.σ.mem cell)] [] d
    ⟨ret.good, ret.minstret, testHolds, by change KeysOK [8]; decide,
      chainPlan_facts (insertTest_code dcode _) (insertTest_access _ d.σ.mem), insertTest_chain_ok _,
      ret.tick⟩).run d ⟨dpc, rfl⟩
  have headAfter : GHolds after.σ (ChainScan.ChainLoop.headRegs (scanR R sp f) (ChainScan.next c0.σ.mem cell)) := by
    apply gholds_of_frame tp.frame _ (by change KeysOK [2,8,9,18,19,20,21,22,23,24,25]; decide) ?_ ?_ dHead
    · change ∀ n ∈ [2,8,9,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · intro n _ m hm
      rw [insertTest_written] at hm
      cases hm
  have amem : after.σ.mem = d.σ.mem := by rw [tp.memory, insertTest_log]; rfl
  refine ⟨after, run1.trans (run2.trans (run3.trans run4)), ⟨⟨e, d, H, cap, cells, emem, rd, ret,
    ⟨cells', shape', mem', old', only', foot'⟩, amem, ?_⟩, headAfter, tp.good, tp.tick, tp.minstret, ?_⟩⟩
  · rw [PCAt, tp.pc, insertTest_endpoint]
  · exact image_of_writeLog (log := []) ret.image ⟨trivial, trivial⟩ (by rw [amem]; rfl)

/-- **The insert loop's obligations** for a caller invariant `Inv`, exit
condition `Done` and rank (the remaining young chain). -/
structure InsertStep (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (R : Nat → BitVec 64) (sp f : BitVec 64) (Inv : BitVec 64 → Config → Prop) (Done : Config → Prop)
    (rank : Config → Nat) : Prop where
  head : ∀ cell c, Inv cell c → InsertHead R sp f cell c
  ready : ∀ cell c, Inv cell c → ∀ e, e.σ.mem = c.σ.mem → ∃ H cap cells, InsertReady Shape H cap cells sp e
  next : ∀ cell c after, Inv cell c → InsertIterated Shape foot R sp f cell c after → PCAt insertPc after →
    Inv (ChainScan.next c.σ.mem cell) after
  done : ∀ cell c after, Inv cell c → InsertIterated Shape foot R sp f cell c after → PCAt tailPc after → Done after
  donePc : ∀ c, Done c → PCAt tailPc c
  progress : ∀ cell c after, Inv cell c → InsertIterated Shape foot R sp f cell c after → rank after < rank c

theorem tail_ne_insert : tailPc ≠ insertPc := by decide

/-- **The insert loop**, from any invariant state at its head to `Done`. -/
theorem insert_loop {R sp f} {Inv : BitVec 64 → Config → Prop} {Done : Config → Prop} {rank : Config → Nat}
    (ops : Skiplist.Ops Shape foot) (step : InsertStep Shape foot R sp f Inv Done rank) :
    Vsa.Logic.Triple (fun c => ∃ cell, Inv cell c) Done := by
  apply loop_to_exit (entry := insertPc) rank
  · rintro c ⟨cell, inv⟩
    exact (step.head cell c inv).pc
  · intro c done onBody
    have exitAt := step.donePc c done
    rw [PCAt] at exitAt onBody
    rw [exitAt] at onBody
    exact tail_ne_insert (Option.some.inj onBody)
  · rintro c ⟨cell, inv⟩
    have input := step.head cell c inv
    obtain ⟨after, run, post⟩ := (insert_iteration ops input (step.ready cell c inv)).run c ⟨input.pc, rfl⟩
    refine ⟨after, run, ?_, step.progress cell c after inv post⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, pc⟩ := post.call
    by_cases more : (ChainScan.next c.σ.mem cell != 0#64) = true
    · rw [if_pos more] at pc
      exact Or.inl ⟨_, step.next cell c after inv post pc⟩
    · rw [if_neg more] at pc
      exact Or.inr (step.done cell c after inv post pc)

end Insert

/-! ## The epilogue: restore, tail-call `caml_skiplist_empty(&caml_global_roots_young)` -/

theorem tail_chain_ok : ChainOK tailPc [2] [tailBlock] := by decide

theorem tail_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_scan_global_young_rootsLoaded mem) :
    ChainCode mem [tailBlock] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  constructor
  all_goals simp only [tailBlock, caml_scan_global_young_rootsXcd7cSeg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_scan_global_young_roots_at_"

theorem tail_access (fsp : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (windows : ∀ off ∈ [16, 24, 8, 0], ReadWindow (fsp + BitVec.ofNat 64 off) 8) :
    ChainAccess m [(2, fsp)] [read8 m (fsp + 16#64).toNat, read8 m (fsp + 24#64).toNat, read8 m (fsp + 8#64).toNat,
      read8 m (fsp + 0#64).toNat] [tailBlock] := by
  refine ChainAccess.cons ⟨?_, ?_⟩ ChainAccess.nil
  · simp only [tailBlock, caml_scan_global_young_rootsXcd7cSeg, List.getD_cons_zero, AccessPlan]
    chain_facts True.intro
    · exact (windows 16 (by decide)).ld rfl rfl (read8_pins _ _)
    · exact (windows 24 (by decide)).ld rfl rfl (read8_pins _ _)
    · exact (windows 8 (by decide)).ld rfl rfl (read8_pins _ _)
    · exact (windows 0 (by decide)).ld rfl rfl (read8_pins _ _)
  · rw [tail_regs]
    simp [tailBlock, caml_scan_global_young_rootsXcd7cSeg, TermFactsO, TermFactsT]

theorem tail_eval_regs (fsp : BitVec 64) (r1 r2 r3 r4 : List (BitVec 8)) :
    (evalBlocks [tailBlock] (SegEvalState.init [(2, fsp)] [r1, r2, r3, r4])).regs = restored fsp r1 r2 r3 r4 := by
  simp only [evalBlocks, evalBlock, SegEvalState.init]
  exact tail_regs fsp r1 r2 r3 r4

theorem tail_eval_log (fsp : BitVec 64) (r1 r2 r3 r4 : List (BitVec 8)) :
    (evalBlocks [tailBlock] (SegEvalState.init [(2, fsp)] [r1, r2, r3, r4])).log = [] := rfl

theorem tail_endpoint (fsp : BitVec 64) (r1 r2 r3 r4 : List (BitVec 8)) :
    evalBlocksPC tailPc (SegEvalState.init [(2, fsp)] [r1, r2, r3, r4]) [tailBlock] = Skiplist.emptyPc := rfl

theorem tail_written : ∀ n ∈ wrChain [tailBlock], n ∈ [1, 2, 8, 9, 10, 18] := by decide

theorem frame_restore (sp : BitVec 64) : frame sp + 32#64 = sp := by
  rw [frame, BitVec.add_assoc]
  have : (18446744073709551584#64 + 32#64 : BitVec 64) = 0#64 := by decide
  rw [this, BitVec.add_zero]

section Tail
variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}

/-- What `caml_skiplist_empty` needs from the caller at the tail call. -/
structure EmptyReady (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (H : List (Nat × Nat)) (cap : Nat) (cells : List (BitVec 64)) (sp : BitVec 64) (e : Config) : Prop where
  image : ExecutableImage e
  heap : HeapReady H cap e
  shape : Shape e.σ.mem Skiplist.globalRootsYoung cells
  frame : NativeFrame sp Skiplist.opStack

/-- The scan returned: `caml_skiplist_empty`'s return to the scan's caller,
with the caller's `sp`, `s0`–`s2` and `s3`–`s9`. -/
structure Finished (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (R : Nat → BitVec 64) (sp ra : BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8)) (after : Config) : Prop where
  emptied : ∃ e H cap cells, e.σ.mem = mem ∧ EmptyReady Shape H cap cells sp e ∧
    Skiplist.Returned H (foot e.σ.mem Skiplist.globalRootsYoung cells) sp ra e after ∧
    Shape after.σ.mem Skiplist.globalRootsYoung [] ∧
    (∀ a, foot after.σ.mem Skiplist.globalRootsYoung [] a → foot e.σ.mem Skiplist.globalRootsYoung cells a)
  registers : GHolds after.σ ([(2, sp), (8, R 8), (9, R 9), (18, R 18)] ++ calleeSaved R)

/-- **The epilogue**: restore the frame and tail-call `caml_skiplist_empty`. -/
theorem stage_tail {R sp ra c0 d} {mem : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    (ops : Skiplist.Ops Shape foot) (st : GStage c0 tailPc L mem d)
    (sp2 : lookupG 2 L = some (frame sp)) (callee : GHolds d.σ (calleeSaved R))
    (windows : ∀ off ∈ [16, 24, 8, 0], ReadWindow (frame sp + BitVec.ofNat 64 off) 8)
    (savedS0 : bytesT mem (frame sp + 16#64).toNat 8 = R 8) (savedRa : bytesT mem (frame sp + 24#64).toNat 8 = ra)
    (savedS1 : bytesT mem (frame sp + 8#64).toNat 8 = R 9) (savedS2 : bytesT mem (frame sp + 0#64).toNat 8 = R 18)
    (aligned : ra.toNat % 4 = 0)
    (ready : ∀ e, e.σ.mem = mem → ∃ H cap cells, EmptyReady Shape H cap cells sp e) :
    ∃ after, Steps d after ∧ Finished Shape foot R sp ra mem after := by
  have spHolds : GHolds d.σ [(2, frame sp)] := ⟨gholds_lookup _ st.regs sp2, trivial⟩
  have facts := chainPlan_facts (tail_code st.code) (tail_access (frame sp) d.σ.mem windows)
  obtain ⟨e, run1, post⟩ := (block_summary [tailBlock] tailPc [(2, frame sp)] _ d
    ⟨st.good, st.minstret, spHolds, by change KeysOK [2]; decide, facts, tail_chain_ok, st.tick⟩).run d ⟨st.pc, rfl⟩
  have emem : e.σ.mem = mem := by rw [post.memory, tail_eval_log, ← st.memory]; rfl
  have holds := post.regs
  rw [tail_eval_regs] at holds
  unfold restored at holds
  rw [frame_restore, read8_value, read8_value, read8_value, read8_value, st.memory, savedS0, savedRa, savedS1,
    savedS2] at holds
  have calleeE : GHolds e.σ (calleeSaved R) := by
    apply gholds_of_frame post.frame _ (by change KeysOK [19, 20, 21, 22, 23, 24, 25]; decide) ?_ ?_ callee
    · change ∀ n ∈ [19, 20, 21, 22, 23, 24, 25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · intro n hn m hm
      have small := tail_written m hm
      simp only [calleeSaved, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn small
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases small with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨H, cap, cells, rd⟩ := ready e emem
  have callInput : Skiplist.CallInput H cap [(10, BitVec.ofNat 64 Skiplist.globalRootsYoung)] sp ra e := by
    refine ⟨⟨post.good, rd.image, post.minstret, gholds_lookup _ holds rfl, aligned, post.tick⟩, rd.heap, ?_, rd.frame⟩
    apply gholds_select holds
    intro n v member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> rfl
  have epc : PCAt Skiplist.emptyPc e := by rw [PCAt, post.pc, tail_endpoint]
  obtain ⟨after, run2, ret, shape, shrinks⟩ :=
    (ops.empty H cap Skiplist.globalRootsYoung cells sp ra e rd.shape callInput).run e ⟨epc, rfl⟩
  have four : GHolds after.σ [(2, sp), (8, R 8), (9, R 9), (18, R 18)] := by
    refine ⟨ret.stack, ?_, ?_, ?_, trivial⟩
    · rw [ret.saved 8 (by decide)]; exact gholds_lookup _ holds rfl
    · rw [ret.saved 9 (by decide)]; exact gholds_lookup _ holds rfl
    · rw [ret.saved 18 (by decide)]; exact gholds_lookup _ holds rfl
  have calleeA : GHolds after.σ (calleeSaved R) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [ret.saved 19 (by decide)]; exact gholds_lookup _ calleeE rfl
    · rw [ret.saved 20 (by decide)]; exact gholds_lookup _ calleeE rfl
    · rw [ret.saved 21 (by decide)]; exact gholds_lookup _ calleeE rfl
    · rw [ret.saved 22 (by decide)]; exact gholds_lookup _ calleeE rfl
    · rw [ret.saved 23 (by decide)]; exact gholds_lookup _ calleeE rfl
    · rw [ret.saved 24 (by decide)]; exact gholds_lookup _ calleeE rfl
    · rw [ret.saved 25 (by decide)]; exact gholds_lookup _ calleeE rfl
  exact ⟨after, run1.trans run2, ⟨e, H, cap, cells, emem, rd, ret, shape, shrinks⟩, (gholds_append _ _).mpr ⟨four, calleeA⟩⟩

end Tail

end OCaml.Vm.Gc.GlobalScan
