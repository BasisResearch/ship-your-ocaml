import OCaml.Vm.Gc.Skiplist
import OCaml.Vm.Boot.Startup.SkipFirstEval
import OCaml.Vm.Boot.Startup.SkipFirstImage
import OCaml.Vm.Boot.Startup.SkipFirstCallInterface
import OCaml.Vm.Boot.Startup.StatChecked
import OCaml.Vm.Boot.Startup.StatCheckedFrame
import OCaml.Vm.Boot.Startup.CallerFrame
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Primitives.BlockPins
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Gc.SkiplistFirst
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap

/-- First registration uses the zero-initialized global header and PRNG seed. -/
structure Empty (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  header : ∀ k < Skiplist.headerBytes, (m[Skiplist.globalRoots + k]?).getD 0 = 0
  seed : ∀ k < 4, (m[Skiplist.randomSeed + k]?).getD 0 = 0

def sk : BitVec 64 := BitVec.ofNat 64 Skiplist.globalRoots

def headBlocks : List BBlock :=
  caml_skiplist_insertXaafcFSeg ++
  caml_skiplist_insertXab10Seg ++
  caml_skiplist_insertXab3cFSeg ++
  caml_skiplist_insertXab48FSeg ++
  caml_skiplist_insertXab58TSeg ++
  caml_skiplist_insertXab68TSeg ++
  caml_skiplist_insertXaca4TSeg ++
  caml_skiplist_insertXacb8Seg

def input (sp ra key s0 s1 : BitVec 64) : GRegs :=
  [(2,sp),(1,ra),(10,sk),(11,key),(12,0),(8,s0),(9,s1)]
def zero4 : List (BitVec 8) := [0,0,0,0]
def zero8 : List (BitVec 8) := [0,0,0,0,0,0,0,0]
def loads : List (List (BitVec 8)) := [zero4,zero8,zero8,zero4]

attribute [local simp]
  skipfirst_line_8002aafc
  skipfirst_line_8002ab00
  skipfirst_line_8002ab04
  skipfirst_line_8002ab08
  skipfirst_line_8002ab10
  skipfirst_line_8002ab14
  skipfirst_line_8002ab18
  skipfirst_line_8002ab1c
  skipfirst_line_8002ab20
  skipfirst_line_8002ab24
  skipfirst_line_8002ab28
  skipfirst_line_8002ab30
  skipfirst_line_8002ab38
  skipfirst_line_8002ab3c
  skipfirst_line_8002ab40
  skipfirst_line_8002ab48
  skipfirst_line_8002ab4c
  skipfirst_line_8002ab50
  skipfirst_line_8002ab58
  skipfirst_line_8002ab60
  skipfirst_line_8002ab68
  skipfirst_line_8002ab6c
  skipfirst_line_8002ab70
  skipfirst_line_8002ab74
  skipfirst_line_8002ab78
  skipfirst_line_8002ab7c
  skipfirst_line_8002ab80
  skipfirst_line_8002ab84
  skipfirst_line_8002ab88
  skipfirst_line_8002ab8c
  skipfirst_line_8002ab90
  skipfirst_line_8002ab94
  skipfirst_line_8002ab98
  skipfirst_line_8002ab9c
  skipfirst_line_8002aba0
  skipfirst_line_8002aba4
  skipfirst_line_8002aba8
  skipfirst_line_8002abac
  skipfirst_line_8002abb0
  skipfirst_line_8002abb4
  skipfirst_line_8002abb8
  skipfirst_line_8002abbc
  skipfirst_line_8002abc0
  skipfirst_line_8002abc4
  skipfirst_line_8002abcc
  skipfirst_line_8002abd0
  skipfirst_line_8002abd4
  skipfirst_line_8002abd8
  skipfirst_line_8002abdc
  skipfirst_line_8002abe8
  skipfirst_line_8002abec
  skipfirst_line_8002abf0
  skipfirst_line_8002abf4
  skipfirst_line_8002abfc
  skipfirst_line_8002ac00
  skipfirst_line_8002ac04
  skipfirst_line_8002ac0c
  skipfirst_line_8002ac10
  skipfirst_line_8002ac14
  skipfirst_line_8002ac18
  skipfirst_line_8002ac1c
  skipfirst_line_8002ac20
  skipfirst_line_8002ac24
  skipfirst_line_8002ac28
  skipfirst_line_8002ac2c
  skipfirst_line_8002ac30
  skipfirst_line_8002ac34
  skipfirst_line_8002ac38
  skipfirst_line_8002ac40
  skipfirst_line_8002ac44
  skipfirst_line_8002ac48
  skipfirst_line_8002ac4c
  skipfirst_line_8002ac50
  skipfirst_line_8002ac58
  skipfirst_line_8002ac5c
  skipfirst_line_8002ac60
  skipfirst_line_8002ac64
  skipfirst_line_8002ac6c
  skipfirst_line_8002ac70
  skipfirst_line_8002ac74
  skipfirst_line_8002ac78
  skipfirst_line_8002ac7c
  skipfirst_line_8002ac80
  skipfirst_line_8002ac88
  skipfirst_line_8002ac90
  skipfirst_line_8002ac94
  skipfirst_line_8002ac98
  skipfirst_line_8002ac9c
  skipfirst_line_8002aca8
  skipfirst_line_8002acac
  skipfirst_line_8002acb0
  skipfirst_line_8002acb8
  skipfirst_line_8002acc0
  skipfirst_line_8002acc4
  skipfirst_line_8002acc8

@[local simp] theorem zero4_value : bytesVal .lw zero4 = 0#64 := rfl
@[local simp] theorem zero8_value : bytesVal .ld zero8 = 0#64 := rfl

local macro "skip_nf" : tactic => `(tactic|
  simp [headBlocks,
    input,
    loads,
    sk,
    caml_skiplist_insertXaafcFSeg,
    caml_skiplist_insertXab10Seg,
    caml_skiplist_insertXab3cFSeg,
    caml_skiplist_insertXab48FSeg,
    caml_skiplist_insertXab58TSeg,
    caml_skiplist_insertXab68TSeg,
    caml_skiplist_insertXaca4TSeg,
    caml_skiplist_insertXacb8Seg,
    evalBlocks,
    evalBlock,
    SegEvalState.init,
    runGM,
    ldsRunM,
    wlogM,
    stepGM,
    stepLdsM,
    eaddrM,
    srcVal,
    lookupG,
    eraseG,
    wvalM,
    wentryM,
    widthOfM,
    imm20Of,
    List.headD_cons,
    List.tail_cons,
    Option.getD_some,
    Nat.reduceEqDiff,
    ite_true,
    ite_false, Functions.sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
    BitVec.add_assoc])

local macro "prefix_stages" : tactic => `(tactic|
  simp only [input, loads, zero4, zero8, SkipFirstEval.stage0_regs sp ra key s0 s1, SkipFirstEval.stage0_loads sp ra key s0 s1, SkipFirstEval.stage0_log sp ra key s0 s1, SkipFirstEval.stage1_regs sp ra key s0 s1, SkipFirstEval.stage1_loads sp ra key s0 s1, SkipFirstEval.stage1_log sp ra key s0 s1, SkipFirstEval.stage2_regs sp ra key s0 s1, SkipFirstEval.stage2_loads sp ra key s0 s1, SkipFirstEval.stage2_log sp ra key s0 s1, SkipFirstEval.stage3_regs sp ra key s0 s1, SkipFirstEval.stage3_loads sp ra key s0 s1, SkipFirstEval.stage3_log sp ra key s0 s1, SkipFirstEval.stage4_regs sp ra key s0 s1, SkipFirstEval.stage4_loads sp ra key s0 s1, SkipFirstEval.stage4_log sp ra key s0 s1, SkipFirstEval.stage5_regs sp ra key s0 s1, SkipFirstEval.stage5_loads sp ra key s0 s1, SkipFirstEval.stage5_log sp ra key s0 s1, SkipFirstEval.stage6_regs sp ra key s0 s1, SkipFirstEval.stage6_loads sp ra key s0 s1, SkipFirstEval.stage6_log sp ra key s0 s1, SkipFirstEval.stage7_regs sp ra key s0 s1, SkipFirstEval.stage7_loads sp ra key s0 s1, SkipFirstEval.stage7_log sp ra key s0 s1])

theorem Empty.level {m} (e : Empty m) : LPins4 m (Skiplist.globalRoots + 136) zero4 := by
  exact ⟨e.header 136 (by decide), e.header 137 (by decide), e.header 138 (by decide), e.header 139 (by decide)⟩

theorem Empty.first {m} (e : Empty m) : LPins8 m Skiplist.globalRoots zero8 := by
  exact ⟨e.header 0 (by decide), e.header 1 (by decide), e.header 2 (by decide), e.header 3 (by decide),
    e.header 4 (by decide), e.header 5 (by decide), e.header 6 (by decide), e.header 7 (by decide)⟩

theorem Empty.random {m} (e : Empty m) : LPins4 m Skiplist.randomSeed zero4 := by
  exact ⟨e.seed 0 (by decide), e.seed 1 (by decide), e.seed 2 (by decide), e.seed 3 (by decide)⟩

/-- Natural addresses of native slots, after the evaluator combines immediates. -/
theorem slot_nat {sp} (frame : NativeFrame sp 192) (off : Nat) (bound : off ≤ 192) :
    (sp + (-192#64 + BitVec.ofNat 64 off)).toNat = nativeFrameBase sp 192 + off := by
  have h := congrArg BitVec.toNat (frame.address off bound)
  rw [frame.slot_nat bound] at h
  simpa only [BitVec.add_assoc] using h

local macro "skip_past" : tactic => `(tactic| (
  repeat (first | rw [stepMemM_store rfl] | rw [stepMemM_skip rfl])
  repeat (refine memFacts_writeLog ?_ ?_)))

theorem prefix_facts {c sp ra key s0 s1} (leaf : LeafInput ra c) (frame : NativeFrame sp 192)
    (empty : Empty c.σ.mem) : ChainFacts c.σ.mem c.σ.mem (input sp ra key s0 s1) loads headBlocks := by
  have code := skipFirst_code leaf.image
  chain_facts code with "Vsa.Sim.Code.caml_skiplist_insert_at_"
  all_goals prefix_stages
  all_goals skip_nf
  all_goals trace_state

def prefixLog (sp ra s0 s1 : BitVec 64) : List WEntry :=
  [(nativeFrameBase sp 192 + 184,8,ra), (nativeFrameBase sp 192 + 24,8,sk),
   (Skiplist.randomSeed,4,25173), (nativeFrameBase sp 192 + 176,8,s0),
   (nativeFrameBase sp 192 + 168,8,s1)]

def prefixRegs (sp key : BitVec 64) : GRegs :=
  [(10,24),(16,sk),(8,key),(9,0),(13,0),(15,0xffffffffc0000000),(14,25173),
   (17,0xfffffffffffffff8),(29,nativeStack sp 192 + 24),(28,0xfffffffffffffff8),
   (6,0),(2,nativeStack sp 192),(11,key),(12,0)]

def prefixFullRegs (sp ra key : BitVec 64) : GRegs :=
  [(10,24),(16,sk),(8,key),(9,0),(13,0),(15,0xffffffffc0000000),(14,25173),
   (17,0xfffffffffffffff8),(29,nativeStack sp 192 + 24),(28,0xfffffffffffffff8),
   (6,0),(2,nativeStack sp 192),(1,ra),(11,key),(12,0)]

def prefixWrites : List Nat := [2,6,13,15,28,17,29,14,8,9,16,10]

theorem prefix_log {sp ra key s0 s1} (frame : NativeFrame sp 192) :
    (evalBlocks headBlocks (SegEvalState.init (input sp ra key s0 s1) loads)).log = prefixLog sp ra s0 s1 := by
  simp only [headBlocks, evalBlocks, evalBlock, SegEvalState.init]
  prefix_stages
  skip_nf
  simp only [prefixLog, slot_nat frame 184 (by decide), slot_nat frame 24 (by decide),
    slot_nat frame 176 (by decide), slot_nat frame 168 (by decide)]

theorem prefix_regs (sp ra key s0 s1 : BitVec 64) :
    (evalBlocks headBlocks (SegEvalState.init (input sp ra key s0 s1) loads)).regs = prefixFullRegs sp ra key := by
  simp only [headBlocks, evalBlocks, evalBlock, SegEvalState.init]
  prefix_stages
  skip_nf
  simp [prefixFullRegs, nativeStack, sk, BitVec.add_assoc]

theorem prefix_out {sp ra s0 s1 a n} (frame : NativeFrame sp 192)
    (below : a + n ≤ heapEnd) (seed : a + n ≤ Skiplist.randomSeed ∨ Skiplist.randomSeed + 4 ≤ a) :
    OutLRange (prefixLog sp ra s0 s1) a n := by
  have lo := frame.lower
  simp only [prefixLog, OutLRange, and_true]
  unfold nativeFrameBase at *
  exact ⟨Or.inl (by omega), Or.inl (by omega), seed, Or.inl (by omega), Or.inl (by omega)⟩

theorem prefix_outside {sp ra s0 s1} (frame : NativeFrame sp 192) : ImageOutside (prefixLog sp ra s0 s1) := by
  constructor
  · exact prefix_out frame (by decide) (Or.inl (by decide))
  · exact prefix_out frame (by decide) (Or.inl (by decide))

/-- Native search of the empty level-0 list and zero-seed random-level path,
ending immediately before the real checked allocation call. -/
theorem prepare (c : Config) (sp ra key s0 s1 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 192) (empty : Empty c.σ.mem)
    (regs : GHolds c.σ (input sp ra key s0 s1)) :
    FnSummary Skiplist.insertPc (fun d => d = c)
      (WriteRegistersPost prefixWrites (prefixLog sp ra s0 s1) c jal_8002acbc_call.pc 24 (prefixRegs sp key)) := by
  apply registers_of_blocks' leaf.image (prefix_outside frame)
    (block_summary headBlocks Skiplist.insertPc (input sp ra key s0 s1) loads c {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,1,10,11,12,8,9]; decide
      shape := by change ChainOK _ [2,1,10,11,12,8,9] _; decide
      facts := prefix_facts leaf frame empty })
  · exact prefix_log frame
  · rfl
  · intro σ pins
    rw [prefix_regs] at pins
    exact holds_project pins (by simp [prefixRegs, prefixFullRegs, lookupG])
  · rfl
  · decide

/-- The 24-byte level-0 skipcell allocated by the first call. -/
structure Cell (p : BitVec 64) : Prop where
  low : heapStart ≤ p.toNat
  high : p.toNat + 24 ≤ heapEnd
  aligned : p.toNat % 16 = 0

theorem Cell.addr {p} (C : Cell p) (off : Nat) (bound : off ≤ 24) :
    (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
  have high := C.high
  unfold heapEnd at high
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Cell.word {p} (C : Cell p) (off : Nat) (bound : off + 8 ≤ 24) (aligned : off % 8 = 0) :
    WriteWindow (p + BitVec.ofNat 64 off) 8 := by
  have lo := C.low
  have hi := C.high
  have al := C.aligned
  constructor <;> rw [C.addr off (by omega)]
  all_goals simp only [heapStart, heapEnd, Layout.sym_tohost] at *
  all_goals omega

def finishBlocks : List BBlock := caml_skiplist_insertXacc0Seg ++ caml_skiplist_insertXac0cSeg ++
  caml_skiplist_insertXac24FSeg ++ caml_skiplist_insertXac40Seg

def finishInput (sp p key : BitVec 64) : GRegs := [(2,nativeStack sp 192),(10,p),(8,key),(9,0)]
def finishLoads (c : Config) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 192 + 24), read8 c.σ.mem Skiplist.globalRoots,
   read8 c.σ.mem (nativeFrameBase sp 192 + 176), read8 c.σ.mem (nativeFrameBase sp 192 + 184),
   read8 c.σ.mem (nativeFrameBase sp 192 + 168)]
def finishLog (p key : BitVec 64) : List WEntry :=
  [(p.toNat,8,key),(p.toNat+8,8,0),(p.toNat+16,8,0),(Skiplist.globalRoots,8,p)]
def finishRegs (sp ra s0 s1 p : BitVec 64) : GRegs :=
  [(2,sp),(10,0),(9,s1),(1,ra),(8,s0),(14,nativeStack sp 192 + 32),(13,p+24),(12,sk),(15,nativeStack sp 192+32),(11,0)]

/-- Data pins at the allocator return; these are derived from the setup and
allocator frame when the complete first-call summary is composed. -/
structure FinishMemory (m : Std.ExtHashMap Nat (BitVec 8)) (sp ra s0 s1 : BitVec 64) : Prop where
  update : bytesT m (nativeFrameBase sp 192 + 24) 8 = sk
  first : bytesT m Skiplist.globalRoots 8 = 0
  saved0 : bytesT m (nativeFrameBase sp 192 + 176) 8 = s0
  savedRa : bytesT m (nativeFrameBase sp 192 + 184) 8 = ra
  saved1 : bytesT m (nativeFrameBase sp 192 + 168) 8 = s1

local macro "finish_nf" : tactic => `(tactic| (
  simp only [finishBlocks, finishInput, finishLoads, caml_skiplist_insertXacc0Seg,
    caml_skiplist_insertXac0cSeg, caml_skiplist_insertXac24FSeg, caml_skiplist_insertXac40Seg]
  skip_nf))

end OCaml.Vm.Gc.SkiplistFirst
