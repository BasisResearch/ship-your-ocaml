import OCaml.Vm.Gc.Skiplist
import OCaml.Vm.Boot.Startup.SkipFirstEval
import OCaml.Vm.Boot.Startup.SkipFirstImage
import OCaml.Vm.Boot.Startup.SkipFirstCallInterface
import OCaml.Vm.Boot.Startup.StatChecked
import OCaml.Vm.Boot.Startup.StatCheckedFrame
import OCaml.Vm.Boot.Startup.CallerFrame
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Primitives.BlockPins
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Gc.SkiplistFirst
-- The generated normalization tactic is shared across different goal shapes.
set_option linter.unusedSimpArgs false
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
  [(2,sp),(1,ra),(10,sk),(11,key),(12,0#64),(8,s0),(9,s1)]
def zero4 : List (BitVec 8) := [0#8,0#8,0#8,0#8]
def zero8 : List (BitVec 8) := [0#8,0#8,0#8,0#8,0#8,0#8,0#8,0#8]
def loads : List (List (BitVec 8)) := [zero4,zero8,zero8,zero4]

@[local simp] theorem zero4_value : bytesVal .lw zero4 = 0#64 := rfl
@[local simp] theorem zero8_value : bytesVal .ld zero8 = 0#64 := rfl

local macro "prefix_stages" sp:ident ra:ident key:ident s0:ident s1:ident : tactic => `(tactic| (
  simp only [input, sk, Skiplist.globalRoots, loads, zero4, zero8]
  skip_first_stages $sp $ra $key $s0 $s1))

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

theorem stack_word {sp} (frame : NativeFrame sp 192) (off : Nat) (c : BitVec 64)
    (offset : -192#64 + BitVec.ofNat 64 off = c)
    (bound : off + 8 ≤ 192) (aligned : off % 8 = 0) : WriteWindow (sp + c) 8 := by
  have hw := frame.word bound aligned
  rw [← frame.address off (by omega)] at hw
  simpa only [BitVec.add_assoc, offset] using hw

theorem stack_nat {sp} (frame : NativeFrame sp 192) (off : Nat) (c : BitVec 64)
    (offset : -192#64 + BitVec.ofNat 64 off = c) (bound : off ≤ 192) :
    (sp + c).toNat = nativeFrameBase sp 192 + off := by
  rw [← offset]
  exact slot_nat frame off bound

local macro "skip_misses" fr:term : tactic => `(tactic| (
  intro _
  try simp only [SkipFirstEval.i8002ab04_address, SkipFirstEval.i8002ab40_address,
    SkipFirstEval.i8002ab58_address, SkipFirstEval.i8002ab6c_address]
  simp only [skipfirst_line_8002ab04, skipfirst_line_8002ab40, skipfirst_line_8002ab58,
    skipfirst_line_8002ab6c, widthOfM, OutLRange, and_true,
    stack_nat $fr 184 18446744073709551608#64 (by decide) (by decide),
    stack_nat $fr 24 18446744073709551448#64 (by decide) (by decide),
    BitVec.toNat_ofNat, Nat.reduceMod] <;>
    (have lower := ($fr).lower
     simp only [heapEnd] at lower
     unfold nativeFrameBase
     omega)))

theorem prefix_facts {c sp ra key s0 s1} (leaf : LeafInput ra c) (frame : NativeFrame sp 192)
    (empty : Empty c.σ.mem) : ChainFacts c.σ.mem c.σ.mem (input sp ra key s0 s1) loads headBlocks := by
  have code := skipFirst_code leaf.image
  simp only [headBlocks, caml_skiplist_insertXaafcFSeg, caml_skiplist_insertXab10Seg, caml_skiplist_insertXab3cFSeg, caml_skiplist_insertXab48FSeg, caml_skiplist_insertXab58TSeg, caml_skiplist_insertXab68TSeg, caml_skiplist_insertXaca4TSeg, caml_skiplist_insertXacb8Seg, List.append_nil, List.cons_append, ChainFacts, BBlockFacts, ProgFactsM, input, sk, Skiplist.globalRoots, loads, zero4, zero8]
  skip_first_steps sp ra key s0 s1
  chain_facts code with "Vsa.Sim.Code.caml_skiplist_insert_at_"
  all_goals try skip_first_steps sp ra key s0 s1
  all_goals try simp only [srcVal, lookupG, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals try decide
  all_goals try simp only [wlogM]
  have nilWrite (m : Std.ExtHashMap Nat (BitVec 8)) : writeLog m [] = m := rfl
  all_goals try simp only [nilWrite]
  · exact SkipFirstEval.i8002ab00_facts _ sp ra key s0 s1 (stack_word frame 184 18446744073709551608#64 (by decide) (by decide) (by decide))
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact SkipFirstEval.i8002ab04_facts _ sp ra key s0 s1 ⟨by decide, by decide, by decide⟩ empty.level
    all_goals skip_misses frame
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact SkipFirstEval.i8002ab40_facts _ sp ra key s0 s1 ⟨by decide, by decide, by decide⟩ empty.first
    all_goals skip_misses frame
  · exact SkipFirstEval.i8002ab4c_facts _ sp ra key s0 s1 (stack_word frame 24 18446744073709551448#64 (by decide) (by decide) (by decide))
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact SkipFirstEval.i8002ab58_facts _ sp ra key s0 s1 ⟨by decide, by decide, by decide⟩ empty.first
    all_goals skip_misses frame
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact SkipFirstEval.i8002ab6c_facts _ sp ra key s0 s1 ⟨by decide, by decide, by decide⟩ empty.random
    all_goals skip_misses frame
  · exact SkipFirstEval.i8002aba8_facts _ sp ra key s0 s1 ⟨by decide, by decide, by decide, by decide⟩
  · exact SkipFirstEval.i8002abb0_facts _ sp ra key s0 s1 (stack_word frame 176 18446744073709551600#64 (by decide) (by decide) (by decide))
  · exact SkipFirstEval.i8002abb4_facts _ sp ra key s0 s1 (stack_word frame 168 18446744073709551592#64 (by decide) (by decide) (by decide))

def prefixLog (sp ra s0 s1 : BitVec 64) : List WEntry :=
  [(nativeFrameBase sp 192 + 184,8,ra), (nativeFrameBase sp 192 + 24,8,sk),
   (Skiplist.randomSeed,4,25173), (nativeFrameBase sp 192 + 176,8,s0),
   (nativeFrameBase sp 192 + 168,8,s1)]

def prefixRegs (sp key : BitVec 64) : GRegs :=
  [(10,24),(16,sk),(8,key),(9,0),(13,0),(15,0xffffffffc0000000),(14,25173),
   (17,0xfffffffffffffff8),(29,nativeStack sp 192 + 24#64),(28,0xfffffffffffffff8),
   (6,0),(2,nativeStack sp 192),(11,key),(12,0)]

def prefixFullRegs (sp ra key : BitVec 64) : GRegs :=
  [(10,24),(16,sk),(8,key),(9,0),(13,0),(15,0xffffffffc0000000),(14,25173),
   (17,0xfffffffffffffff8),(29,nativeStack sp 192 + 24#64),(28,0xfffffffffffffff8),
   (6,0),(2,nativeStack sp 192),(1,ra),(11,key),(12,0)]

def prefixWrites : List Nat := [2,6,13,15,28,17,29,14,8,9,16,10]

theorem prefix_log {sp ra key s0 s1} (frame : NativeFrame sp 192) :
    (evalBlocks headBlocks (SegEvalState.init (input sp ra key s0 s1) loads)).log = prefixLog sp ra s0 s1 := by
  simp only [headBlocks, caml_skiplist_insertXaafcFSeg, caml_skiplist_insertXab10Seg, caml_skiplist_insertXab3cFSeg, caml_skiplist_insertXab48FSeg, caml_skiplist_insertXab58TSeg, caml_skiplist_insertXab68TSeg, caml_skiplist_insertXaca4TSeg, caml_skiplist_insertXacb8Seg, evalBlocks, evalBlock, SegEvalState.init]
  simp only [List.cons_append, List.nil_append, evalBlocks, evalBlock]
  prefix_stages sp ra key s0 s1
  simp only [prefixLog, sk, Skiplist.globalRoots, Skiplist.randomSeed,
    stack_nat frame 184 18446744073709551608#64 (by decide) (by decide),
    stack_nat frame 24 18446744073709551448#64 (by decide) (by decide),
    stack_nat frame 176 18446744073709551600#64 (by decide) (by decide),
    stack_nat frame 168 18446744073709551592#64 (by decide) (by decide)]
  rfl

theorem prefix_regs (sp ra key s0 s1 : BitVec 64) :
    (evalBlocks headBlocks (SegEvalState.init (input sp ra key s0 s1) loads)).regs = prefixFullRegs sp ra key := by
  simp only [headBlocks, caml_skiplist_insertXaafcFSeg, caml_skiplist_insertXab10Seg, caml_skiplist_insertXab3cFSeg, caml_skiplist_insertXab48FSeg, caml_skiplist_insertXab58TSeg, caml_skiplist_insertXab68TSeg, caml_skiplist_insertXaca4TSeg, caml_skiplist_insertXacb8Seg, evalBlocks, evalBlock, SegEvalState.init]
  simp only [List.cons_append, List.nil_append, evalBlocks, evalBlock]
  prefix_stages sp ra key s0 s1
  simp only [prefixFullRegs, nativeStack, sk, Skiplist.globalRoots, BitVec.add_assoc,
    show -192#64 + 24#64 = 18446744073709551448#64 by decide]
  try rfl

def prefixWindows (sp : BitVec 64) : List W :=
  [⟨nativeFrameBase sp 192, sp.toNat⟩, ⟨Skiplist.randomSeed, Skiplist.randomSeed + 4⟩]

theorem prefix_inside {sp ra s0 s1} (frame : NativeFrame sp 192) :
    LogInW (prefixWindows sp) (prefixLog sp ra s0 s1) := by
  apply OCaml.Vm.Sim.log_in_windows_of_mem
  intro e member
  simp only [prefixLog, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [prefixWindows, InsideW]
  all_goals have lower := frame.lower
  all_goals unfold nativeFrameBase
  all_goals omega

theorem prefix_out {sp ra s0 s1 a n} (frame : NativeFrame sp 192)
    (below : a + n ≤ heapEnd) (seed : a + n ≤ Skiplist.randomSeed ∨ Skiplist.randomSeed + 4 ≤ a) :
    OutLRange (prefixLog sp ra s0 s1) a n := by
  apply OCaml.Vm.Sim.outLRange_of_windows (prefix_inside frame)
  simp only [prefixWindows, OutWRange, and_true]
  refine ⟨Or.inl ?_, seed⟩
  have lower := frame.lower
  unfold nativeFrameBase
  omega

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
  [(2,sp),(10,0),(9,s1),(1,ra),(8,s0),(11,0),(13,p+24),(14,nativeStack sp 192+32),(12,sk),(15,nativeStack sp 192+32)]

/-- Data pins at the allocator return; these are derived from the setup and
allocator frame when the complete first-call summary is composed. -/
structure FinishMemory (m : Std.ExtHashMap Nat (BitVec 8)) (sp ra s0 s1 : BitVec 64) : Prop where
  update : bytesT m (nativeFrameBase sp 192 + 24) 8 = sk
  first : bytesT m Skiplist.globalRoots 8 = 0
  saved0 : bytesT m (nativeFrameBase sp 192 + 176) 8 = s0
  savedRa : bytesT m (nativeFrameBase sp 192 + 184) 8 = ra
  saved1 : bytesT m (nativeFrameBase sp 192 + 168) 8 = s1


end OCaml.Vm.Gc.SkiplistFirst

namespace OCaml.Vm.Gc.SkiplistFirst
set_option linter.unusedSimpArgs false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap
local macro "finish_eval_nf" h:ident : tactic => `(tactic|
  simp only [
    skipfirst_line_8002acc0,
    skipfirst_line_8002acc4,
    skipfirst_line_8002acc8,
    skipfirst_line_8002ac0c,
    skipfirst_line_8002ac10,
    skipfirst_line_8002ac14,
    skipfirst_line_8002ac18,
    skipfirst_line_8002ac1c,
    skipfirst_line_8002ac20,
    skipfirst_line_8002ac24,
    skipfirst_line_8002ac28,
    skipfirst_line_8002ac2c,
    skipfirst_line_8002ac30,
    skipfirst_line_8002ac34,
    skipfirst_line_8002ac38,
    skipfirst_line_8002ac40,
    skipfirst_line_8002ac44,
    skipfirst_line_8002ac48,
    skipfirst_line_8002ac4c,
    skipfirst_line_8002ac50,
    finishBlocks,
    finishInput,
    finishLoads,
    caml_skiplist_insertXacc0Seg,
    caml_skiplist_insertXac0cSeg,
    caml_skiplist_insertXac24FSeg,
    caml_skiplist_insertXac40Seg,
    List.cons_append,
    List.nil_append,
    evalBlocks,
    evalBlock,
    SegEvalState.init,
    runGM,
    ldsRunM,
    wlogM,
    stepGM,
    stepLdsM,
    srcVal,
    lookupG,
    eraseG,
    wvalM,
    wentryM,
    widthOfM,
    eaddrM,
    shamtOf,
    List.headD_cons,
    List.tail_cons,
    List.headD_nil,
    Option.getD_some,
    Nat.reduceEqDiff,
    ite_true,
    ite_false,
    read8_value,
    ($h).update,
    ($h).first,
    ($h).saved0,
    ($h).savedRa,
    ($h).saved1,
    BitVec.add_zero,
    BitVec.zero_add,
    BitVec.add_assoc,
    (show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide),
    (show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide),
    (show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide),
    (show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide),
    (show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide),
    (show Functions.sign_extend (m := 64) 168#12 = 168#64 by decide),
    (show Functions.sign_extend (m := 64) 176#12 = 176#64 by decide),
    (show Functions.sign_extend (m := 64) 184#12 = 184#64 by decide),
    (show Functions.sign_extend (m := 64) 192#12 = 192#64 by decide),
    (show Functions.sign_extend (m := 64) 4088#12 = -8#64 by decide),
    (show Sail.shift_bits_left 0#64 (Sail.BitVec.extractLsb ((32#12).extractLsb' 0 6) 5 0) = 0#64 by decide),
    (show Sail.shift_bits_right 0#64 (Sail.BitVec.extractLsb ((29#12).extractLsb' 0 6) 5 0) = 0#64 by decide),
    (show 24#64 + 8#64 = 32#64 by decide),
    (show 16#64 + 8#64 = 24#64 by decide),
    (show 24#64 + -8#64 = 16#64 by decide)])

theorem finish_regs (c : Config) (sp ra s0 s1 p key : BitVec 64)
    (h : FinishMemory c.σ.mem sp ra s0 s1) :
    (evalBlocks finishBlocks (SegEvalState.init (finishInput sp p key) (finishLoads c sp))).regs =
      finishRegs sp ra s0 s1 p := by
  finish_eval_nf h
  try finish_eval_nf h
  simp only [finishRegs, nativeStack_restore]
  try rfl

theorem finish_log (c : Config) (sp ra s0 s1 p key : BitVec 64)
    (C : Cell p) (h : FinishMemory c.σ.mem sp ra s0 s1) :
    (evalBlocks finishBlocks (SegEvalState.init (finishInput sp p key) (finishLoads c sp))).log =
      finishLog p key := by
  finish_eval_nf h
  try finish_eval_nf h
  simp only [finishLog, C.addr 8 (by decide), C.addr 16 (by decide), sk,
    Skiplist.globalRoots, BitVec.toNat_ofNat, Nat.reduceMod]
  try rfl

theorem finish_pc (c : Config) (sp ra s0 s1 p key : BitVec 64)
    (h : FinishMemory c.σ.mem sp ra s0 s1) (aligned : ra.toNat % 4 = 0) :
    evalBlocksPC jal_8002acbc_call.link (SegEvalState.init (finishInput sp p key) (finishLoads c sp))
      finishBlocks = ra := by
  simp only [evalBlocksPC, finishBlocks, caml_skiplist_insertXacc0Seg,
    caml_skiplist_insertXac0cSeg, caml_skiplist_insertXac24FSeg, caml_skiplist_insertXac40Seg,
    List.cons_append, List.nil_append, chainEndPC, endPCB, tgtPCT, SegEvalState.init]
  finish_eval_nf h
  simpa only [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
    BitVec.add_zero] using ret_tgt ra aligned

local macro "finish_misses" h:ident fr:ident cell:ident : tactic => `(tactic| (
  intro _
  try finish_eval_nf $h
  try simp only [($cell).addr 8 (by decide), ($cell).addr 16 (by decide), nativeStack,
    ($fr).address 24 (by decide), ($fr).address 168 (by decide),
    ($fr).address 176 (by decide), ($fr).address 184 (by decide),
    ($fr).slot_nat (off := 24) (by decide), ($fr).slot_nat (off := 168) (by decide),
    ($fr).slot_nat (off := 176) (by decide), ($fr).slot_nat (off := 184) (by decide)]
  simp only [OutLRange, and_true, sk, Skiplist.globalRoots,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;>
    (have lower := ($fr).lower
     have high := ($cell).high
     have low := ($cell).low
     simp only [heapStart, heapEnd] at lower high low
     try unfold nativeFrameBase
     omega)))

theorem finish_facts {c sp ra s0 s1 p key}
    (leaf : LeafInput jal_8002acbc_call.link c) (frame : NativeFrame sp 192)
    (C : Cell p) (h : FinishMemory c.σ.mem sp ra s0 s1) (aligned : ra.toNat % 4 = 0) :
    ChainFacts c.σ.mem c.σ.mem (finishInput sp p key) (finishLoads c sp) finishBlocks := by
  have code := skipFirst_code leaf.image
  simp only [finishBlocks, caml_skiplist_insertXacc0Seg, caml_skiplist_insertXac0cSeg,
    caml_skiplist_insertXac24FSeg, caml_skiplist_insertXac40Seg,
    List.cons_append, List.nil_append, ChainFacts, BBlockFacts, ProgFactsM]
  finish_eval_nf h
  chain_facts code with "Vsa.Sim.Code.caml_skiplist_insert_at_"
  all_goals try finish_eval_nf h
  all_goals try simp only [guardB, bne_self_eq_false]
  all_goals try (
    have ret : Sail.BitVec.update ra 0 0#1 = ra := by
      simpa only [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
        BitVec.add_zero] using ret_tgt ra aligned
    rw [ret]
    exact aligned)
  all_goals repeat (first | rw [stepMemM_store rfl] | rw [stepMemM_skip rfl])
  all_goals try finish_eval_nf h

  · exact (C.word 0 (by decide) (by decide)).sd rfl (by finish_eval_nf h)
  · exact (C.word 8 (by decide) (by decide)).sd rfl (by finish_eval_nf h)
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl
        (by finish_eval_nf h) (frame.pins_slot c (off := 24) (by decide))
    all_goals finish_misses h frame C
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact (show ReadWindow sk 8 from ⟨by decide, by decide, by decide⟩).ld rfl
        (by finish_eval_nf h) (read8_pins _ _)
    all_goals finish_misses h frame C
  · exact (C.word 16 (by decide) (by decide)).sd rfl (by finish_eval_nf h)
  · exact (show WriteWindow sk 8 from ⟨by decide, by decide, by decide, by decide⟩).sd rfl (by finish_eval_nf h)
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact (frame.read_slot (off := 176) (by decide) (by decide)).ld rfl
        (by finish_eval_nf h) (frame.pins_slot c (off := 176) (by decide))
    all_goals finish_misses h frame C
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact (frame.read_slot (off := 184) (by decide) (by decide)).ld rfl
        (by finish_eval_nf h) (frame.pins_slot c (off := 184) (by decide))
    all_goals finish_misses h frame C
  · repeat (refine memFacts_writeLog ?_ ?_)
    · exact (frame.read_slot (off := 168) (by decide) (by decide)).ld rfl
        (by finish_eval_nf h) (frame.pins_slot c (off := 168) (by decide))
    all_goals finish_misses h frame C

def finishWrites : List Nat := [15,14,13,12,11,8,1,9,10,2]
def finishWindows (p : BitVec 64) : List W :=
  [⟨p.toNat, p.toNat + 24⟩, ⟨Skiplist.globalRoots, Skiplist.globalRoots + 8⟩]

theorem finish_inside (p key : BitVec 64) : LogInW (finishWindows p) (finishLog p key) := by
  apply OCaml.Vm.Sim.log_in_windows_of_mem
  intro e member
  simp only [finishLog, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp only [finishWindows, InsideW]
  all_goals omega

theorem finish_outside {p key} (C : Cell p) : ImageOutside (finishLog p key) := by
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows (finish_inside p key)
  all_goals simp only [finishWindows, OutWRange, and_true]
  all_goals have low := C.low
  all_goals simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize,
    heapStart, Skiplist.globalRoots] at *
  all_goals constructor <;> left <;> omega

/-- The real level-0 cell/header stores and original caller return. -/
theorem finish (c : Config) (sp ra s0 s1 p key : BitVec 64)
    (leaf : LeafInput jal_8002acbc_call.link c) (frame : NativeFrame sp 192)
    (C : Cell p) (h : FinishMemory c.σ.mem sp ra s0 s1) (aligned : ra.toNat % 4 = 0)
    (regs : GHolds c.σ (finishInput sp p key)) :
    FnSummary jal_8002acbc_call.link (fun d => d = c)
      (WriteRegistersPost finishWrites (finishLog p key) c ra 0 (finishRegs sp ra s0 s1 p)) := by
  apply registers_of_blocks' leaf.image (finish_outside C)
    (block_summary finishBlocks jal_8002acbc_call.link (finishInput sp p key) (finishLoads c sp) c {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,10,8,9]; decide
      shape := by change ChainOK _ [2,10,8,9] finishBlocks; decide
      facts := finish_facts leaf frame C h aligned })
  · exact finish_log c sp ra s0 s1 p key C h
  · exact finish_pc c sp ra s0 s1 p key h aligned
  · intro σ pins
    rw [finish_regs c sp ra s0 s1 p key h] at pins
    exact pins
  · rfl
  · decide

end OCaml.Vm.Gc.SkiplistFirst

namespace OCaml.Vm.Gc.SkiplistFirst
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap

theorem prepare_call (c : Config) (sp ra key s0 s1 : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 192) (empty : Empty c.σ.mem)
    (regs : GHolds c.σ (input sp ra key s0 s1)) :
    FnSummary Skiplist.insertPc (fun d => d = c)
      (WriteRegistersPost (prefixWrites ++ [1]) (prefixLog sp ra s0 s1) c
        jal_8002acbc_call.target 24 ((1, jal_8002acbc_call.link) :: prefixRegs sp key)) := by
  exact block_then_call c jal_8002acbc_call_shape jal_8002acbc_call_decode
    (fun _ image => jal_8002acbc_call_pins image) (prepare c sp ra key s0 s1 leaf frame empty regs)
    (by simp only [prefixRegs, keysG]; decide)
    (by simp only [KeysAvoidRa, prefixRegs, keysG]; decide) rfl

theorem pins_before_seed (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) :
    pin.1 < Skiplist.randomSeed := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr,
    Skiplist.randomSeed] at * <;> omega

theorem seed_out {H a} (owned : vsaFoot H a) :
    a < Skiplist.randomSeed ∨ Skiplist.randomSeed + 4 ≤ a := by
  rcases owned with global | ⟨lo, _, _⟩
  · unfold allocGlobal InRange at global
    unfold Skiplist.randomSeed
    omega
  · have below : Skiplist.randomSeed + 4 ≤ heapStart := by decide
    omega

theorem header_not_foot {H a} (lo : Skiplist.globalRoots ≤ a)
    (hi : a < Skiplist.globalRoots + Skiplist.headerBytes) : ¬ vsaFoot H a := by
  rintro (global | ⟨low, _, _⟩)
  · unfold allocGlobal InRange at global
    simp only [Skiplist.globalRoots, Skiplist.headerBytes] at lo hi
    omega
  · simp only [Skiplist.globalRoots, Skiplist.headerBytes] at lo hi
    unfold heapStart at low
    omega

theorem prefix_ready {c after H capacity sp ra key s0 s1}
    (ready : RuntimeReady H capacity sp ra c) (frame : NativeFrame sp 192)
    (post : WriteRegistersPost (prefixWrites ++ [1]) (prefixLog sp ra s0 s1) c
      jal_8002acbc_call.target 24 ((1, jal_8002acbc_call.link) :: prefixRegs sp key) after) :
    RuntimeReady H capacity (nativeStack sp 192) jal_8002acbc_call.link after := by
  apply ready.window_log post (by decide)
    (by simp only [prefixWrites, prefixRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs rfl) (gholds_lookup (n := 1) _ post.regs rfl)
    (by decide) (prefix_inside frame)
  · intro pin member
    have low := pins_before_seed pin member
    have lower := frame.lower
    have bound : Skiplist.randomSeed ≤ heapEnd := by decide
    simp only [prefixWindows, OutW, and_true]
    exact ⟨Or.inl (by unfold nativeFrameBase; omega), Or.inl low⟩
  · simp only [prefixWindows, OutWRange, and_true]
    have lower := frame.lower
    simp only [Layout.sym_Caml_state, Skiplist.randomSeed, heapEnd] at lower ⊢
    unfold nativeFrameBase
    omega
  · simp only [prefixWindows, OutWRange, and_true]
    have lower := frame.lower
    simp only [Layout.sym_pool, Skiplist.randomSeed, heapEnd] at lower ⊢
    unfold nativeFrameBase
    omega
  · intro a owned
    have below := allocator_foot_below owned
    have lower := frame.lower
    simp only [prefixWindows, OutW, and_true]
    exact ⟨Or.inl (by unfold nativeFrameBase; omega), seed_out owned⟩

theorem prefix_word (m : Std.ExtHashMap Nat (BitVec 8)) (sp ra s0 s1 : BitVec 64)
    (frame : NativeFrame sp 192) (i off : Nat) (value : BitVec 64)
    (slot : (i, off, value) ∈ [(0,184,ra),(1,24,sk),(3,176,s0),(4,168,s1)]) :
    bytesT (writeLog m (prefixLog sp ra s0 s1)) (nativeFrameBase sp 192 + off) 8 = value := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at slot
  apply word_writeLog_at m (prefixLog sp ra s0 s1) i _ value
  · rcases slot with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals rfl
  · rcases slot with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals simp only [prefixLog, Nat.reduceAdd, List.drop, OutLRange, and_true]
    all_goals have lower := frame.lower
    all_goals simp only [Skiplist.randomSeed, heapEnd] at lower ⊢
    all_goals unfold nativeFrameBase
    all_goals omega

theorem empty_word {m} (e : Empty m) : bytesT m Skiplist.globalRoots 8 = 0#64 := by
  rw [bytesT_eight_eq, bytesT8_of_lpins8 e.first]
  rfl
theorem finish_memory {before atCall after H capacity sp ra key s0 s1}
    (frame : NativeFrame sp 192) (nested : NativeFrame (nativeStack sp 192) 544)
    (empty : Empty before.σ.mem)
    (post : WriteRegistersPost (prefixWrites ++ [1]) (prefixLog sp ra s0 s1) before
      jal_8002acbc_call.target 24 ((1, jal_8002acbc_call.link) :: prefixRegs sp key) atCall)
    (B : StatCheckedReturned H capacity (nativeStack sp 192) jal_8002acbc_call.link key 24 atCall after) :
    FinishMemory after.σ.mem sp ra s0 s1 := by
  have word (i off : Nat) (value : BitVec 64)
      (slot : (i, off, value) ∈ [(0,184,ra),(1,24,sk),(3,176,s0),(4,168,s1)]) :
      bytesT after.σ.mem (nativeFrameBase sp 192 + off) 8 = value := by
    rw [word_observed (m := atCall.σ.mem) _ (fun k hk =>
      (B.caller_frame nested).byte _ (by rw [frame.stack_nat]; omega)), post.memory]
    exact prefix_word before.σ.mem sp ra s0 s1 frame i off value slot
  refine {
    update := word 1 24 sk (by simp)
    saved0 := word 3 176 s0 (by simp)
    savedRa := word 0 184 ra (by simp)
    saved1 := word 4 168 s1 (by simp)
    first := ?_ }
  have headerBelow : Skiplist.globalRoots + 8 ≤ heapEnd := by decide
  have headerSize : 8 ≤ Skiplist.headerBytes := by decide
  rw [word_observed (m := atCall.σ.mem) _ (fun i hi =>
    B.framed_byte nested (by omega) (header_not_foot (by omega) (by omega))),
    post.memory, bytesT_writeLog_out _ (prefix_out frame (by decide) (Or.inr (by decide)))]
  exact empty_word empty

theorem allocated_cell {H capacity sp ra key before after}
    (B : StatCheckedReturned H capacity sp ra key 24 before after) : Cell (vsaReg B.allocated 10) := by
  obtain ⟨_, low, high, _⟩ := B.allocation.allocation.result.fresh.destruct
  change heapStart ≤ (vsaReg B.allocated 10).toNat at low
  change (vsaReg B.allocated 10).toNat + 24 ≤ heapEnd at high
  exact ⟨low, high, B.allocation.allocation.result.align⟩

def checkedWrites : List Nat := 8 :: abiClobbered

theorem checked_frame {H capacity sp ra key n before after}
    (platform : VsaOk startupLive before)
    (B : StatCheckedReturned H capacity sp ra key n before after) : GprsSame before after checkedWrites := by
  have savedPlatform : VsaOk startupLive B.allocation.saved :=
    B.allocation.setup.vsaOk_of_written platform (by decide)
      (B.allocation.setup.writtenPresent (by simp only [statCheckedRegs, keysG]; decide))
      (by intro a ha; rw [B.allocation.setup.memory]; exact writeLog_present _ _ _ (platform.live a ha))
  have mallocPlatform : VsaOk startupLive B.allocation.atMalloc :=
    B.allocation.call.vsaOk_of_written savedPlatform (by decide)
      (B.allocation.call.writtenPresent (by simp only [statCheckedCallRegs, keysG]; decide))
      (by intro a ha; rw [B.allocation.call.memory]; exact savedPlatform.live a ha)
  have mallocFrame := GprsSame.of_saved (fun k member =>
    allocator_abi_register mallocPlatform B.allocation.allocation.good B.allocation.allocation.result.frame
      B.allocation.allocation.registers k member)
  exact (((GprsSame.of_post B.allocation.setup (by decide)).trans
    (GprsSame.of_post B.allocation.call (by decide))).trans mallocFrame |>.trans
      (GprsSame.of_post B.returned (by decide))).mono (by decide)

structure NativeFirst (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 s1 key : BitVec 64) (before after : Config) where
  atCall : Config
  afterAlloc : Config
  prepared : WriteRegistersPost (prefixWrites ++ [1]) (prefixLog sp ra s0 s1) before
    jal_8002acbc_call.target 24 ((1, jal_8002acbc_call.link) :: prefixRegs sp key) atCall
  allocation : StatCheckedReturned H capacity (nativeStack sp 192) jal_8002acbc_call.link key 24 atCall afterAlloc
  p : BitVec 64
  pointer : p = vsaReg allocation.allocated 10
  terminal : WriteRegistersPost finishWrites (finishLog p key) afterAlloc ra 0 (finishRegs sp ra s0 s1 p) after

theorem call_frame {sp} (frame : NativeFrame sp Skiplist.opStack) :
    NativeFrame (nativeStack sp 192) 544 :=
  (frame.resize (small := 736) (by decide) (by decide)).nested (front := 192) (by decide)

theorem native_first (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 key : BitVec 64) (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp Skiplist.opStack) (empty : Empty c.σ.mem)
    (regs : GHolds c.σ (input sp ra key s0 s1)) (charged : vsaChg 24 charge) :
    FnSummary Skiplist.insertPc (fun d => d = c)
      (fun after => Nonempty (NativeFirst H capacity sp ra s0 s1 key c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := frame.resize (small := 192) (by decide) (by decide)
  have nested := call_frame frame
  obtain ⟨atCall, run1, A⟩ := (prepare_call c sp ra key s0 s1 ready.toLeafInput short empty regs).run c ⟨pc, rfl⟩
  have callReady := prefix_ready ready short A
  obtain ⟨allocated, run2, ⟨B⟩⟩ := (stat_checked atCall H capacity charge (nativeStack sp 192)
    jal_8002acbc_call.link key 24 callReady nested
    (gholds_lookup (n := 8) _ A.regs rfl) (gholds_lookup (n := 10) _ A.regs rfl) charged).run atCall
      ⟨by rw [← jal_8002acbc_call_target]; exact A.pc, rfl⟩
  let p := vsaReg B.allocated 10
  have C : Cell p := allocated_cell B
  have memory := finish_memory short nested empty A B
  have bank := checked_frame callReady.platform B
  have saved1 : gprGet allocated.σ 9 = some 0#64 :=
    bank.get (n := 9) (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ A.regs rfl)
  have finishRegs : GHolds allocated.σ (finishInput sp p key) :=
    ⟨B.ready.stack, B.returned.result, gholds_lookup (n := 8) _ B.returned.regs rfl, saved1, trivial⟩
  obtain ⟨after, run3, terminal⟩ := (finish allocated sp ra s0 s1 p key B.ready.toLeafInput short C memory
    ready.aligned finishRegs).run allocated ⟨B.returned.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans run3), ⟨atCall, allocated, A, B, p, rfl, terminal⟩⟩

theorem finish_ready {before after H capacity sp ra s0 s1 key p}
    (ready : RuntimeReady ((p.toNat, 24) :: H) capacity (nativeStack sp 192) jal_8002acbc_call.link before)
    (C : Cell p)
    (post : WriteRegistersPost finishWrites (finishLog p key) before ra 0 (finishRegs sp ra s0 s1 p) after)
    (aligned : ra.toNat % 4 = 0) : RuntimeReady ((p.toNat, 24) :: H) capacity sp ra after := by
  apply ready.window_log post (by decide)
    (by simp only [finishRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs rfl) (gholds_lookup (n := 1) _ post.regs rfl)
    aligned (finish_inside p key)
  · intro pin member
    have low := pins_before_seed pin member
    have cellLow := C.low
    have arena : Skiplist.randomSeed ≤ heapStart := by decide
    have header : Skiplist.randomSeed ≤ Skiplist.globalRoots := by decide
    simp only [finishWindows, OutW, and_true]
    exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
  · have low := C.low
    have bound : Layout.sym_Caml_state + 8 ≤ heapStart := by decide
    simp only [finishWindows, OutWRange, and_true]
    exact ⟨Or.inl (by omega), by decide⟩
  · have low := C.low
    have bound : Layout.sym_pool + 8 ≤ heapStart := by decide
    simp only [finishWindows, OutWRange, and_true]
    exact ⟨Or.inl (by omega), by decide⟩
  · intro a owned
    have low := C.low
    simp only [finishWindows, OutW, and_true]
    constructor
    · by_cases left : a < p.toNat
      · exact Or.inl left
      by_cases right : p.toNat + 24 ≤ a
      · exact Or.inr right
      exfalso
      exact (owned_not_foot (by omega) ⟨(p.toNat, 24), by simp,
        by change p.toNat ≤ a ∧ a < p.toNat + 24; constructor <;> omega⟩) owned
    · by_cases left : a < Skiplist.globalRoots
      · exact Or.inl left
      by_cases right : Skiplist.globalRoots + 8 ≤ a
      · exact Or.inr right
      exfalso
      exact (header_not_foot (by omega) (by unfold Skiplist.headerBytes; omega)) owned

theorem NativeFirst.cell {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) : Cell F.p := by
  rw [F.pointer]
  exact allocated_cell F.allocation

theorem NativeFirst.ready {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) (aligned : ra.toNat % 4 = 0) :
    RuntimeReady ((F.p.toNat, 24) :: H) capacity sp ra after := by
  apply finish_ready (C := F.cell) (post := F.terminal) (aligned := aligned)
  rw [F.pointer]
  exact F.allocation.ready

theorem NativeFirst.saved {H capacity budget sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after)
    (ready : RuntimeReady H budget sp ra before) (frame : NativeFrame sp 192)
    (regs : GHolds before.σ (input sp ra key s0 s1)) :
    ∀ n ∈ abiSaved, gprGet after.σ n = gprGet before.σ n := by
  have called := prefix_ready ready frame F.prepared
  have bank := ((GprsSame.of_post F.prepared (by decide)).trans
    (checked_frame called.platform F.allocation)).trans (GprsSame.of_post F.terminal (by decide))
  intro n member
  by_cases eq8 : n = 8
  · subst n
    exact (gholds_lookup (n := 8) _ F.terminal.regs rfl).trans (gholds_lookup (n := 8) _ regs rfl).symm
  by_cases eq9 : n = 9
  · subst n
    exact (gholds_lookup (n := 9) _ F.terminal.regs rfl).trans (gholds_lookup (n := 9) _ regs rfl).symm
  have bounds : 1 ≤ n ∧ n ≤ 31 := by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at member; omega
  apply bank.same n bounds.1 bounds.2
  simp only [finishWrites, checkedWrites, abiClobbered, prefixWrites, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at member
  omega

theorem NativeFirst.output {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) :
    Vsa.Machine.output after.σ = Vsa.Machine.output before.σ := by
  have out := F.allocation.allocation.allocation.output
  change Vsa.Machine.output F.allocation.allocated.σ =
    Vsa.Machine.output F.allocation.allocation.atMalloc.σ at out
  simpa only [Vsa.Machine.output, F.terminal.output, F.allocation.returned.output,
    F.allocation.allocation.call.output, F.allocation.allocation.setup.output, F.prepared.output] using out

structure Selected (H kept : List (Nat × Nat)) : Prop where
  member : ∀ e ∈ kept, e ∈ H
  lower : ∀ e ∈ kept, heapStart ≤ e.1
  upper : ∀ e ∈ kept, e.1 + e.2 ≤ heapEnd
  positive : ∀ e ∈ kept, 0 < e.2

structure KeySlot (kept : List (Nat × Nat)) (key : BitVec 64) (block : Nat × Nat) : Prop where
  member : block ∈ kept
  lower : heapStart ≤ key.toNat
  upper : key.toNat + 8 ≤ heapEnd
  aligned : key.toNat % 8 = 0
  start : block.1 ≤ key.toNat
  stop : key.toNat + 8 ≤ block.1 + block.2

theorem live_windows {kept before after log windows}
    (memory : after.σ.mem = writeLog before.σ.mem log) (inside : LogInW windows log)
    (outside : ∀ e ∈ kept, OutWRange windows e.1 e.2) : LiveFrame kept before after := by
  constructor
  intro e member x owned
  have range := OCaml.Vm.Sim.outLRange_of_windows inside (outside e member)
  rw [memory, writeLog_out _ _ _ (outL_of_range range (by unfold InExt at owned; omega)
    (by unfold InExt at owned; omega))]

theorem Selected.foot {H kept a} (S : Selected H kept) (owned : vsaFoot H a) : vsaFoot kept a := by
  rcases owned with global | ⟨lo, hi, outside⟩
  · exact Or.inl global
  · exact Or.inr ⟨lo, hi, fun e member => outside e (S.member e member)⟩

theorem NativeFirst.live {H kept capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) (S : Selected H kept)
    (frame : NativeFrame sp Skiplist.opStack) : LiveFrame kept before after := by
  have short := frame.resize (small := 192) (by decide) (by decide)
  have nested := call_frame frame
  have front : LiveFrame kept before F.atCall := live_windows F.prepared.memory (prefix_inside short) (by
    intro e member
    have low := S.lower e member
    have high := S.upper e member
    have lower := short.lower
    have seed : Skiplist.randomSeed + 4 ≤ heapStart := by decide
    simp only [prefixWindows, OutWRange, and_true]
    exact ⟨Or.inl (by unfold nativeFrameBase; omega), Or.inr (by omega)⟩)
  have middle : LiveFrame kept F.atCall F.afterAlloc := LiveFrame.of_foot
    (fun e member => ⟨S.lower e member, S.upper e member⟩)
    (fun a below outside => F.allocation.framed_byte nested below (fun owned => outside (S.foot owned)))
  have back : LiveFrame kept F.afterAlloc after := live_windows F.terminal.memory (finish_inside F.p key) (by
    intro e member
    have apart : F.p.toNat + 24 ≤ e.1 ∨ e.1 + e.2 ≤ F.p.toNat := by
      rw [F.pointer]
      exact OCaml.Vm.Boot.Startup.FreshBlock.apart F.allocation.allocation.allocation.result.fresh
        (S.member e member) (by decide) (S.positive e member)
    have low := S.lower e member
    have header : Skiplist.globalRoots + 8 ≤ heapStart := by decide
    simp only [finishWindows, OutWRange, and_true]
    exact ⟨apart.elim Or.inr Or.inl, Or.inr (by omega)⟩)
  exact (front.trans middle).trans back

theorem KeySlot.value {kept key block before after} (slot : KeySlot kept key block)
    (live : LiveFrame kept before after) : bytesT after.σ.mem key.toNat 8 = bytesT before.σ.mem key.toNat 8 := by
  apply word_observed
  intro i hi
  apply live.byte block slot.member
  have lo := slot.start
  have high := slot.stop
  change block.1 ≤ key.toNat + i ∧ key.toNat + i < block.1 + block.2
  constructor <;> omega

structure CellWords (m : Std.ExtHashMap Nat (BitVec 8)) (p key : BitVec 64) : Prop where
  keyWord : bytesT m p.toNat 8 = key
  dataWord : bytesT m (p.toNat + 8) 8 = 0
  nextWord : bytesT m (p.toNat + 16) 8 = 0
  headerWord : bytesT m Skiplist.globalRoots 8 = p

theorem finish_words (m : Std.ExtHashMap Nat (BitVec 8)) (p key : BitVec 64) (C : Cell p) :
    CellWords (writeLog m (finishLog p key)) p key := by
  let cells : List (Nat × BitVec 64) :=
    [(p.toNat,key),(p.toNat+8,0),(p.toNat+16,0),(Skiplist.globalRoots,p)]
  have separated : cells.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by
    have low := C.low
    have header : Skiplist.globalRoots + 8 ≤ heapStart := by decide
    simp [cells, List.pairwise_cons] <;> omega
  have word (a : Nat) (value : BitVec 64) (member : (a,value) ∈ cells) :
      bytesT (writeLog m (finishLog p key)) a 8 = value := by
    change bytesT (writeLog m (cells.map (fun (a,v) => (a,8,v)))) a 8 = value
    exact word_writeLog_cells m cells separated member
  exact ⟨word _ _ (by simp [cells]), word _ _ (by simp [cells]),
    word _ _ (by simp [cells]), word _ _ (by simp [cells])⟩

theorem NativeFirst.words {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) : CellWords after.σ.mem F.p key := by
  rw [F.terminal.memory]
  exact finish_words _ _ _ F.cell

theorem NativeFirst.header_tail {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after)
    (frame : NativeFrame sp Skiplist.opStack) (empty : Empty before.σ.mem) :
    ∀ k, 8 ≤ k → k < Skiplist.headerBytes → (after.σ.mem[Skiplist.globalRoots + k]?).getD 0 = 0 := by
  intro k klo khi
  have short := frame.resize (small := 192) (by decide) (by decide)
  have nested := call_frame frame
  have endHeader : Skiplist.globalRoots + Skiplist.headerBytes ≤ heapStart := by decide
  have arena : heapStart ≤ heapEnd := by decide
  have low := F.cell.low
  have outside : OutLRange (finishLog F.p key) (Skiplist.globalRoots + k) 1 := by
    apply OCaml.Vm.Sim.outLRange_of_windows (finish_inside F.p key)
    simp only [finishWindows, OutWRange, and_true]
    exact ⟨Or.inl (by omega), Or.inr (by omega)⟩
  have firstOutside : OutLRange (prefixLog sp ra s0 s1) (Skiplist.globalRoots + k) 1 :=
    prefix_out short (by omega) (Or.inr (by unfold Skiplist.randomSeed Skiplist.globalRoots; omega))
  rw [F.terminal.memory, writeLog_out _ _ _ (outL_of_range outside (by omega) (by omega)),
    F.allocation.framed_byte nested (by omega) (header_not_foot (by omega) (by omega)),
    F.prepared.memory, writeLog_out _ _ _ (outL_of_range firstOutside (by omega) (by omega))]
  exact empty.header k khi

theorem KeySlot.window {kept key block} (slot : KeySlot kept key block) : ReadWindow key 8 := by
  have lo := slot.lower
  have hi := slot.upper
  have ramLo : 0x80000000 ≤ heapStart := by decide
  have ramHi : heapEnd ≤ 0x100000000 := by decide
  have htif : Layout.sym_tohost + 8 ≤ heapStart := by decide
  exact ⟨by omega, by omega, Or.inr (by omega)⟩

def startupKey : BitVec 64 := firstDomainPtr + BitVec.ofNat 64 SkipFirstEval.startupKeyOffset
def startupBlock : Nat × Nat := (firstDomainPtr.toNat, Layout.domainStateBytes)
def startupBlocks : List (Nat × Nat) := [startupBlock]

theorem startup_selected {H} (owned : startupBlock ∈ H) : Selected H startupBlocks := by
  constructor
  · intro e member
    have eq : e = startupBlock := List.mem_singleton.mp member
    subst e
    exact owned
  all_goals intro e member
  all_goals have eq : e = startupBlock := List.mem_singleton.mp member
  all_goals subst e
  all_goals decide

theorem startup_key_slot : KeySlot startupBlocks startupKey startupBlock := by
  constructor
  · exact List.mem_singleton_self _
  all_goals decide

theorem NativeFirst.chain {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) :
    Skiplist.Chain after.σ.mem (bytesT after.σ.mem Skiplist.globalRoots 8) [F.p] := by
  rw [F.words.headerWord]
  change F.p = F.p ∧ F.p ≠ 0#64 ∧ ChainScan.next after.σ.mem F.p = 0#64
  refine ⟨rfl, ?_, ?_⟩
  · intro eq
    have low := F.cell.low
    rw [eq] at low
    change heapStart ≤ 0 at low
    have positive : 0 < heapStart := by decide
    omega
  · unfold ChainScan.next
    rw [F.cell.addr 16 (by decide)]
    exact F.words.nextWord

theorem prefix_seed_word (m : Std.ExtHashMap Nat (BitVec 8)) (sp ra s0 s1 : BitVec 64)
    (frame : NativeFrame sp 192) : bytesT (writeLog m (prefixLog sp ra s0 s1)) Skiplist.randomSeed 4 = 25173#32 := by
  let front : List WEntry := [(nativeFrameBase sp 192 + 184,8,ra), (nativeFrameBase sp 192 + 24,8,sk)]
  let back := nativeWordLog sp 192 [(176,s0),(168,s1)]
  have bounds : ∀ off value, (off,value) ∈ [(176,s0),(168,s1)] → off + 8 ≤ 192 := by
    intro off value member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    omega
  have backEq : back = [(nativeFrameBase sp 192 + 176,8,s0),(nativeFrameBase sp 192 + 168,8,s1)] :=
    frame.word_log_slots bounds
  have inside : LogInW [⟨nativeFrameBase sp 192,sp.toNat⟩] back := frame.word_log_inside bounds
  have outside : OutLRange back Skiplist.randomSeed 4 := by
    apply OCaml.Vm.Sim.outLRange_of_windows inside
    change (Skiplist.randomSeed + 4 ≤ nativeFrameBase sp 192 ∨ sp.toNat ≤ Skiplist.randomSeed) ∧ True
    have lower := frame.lower
    have bound : Skiplist.randomSeed + 4 ≤ heapEnd := by decide
    exact ⟨Or.inl (by unfold nativeFrameBase; omega), trivial⟩
  have logEq : prefixLog sp ra s0 s1 = (front ++ [(Skiplist.randomSeed,4,25173)]) ++ back := by
    rw [backEq]
    rfl
  rw [logEq, writeLog_append, bytesT_writeLog_out _ outside, writeLog_append]
  have word := word32_writeLog (writeLog m front) Skiplist.randomSeed 25173#64
  rw [show (25173#64).setWidth 32 = 25173#32 by decide] at word
  exact word

theorem NativeFirst.seed {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after) (frame : NativeFrame sp Skiplist.opStack) :
    bytesT after.σ.mem Skiplist.randomSeed 4 = 25173#32 := by
  have short := frame.resize (small := 192) (by decide) (by decide)
  have nested := call_frame frame
  have below : Skiplist.randomSeed + 4 ≤ heapEnd := by decide
  have arena : Skiplist.randomSeed + 4 ≤ heapStart := by decide
  have header : Skiplist.randomSeed + 4 ≤ Skiplist.globalRoots := by decide
  have low := F.cell.low
  have outside : OutLRange (finishLog F.p key) Skiplist.randomSeed 4 := by
    apply OCaml.Vm.Sim.outLRange_of_windows (finish_inside F.p key)
    simp only [finishWindows, OutWRange, and_true]
    exact ⟨Or.inl (by omega), Or.inl header⟩
  have copied : Reloc.Copied F.atCall F.afterAlloc Skiplist.randomSeed Skiplist.randomSeed 4 := by
    intro i hi
    rw [byte_total, byte_total]
    exact F.allocation.framed_byte nested (by omega) (by
      intro owned
      have out := seed_out owned
      omega)
  rw [F.terminal.memory, bytesT_writeLog_out _ outside, Reloc.bytesT_congr copied, F.prepared.memory]
  exact prefix_seed_word _ sp ra s0 s1 short

/-- The real insertion keeps the caller's bytes above its entry stack. -/
theorem NativeFirst.caller_frame {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after)
    (frame : NativeFrame sp Skiplist.opStack) : CallerFrame sp before after := by
  have short := frame.resize (small := 192) (by decide) (by decide)
  have nested := call_frame frame
  have cell := F.cell
  have lower := short.lower
  have upper := cell.high
  have roots : Skiplist.globalRoots + 8 ≤ heapEnd := by decide
  have seed : Skiplist.randomSeed + 4 ≤ heapEnd := by decide
  constructor
  intro x hx
  have front : OutW (prefixWindows sp) x := by
    simp only [prefixWindows, OutW, and_true]
    exact ⟨Or.inr hx, Or.inr (by omega)⟩
  have back : OutW (finishWindows F.p) x := by
    simp only [finishWindows, OutW, and_true]
    exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
  rw [F.terminal.memory, frameOn_writeLog _ _ _ (finish_inside F.p key) x back,
    (F.allocation.caller_frame nested).byte x (by rw [short.stack_nat]; unfold nativeFrameBase; omega),
    F.prepared.memory, frameOn_writeLog _ _ _ (prefix_inside short) x front]

/-- Low runtime globals outside the seed, published root pointer and allocator
metadata retain their entry values through the complete first insertion. -/
theorem NativeFirst.low_kept {H capacity sp ra s0 s1 key before after}
    (F : NativeFirst H capacity sp ra s0 s1 key before after)
    (frame : NativeFrame sp Skiplist.opStack) (x : Nat) (low : x < heapStart)
    (alloc : ¬ allocGlobal x) (seed : x < Skiplist.randomSeed ∨ Skiplist.randomSeed + 4 ≤ x)
    (header : x < Skiplist.globalRoots ∨ Skiplist.globalRoots + 8 ≤ x) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have short := frame.resize (small := 192) (by decide) (by decide)
  have nested := call_frame frame
  have cell := F.cell
  have bound : heapStart ≤ heapEnd := by decide
  have front : OutW (prefixWindows sp) x := by
    simp only [prefixWindows, OutW, and_true]
    have lower := short.lower
    exact ⟨Or.inl (by unfold nativeFrameBase; omega), seed⟩
  have back : OutW (finishWindows F.p) x := by
    simp only [finishWindows, OutW, and_true]
    exact ⟨Or.inl (by have := cell.low; omega), header⟩
  rw [F.terminal.memory, frameOn_writeLog _ _ _ (finish_inside F.p key) x back,
    F.allocation.framed_byte nested (by omega) (fun h => h.elim alloc (fun h => by omega)),
    F.prepared.memory, frameOn_writeLog _ _ _ (prefix_inside short) x front]

structure FirstInserted (H kept : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 s1 key : BitVec 64) (before after : Config) where
  native : NativeFirst H capacity sp ra s0 s1 key before after
  cell : Cell native.p
  words : CellWords after.σ.mem native.p key
  level0 : Skiplist.Chain after.σ.mem (bytesT after.σ.mem Skiplist.globalRoots 8) [native.p]
  seed : bytesT after.σ.mem Skiplist.randomSeed 4 = 25173#32
  headerTail : ∀ k, 8 ≤ k → k < Skiplist.headerBytes → (after.σ.mem[Skiplist.globalRoots + k]?).getD 0 = 0
  ready : RuntimeReady ((native.p.toNat,24) :: H) capacity sp ra after
  saved : ∀ n ∈ abiSaved, gprGet after.σ n = gprGet before.σ n
  live : LiveFrame kept before after
  keyKept : bytesT after.σ.mem key.toNat 8 = bytesT before.σ.mem key.toNat 8
  keyWindow : ReadWindow key 8
  keyAligned : key.toNat % 8 = 0
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

theorem first_insert (c : Config) (H kept : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 key : BitVec 64) (block : Nat × Nat)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp Skiplist.opStack)
    (empty : Empty c.σ.mem) (regs : GHolds c.σ (input sp ra key s0 s1)) (charged : vsaChg 24 charge)
    (selection : Selected H kept) (slot : KeySlot kept key block) :
    FnSummary Skiplist.insertPc (fun d => d = c)
      (fun after => Nonempty (FirstInserted H kept capacity sp ra s0 s1 key c after)) := by
  apply (native_first c H capacity charge sp ra s0 s1 key ready frame empty regs charged).weaken (fun _ h => h)
  intro after ⟨F⟩
  have short := frame.resize (small := 192) (by decide) (by decide)
  have live := F.live selection frame
  have returned := F.ready ready.aligned
  exact ⟨{
    native := F
    cell := F.cell
    words := F.words
    level0 := F.chain
    seed := F.seed frame
    headerTail := F.header_tail frame empty
    ready := returned
    saved := F.saved ready short regs
    live := live
    keyKept := slot.value live
    keyWindow := slot.window
    keyAligned := slot.aligned
    output := F.output
    htif := returned.platform.htifIdle.trans ready.platform.htifIdle.symm }⟩

theorem first_insert_startup (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 : BitVec 64) (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp Skiplist.opStack) (empty : Empty c.σ.mem)
    (regs : GHolds c.σ (input sp ra startupKey s0 s1))
    (owned : startupBlock ∈ H) (charged : vsaChg 24 charge) :
    FnSummary Skiplist.insertPc (fun d => d = c)
      (fun after => Nonempty (FirstInserted H startupBlocks capacity sp ra s0 s1 startupKey c after)) :=
  first_insert c H startupBlocks capacity charge sp ra s0 s1 startupKey startupBlock
    ready frame empty regs charged (startup_selected owned) startup_key_slot

end OCaml.Vm.Gc.SkiplistFirst
