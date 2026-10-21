import OCaml.Vm.Gc.BestFitFallback
import OCaml.Vm.Gc.FfsLowest
import OCaml.Vm.Gc.BestFitRemnant

/-! # Best-fit: the next nonempty small list

`bf_allocate(wosz)` with `bf_small_fl[wosz]` empty filters the small-list
bitmap to sizes above `wosz` and calls `ffs`. A nonzero result `s` names the
smallest nonempty larger list: its head is popped (cursor repair and bitmap
clearing as on the exact path), split (`bf_split_small`, inlined: the head
keeps `s - wosz - 1` words and the allocation is carved from its end), and
the remnant goes back through `bf_insert_remnant_small`. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- `ffs` returned `k + 1` to the fallback continuation. -/
structure Found (R : Nat → BitVec 64) (k : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt call.link after
  result : gprGet after.σ 10 = some (BitVec.ofNat 64 (k + 1))
  stack : gprGet after.σ 2 = some (frameSp R)
  memory : after.σ.mem = writeLog before.σ.mem (effect R (bitmap before))
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,10,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- The fallback prologue and `ffs` on a filtered bitmap with lowest set bit `k`. -/
theorem search_nonzero {R c k} (input : Input R c) (ffsCode : Code.FfsLoaded c.σ.mem)
    (lowest : FfsLowest.Lowest (filtered (R 10) (bitmap c)) k) :
    FnSummary pc (fun d => d = c) (Found R k c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare input).run
  intro middle prepared
  have ffsCode' : Code.FfsLoaded middle.σ.mem :=
    image_after Code.ffs_transport (by decide) ffsCode
      (chainPlan_facts (code_facts input.code) (access input)) prepared.machine
  let pins : GRegs := [(2,frameSp R),(10,filtered (R 10) (bitmap c))]
  have holds : GHolds middle.σ pins :=
    ⟨gholds_lookup _ prepared.registers rfl,gholds_lookup _ prepared.registers rfl,True.intro⟩
  have callSummary := call_summary call_shape call_decode middle (call_pins prepared.code)
    prepared.machine.good prepared.machine.tick prepared.machine.minstret pins holds
    (by change KeysOK [2,10]; decide)
    (by change ∀ n ∈ [2,10], n ≠ 1; decide)
  obtain ⟨callee,callRun,called⟩ := callSummary.run middle ⟨prepared.pc,rfl⟩
  have ffsInput : FfsLowest.Input call.link (filtered (R 10) (bitmap c)) k callee :=
    ⟨called.good,called.tick,called.minstret,called.mem ▸ ffsCode',
      ⟨called.ra,gholds_lookup _ called.registers rfl,True.intro⟩,by decide,by decide,lowest⟩
  have calleePc : PCAt FfsLowest.pc callee := by
    have h : FfsLowest.pc = FfsZero.pc := rfl
    rw [h]; simpa only [PCAt,call_target] using called.pc
  obtain ⟨after,run,returned⟩ := (FfsLowest.nonzero ffsInput).run callee ⟨calleePc,rfl⟩
  have memory : after.σ.mem = middle.σ.mem := returned.memory.trans called.mem
  refine ⟨after,callRun.trans run,⟨returned.good,returned.tick,returned.minstret,
    returned.pc,returned.result,?_,memory.trans prepared.memory,memory ▸ prepared.code,
    returned.output.trans (called.output.trans prepared.machine.output),?_⟩⟩
  · have same := returned.frame Register.x2 (by decide) (by decide)
    have stack : gprGet callee.σ 2 = some (frameSp R) := gholds_lookup _ called.registers rfl
    exact same.trans stack
  · intro r noise outside
    apply (returned.frame r noise (fun n hn => outside n (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
      rcases hn with rfl | rfl | rfl <;> simp))).trans
    apply (called.frame r noise (by simp [wrChain]) (outside 1 (by simp))).trans
    apply prepared.machine.frame r noise
    intro n hn
    apply outside n
    have h := written n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with rfl | rfl | rfl | rfl <;> simp

end OCaml.Vm.Gc.BestFitFallback

namespace OCaml.Vm.Gc.BestFitNext
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def blk (s : List BBlock) : BBlock := s.getD 0 {body := [], term := none}

macro "bf_simp" : tactic => `(tactic|
  simp [blk, bf_allocateX73f8TSeg, bf_allocateX74a8FSeg, bf_allocateX74a8TSeg, bf_allocateX7594Seg,
    bf_allocateX74bcTSeg, bf_allocateX74bcFSeg, bf_allocateX74ccSeg, bf_allocateX74e8Seg, bf_allocateX7534Seg,
    runGM, wlogM, wentryM, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    widthOfM, shamtOf, Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    BitVec.sub_eq_add_neg, ldsRunM, BestFitRemnant.shift4, BestFitRemnant.log16])

/-! ## Stage 1: the list `s` (`0x800073f8`) -/

def pickRegs (sp s : BitVec 64) : GRegs := [(2, sp), (10, s)]
def pickPlain : List BBlock := [blk bf_allocateX73f8TSeg, blk bf_allocateX74a8FSeg]

def sx (s : BitVec 64) : BitVec 64 := BitVec.signExtend 64 (BitVec.extractLsb 31 0 s)
def flBase : BitVec 64 := 2147902168#64

theorem sx_small {n : Nat} (h : n < 33) : sx (BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  have all : ∀ k < 33, sx (BitVec.ofNat 64 k) = BitVec.ofNat 64 k := by decide
  exact all n h

/-- Stage 2's registers. -/
def popRegs (sp s b bits wosz : BitVec 64) : GRegs :=
  [(2, sp), (10, s), (11, b), (12, bits), (13, flBase), (14, wosz), (15, sx s <<< 4)]

structure Picked (sp s : BitVec 64) (b0 b8 bh bm : List (BitVec 8)) (L : GRegs) : Prop where
  sp : lookupG 2 L = some sp
  size : lookupG 10 L = some s
  b : lookupG 11 L = some (bytesVal .ld bh)
  bits : lookupG 12 L = some (bytesVal .ld b0)
  fl : lookupG 13 L = some flBase
  wosz : lookupG 14 L = some (bytesVal .ld b8)
  shifted : lookupG 15 L = some (sx s <<< 4)

theorem pick_regs (sp s : BitVec 64) (b0 b8 bh bm : List (BitVec 8)) :
    Picked sp s b0 b8 bh bm (evalBlocks pickPlain (SegEvalState.init (pickRegs sp s) [b0, b8, bh, bm])).regs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [pickPlain, evalBlocks, evalBlock, SegEvalState.init] <;>
    simp only [pickRegs] <;> bf_simp <;> rfl

end OCaml.Vm.Gc.BestFitNext
