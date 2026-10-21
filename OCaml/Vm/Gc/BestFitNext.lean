import OCaml.Vm.Gc.BestFitFallback
import OCaml.Vm.Gc.FfsLowest
import OCaml.Vm.Gc.BestFitRemnant
import Vsa.Sim.GRegsLookup

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

def pickRepair : List BBlock := [blk bf_allocateX73f8TSeg, blk bf_allocateX74a8TSeg, blk bf_allocateX7594Seg]
def pickPc : BitVec 64 := 0x800073f8#64
def popPc : BitVec 64 := 0x800074bc#64

theorem pick_repair_regs (sp s : BitVec 64) (b0 b8 bh bm : List (BitVec 8)) :
    Picked sp s b0 b8 bh bm (evalBlocks pickRepair (SegEvalState.init (pickRegs sp s) [b0, b8, bh, bm])).regs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [pickRepair, evalBlocks, evalBlock, SegEvalState.init] <;>
    simp only [pickRegs] <;> bf_simp <;> rfl

theorem slot_of {s : BitVec 64} (small : s.toNat ≤ 16) : flBase + sx s <<< 4 = BestFitRemnant.slot s := by
  have hs : s = BitVec.ofNat 64 s.toNat := by simp
  rw [hs, sx_small (by omega)]
  simp only [BestFitRemnant.slot, BestFitSmall.slot, flBase, Layout.bf_small_size, BestFitRemnant.log16,
    Layout.sym_bf_small_fl]

/-- The first two blocks' register list. -/
def r73 (sp s : BitVec 64) (b0 b8 : List (BitVec 8)) (lds : List (List (BitVec 8))) : GRegs :=
  runGM (blk bf_allocateX73f8TSeg).body (pickRegs sp s) (b0 :: b8 :: lds)

theorem acc73 (m : Std.ExtHashMap Nat (BitVec 8)) (sp s : BitVec 64) (b0 b8 : List (BitVec 8))
    (lds : List (List (BitVec 8))) (low : ReadWindow sp 8) (high : ReadWindow (sp + 8#64) 8)
    (p0 : LPins8 m sp.toNat b0) (p8 : LPins8 m (sp + 8#64).toNat b8) :
    AccessPlan m (pickRegs sp s) (b0 :: b8 :: lds) (blk bf_allocateX73f8TSeg).body := by
  simp only [blk, bf_allocateX73f8TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply low.ld rfl (by simp only [pickRegs]; bf_simp)
    simpa [stepMemM, mkLine, decodeM, stepLdsM] using p0
  · apply high.ld rfl (by simp only [pickRegs]; bf_simp)
    simpa [stepMemM, mkLine, decodeM, stepLdsM] using p8

theorem guard73 (sp s : BitVec 64) (b0 b8 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (positive : 1 ≤ s.toNat) (small : s.toNat ≤ 16) :
    TermFactsO (r73 sp s b0 b8 lds) (blk bf_allocateX73f8TSeg).term := by
  have hs : s = BitVec.ofNat 64 s.toNat := by simp
  have v15 : srcVal 15 (r73 sp s b0 b8 lds) = sx s := by simp only [r73, pickRegs]; bf_simp; rfl
  change guardB bop.BNE (srcVal 15 (r73 sp s b0 b8 lds)) (srcVal 0 (r73 sp s b0 b8 lds)) = true
  have z : srcVal 0 (r73 sp s b0 b8 lds) = 0#64 := rfl
  rw [v15, z, hs, sx_small (by omega)]
  simp only [guardB, bne_iff_ne, ne_eq]
  intro h
  have := congrArg BitVec.toNat h
  simp at this; omega

theorem r73_regs (sp s : BitVec 64) (b0 b8 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    srcVal 13 (r73 sp s b0 b8 lds) = flBase ∧ srcVal 15 (r73 sp s b0 b8 lds) = sx s := by
  refine ⟨?_, ?_⟩ <;> simp only [r73, pickRegs] <;> bf_simp <;> rfl

/-- The list slot read by `0x800074a8` from any register list with `a3`, `a5`. -/
theorem acc74a8 (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (x : BitVec 64) (bh bm : List (BitVec 8))
    (lds : List (List (BitVec 8))) (addr : srcVal 13 L + srcVal 15 L <<< 4 = x)
    (head : ReadWindow x 8) (merge : ReadWindow (x + 8#64) 8)
    (ph : LPins8 m x.toNat bh) (pm : LPins8 m (x + 8#64).toNat bm) :
    AccessPlan m L (bh :: bm :: lds) (blk bf_allocateX74a8FSeg).body := by
  simp only [blk, bf_allocateX74a8FSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply head.ld rfl
    · simp [eaddrM, mkLine, decodeM, stepGM, srcVal, lookupG, eraseG, wvalM, shamtOf,
        Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
        BestFitRemnant.shift4] at addr ⊢
      rw [lookupG_eraseG_ne (by decide)]; exact addr
    · simpa [stepMemM, mkLine, decodeM, stepLdsM] using ph
  · apply merge.ld rfl
    · simp [eaddrM, mkLine, decodeM, stepGM, srcVal, lookupG, eraseG, wvalM, shamtOf,
        Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
        BestFitRemnant.shift4] at addr ⊢
      rw [← addr, lookupG_eraseG_ne (by decide)]
    · simpa [stepMemM, mkLine, decodeM, stepLdsM] using pm

macro "gen_simp" : tactic => `(tactic|
  simp [blk, bf_allocateX74a8FSeg, bf_allocateX74a8TSeg, bf_allocateX7594Seg, runGM, wlogM, wentryM, eaddrM, stepGM,
    stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, widthOfM, shamtOf, Sail.BitVec.extractLsb,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BestFitRemnant.shift4, ldsRunM])

structure After74 (L : GRegs) (bh bm : List (BitVec 8)) (L' : GRegs) : Prop where
  block : srcVal 11 L' = bytesVal .ld bh
  merge : srcVal 17 L' = bytesVal .ld bm
  slot : srcVal 16 L' = srcVal 13 L + srcVal 15 L <<< 4

theorem after74 (L : GRegs) (bh bm : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    After74 L bh bm (runGM (blk bf_allocateX74a8FSeg).body L (bh :: bm :: lds)) := by
  refine ⟨?_, ?_, ?_⟩ <;> gen_simp <;> simp [lookupG_eraseG_ne]

theorem body74 : (blk bf_allocateX74a8TSeg).body = (blk bf_allocateX74a8FSeg).body := rfl

theorem fix_log (L : GRegs) (lds : List (List (BitVec 8))) :
    wlogM (blk bf_allocateX7594Seg).body L lds = [((srcVal 16 L + 8#64).toNat, 8, srcVal 16 L)] := by
  gen_simp

theorem fix_regs (L : GRegs) (lds : List (List (BitVec 8))) : runGM (blk bf_allocateX7594Seg).body L lds = L := rfl

theorem fix_access (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (lds : List (List (BitVec 8))) (x : BitVec 64)
    (slot : srcVal 16 L = x) (window : WriteWindow (x + 8#64) 8) :
    AccessPlan m L lds (blk bf_allocateX7594Seg).body := by
  simp only [blk, bf_allocateX7594Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  apply window.sd rfl
  simp [eaddrM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  simpa [srcVal] using congrArg (· + 8#64) slot

def allBlocks : List BBlock :=
  [blk bf_allocateX73f8TSeg, blk bf_allocateX74a8FSeg, blk bf_allocateX74a8TSeg, blk bf_allocateX7594Seg,
    blk bf_allocateX74bcTSeg, blk bf_allocateX74bcFSeg, blk bf_allocateX74ccSeg, blk bf_allocateX74e8Seg,
    blk bf_allocateX7534Seg]

theorem all_code {mem : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Bf_allocateLoaded mem) :
    ChainCode mem allBlocks := by
  intro b member
  simp only [allBlocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [blk, bf_allocateX73f8TSeg, bf_allocateX74a8FSeg, bf_allocateX74a8TSeg, bf_allocateX7594Seg,
    bf_allocateX74bcTSeg, bf_allocateX74bcFSeg, bf_allocateX74ccSeg, bf_allocateX74e8Seg, bf_allocateX7534Seg,
    List.getD_cons_zero, CodeFacts]
  all_goals chain_facts code with "Vsa.Sim.Code.bf_allocate_at_"

theorem code_of {mem : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Bf_allocateLoaded mem) {bs : List BBlock}
    (sub : ∀ b ∈ bs, b ∈ allBlocks) : ChainCode mem bs :=
  fun b h => all_code code b (sub b h)

def slotS (s : BitVec 64) : BitVec 64 := BestFitRemnant.slot s
def headOf (s : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (slotS s).toNat 8
def cursorOf (s : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (slotS s + 8#64).toNat 8

def pickLoads (sp s : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [Primitives.read8 m sp.toNat, Primitives.read8 m (sp + 8#64).toNat, Primitives.read8 m (slotS s).toNat,
    Primitives.read8 m (slotS s + 8#64).toNat]

/-- The cursor repair when the cursor pointed at the popped head. -/
def pickLog (s : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List WEntry :=
  if cursorOf s m = headOf s m then [((slotS s + 8#64).toNat, 8, slotS s)] else []

structure PickInput (sp s : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (pickRegs sp s)
  positive : 1 ≤ s.toNat
  small : s.toNat ≤ 16
  low : ReadWindow sp 8
  high : ReadWindow (sp + 8#64) 8

structure PickPost (sp s : BitVec 64) (before after : Config) : Prop where
  pc : PCAt popPc after
  registers : GHolds after.σ (popRegs sp s (headOf s before.σ.mem) (bytesT before.σ.mem sp.toNat 8)
    (bytesT before.σ.mem (sp + 8#64).toNat 8))
  memory : after.σ.mem = writeLog before.σ.mem (pickLog s before.σ.mem)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10, 11, 12, 13, 14, 15, 16, 17], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem lds73 (b0 b8 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM (blk bf_allocateX73f8TSeg).body (b0 :: b8 :: lds) = lds := rfl

theorem addr73 {sp s : BitVec 64} (small : s.toNat ≤ 16) (b0 b8 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    srcVal 13 (r73 sp s b0 b8 lds) + srcVal 15 (r73 sp s b0 b8 lds) <<< 4 = slotS s := by
  rw [(r73_regs sp s b0 b8 lds).1, (r73_regs sp s b0 b8 lds).2]; exact slot_of small

theorem picked_holds {c : Config} {sp s : BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    (picked : Picked sp s (Primitives.read8 m sp.toNat) (Primitives.read8 m (sp + 8#64).toNat)
      (Primitives.read8 m (slotS s).toNat) (Primitives.read8 m (slotS s + 8#64).toNat) L) (held : GHolds c.σ L) :
    GHolds c.σ (popRegs sp s (headOf s m) (bytesT m sp.toNat 8) (bytesT m (sp + 8#64).toNat 8)) := by
  have b := picked.b; have bits := picked.bits; have wosz := picked.wosz
  rw [read8_value] at b bits wosz
  exact ⟨gholds_lookup _ held picked.sp, gholds_lookup _ held picked.size, gholds_lookup _ held b,
    gholds_lookup _ held bits, gholds_lookup _ held picked.fl, gholds_lookup _ held wosz,
    gholds_lookup _ held picked.shifted, True.intro⟩

theorem plain_pc (sp s : BitVec 64) (b0 b8 bh bm : List (BitVec 8)) :
    evalBlocksPC pickPc (SegEvalState.init (pickRegs sp s) [b0, b8, bh, bm]) pickPlain = popPc := by
  simp only [evalBlocksPC, pickPlain, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0, pickRegs]
  bf_simp; rfl

theorem repair_pc (sp s : BitVec 64) (b0 b8 bh bm : List (BitVec 8)) :
    evalBlocksPC pickPc (SegEvalState.init (pickRegs sp s) [b0, b8, bh, bm]) pickRepair = popPc := by
  simp only [evalBlocksPC, pickRepair, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0, pickRegs]
  bf_simp; rfl

theorem plain_log (sp s : BitVec 64) (b0 b8 bh bm : List (BitVec 8)) :
    (evalBlocks pickPlain (SegEvalState.init (pickRegs sp s) [b0, b8, bh, bm])).log = [] := by
  simp only [pickPlain, evalBlocks, evalBlock, SegEvalState.init, pickRegs]; bf_simp

theorem repair_log {sp s : BitVec 64} (small : s.toNat ≤ 16) (b0 b8 bh bm : List (BitVec 8)) :
    (evalBlocks pickRepair (SegEvalState.init (pickRegs sp s) [b0, b8, bh, bm])).log =
      [((slotS s + 8#64).toNat, 8, slotS s)] := by
  rw [slotS, ← slot_of small]
  simp only [pickRepair, evalBlocks, evalBlock, SegEvalState.init, pickRegs]; bf_simp; exact ⟨rfl, rfl⟩

theorem pick {sp s c} (input : PickInput sp s c) : FnSummary pickPc (fun d => d = c) (PickPost sp s c) := by
  let m := c.σ.mem
  have small := input.small
  have slotW := BestFitRemnant.slot_window small
  have mergeW := BestFitRemnant.merge_window small
  have after := after74 (r73 sp s (Primitives.read8 m sp.toNat) (Primitives.read8 m (sp + 8#64).toNat)
    [Primitives.read8 m (slotS s).toNat, Primitives.read8 m (slotS s + 8#64).toNat])
    (Primitives.read8 m (slotS s).toNat) (Primitives.read8 m (slotS s + 8#64).toNat) []
  have addr := addr73 small (sp := sp) (Primitives.read8 m sp.toNat) (Primitives.read8 m (sp + 8#64).toNat)
    [Primitives.read8 m (slotS s).toNat, Primitives.read8 m (slotS s + 8#64).toNat]
  have access74 := acc74a8 m _ (slotS s) _ _ [] addr slotW.read mergeW.read (read8_pins _ _) (read8_pins _ _)
  have first : BlockAccess m (pickRegs sp s) (pickLoads sp s m) (blk bf_allocateX73f8TSeg) :=
    ⟨acc73 _ _ _ _ _ _ input.low input.high (read8_pins _ _) (read8_pins _ _),
      guard73 _ _ _ _ _ input.positive small⟩
  have keys : KeysOK (keysG (pickRegs sp s)) := by change KeysOK [2, 10]; decide
  by_cases repair : cursorOf s m = headOf s m
  · have chainA : ChainAccess m (pickRegs sp s) (pickLoads sp s m) pickRepair := by
      apply ChainAccess.cons first
      rw [show wlogM (blk bf_allocateX73f8TSeg).body (pickRegs sp s) (pickLoads sp s m) = [] from rfl]
      change ChainAccess (writeLog m []) (r73 sp s _ _ _) (ldsRunM _ (_ :: _ :: _)) _
      rw [lds73]
      apply ChainAccess.cons ⟨by rw [body74]; exact access74, ?_⟩
      · rw [body74]
        apply ChainAccess.cons ⟨fix_access _ _ _ (slotS s) (by rw [after.slot, addr]) mergeW, trivial⟩
          ChainAccess.nil
      · rw [body74]
        change guardB bop.BEQ (srcVal 17 _) (srcVal 11 _) = true
        rw [after.merge, after.block, read8_value, read8_value]
        simp only [guardB]
        exact beq_iff_eq.mpr repair
    have summary := block_summary pickRepair pickPc (pickRegs sp s) (pickLoads sp s m) c
      ⟨input.good, input.minstret, input.registers, keys,
        chainPlan_facts (code_of input.code (by
          intro x h; simp only [pickRepair, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> simp [allBlocks])) chainA,
        by change ChainOK pickPc [2, 10] pickRepair; decide, input.tick⟩
    apply summary.weaken (fun _ h => h)
    intro d post
    refine ⟨?_, picked_holds ?_ post.regs, ?_, post.good, post.tick, post.minstret, post.output,
      fun r noise outside => post.frame r noise (fun n hn => outside n (by
        have h : ∀ n ∈ wrChain pickRepair, n ∈ [10, 11, 12, 13, 14, 15, 16, 17] := by decide
        exact h n hn))⟩
    · rw [PCAt, post.pc, pickLoads, repair_pc]
    · exact pick_repair_regs _ _ _ _ _ _
    · rw [post.memory, pickLoads, repair_log small, pickLog, if_pos repair]
  · have chainA : ChainAccess m (pickRegs sp s) (pickLoads sp s m) pickPlain := by
      apply ChainAccess.cons first
      rw [show wlogM (blk bf_allocateX73f8TSeg).body (pickRegs sp s) (pickLoads sp s m) = [] from rfl]
      change ChainAccess (writeLog m []) (r73 sp s _ _ _) (ldsRunM _ (_ :: _ :: _)) _
      rw [lds73]
      apply ChainAccess.cons ⟨access74, ?_⟩ ChainAccess.nil
      change guardB bop.BEQ (srcVal 17 _) (srcVal 11 _) = false
      rw [after.merge, after.block, read8_value, read8_value]
      simp only [guardB]
      exact beq_eq_false_iff_ne.mpr repair
    have summary := block_summary pickPlain pickPc (pickRegs sp s) (pickLoads sp s m) c
      ⟨input.good, input.minstret, input.registers, keys,
        chainPlan_facts (code_of input.code (by
          intro x h; simp only [pickPlain, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp [allBlocks])) chainA,
        by change ChainOK pickPc [2, 10] pickPlain; decide, input.tick⟩
    apply summary.weaken (fun _ h => h)
    intro d post
    refine ⟨?_, picked_holds ?_ post.regs, ?_, post.good, post.tick, post.minstret, post.output,
      fun r noise outside => post.frame r noise (fun n hn => outside n (by
        have h : ∀ n ∈ wrChain pickPlain, n ∈ [10, 11, 12, 13, 14, 15, 16, 17] := by decide
        exact h n hn))⟩
    · rw [PCAt, post.pc, pickLoads, plain_pc]
    · exact pick_regs _ _ _ _ _ _
    · rw [post.memory, pickLoads, plain_log, pickLog, if_neg repair]

/-! ## Stage 2: pop the head (`0x800074bc`) -/

def splitPc : BitVec 64 := 0x800074e8#64
def popKeep : List BBlock := [blk bf_allocateX74bcTSeg]
def popEmpty : List BBlock := [blk bf_allocateX74bcFSeg, blk bf_allocateX74ccSeg]

macro "pop_simp" : tactic => `(tactic|
  simp [blk, bf_allocateX74bcTSeg, bf_allocateX74bcFSeg, bf_allocateX74ccSeg, popRegs, runGM, wlogM, wentryM,
    eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of, widthOfM, shamtOf,
    Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, ldsRunM,
    BitVec.sub_eq_add_neg, BestFitRemnant.shift4])

/-- Stage 3's registers. -/
def splitRegs (sp b wosz : BitVec 64) : GRegs := [(2, sp), (11, b), (14, wosz)]

theorem keep_log (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) :
    (evalBlocks popKeep (SegEvalState.init (popRegs sp s b bits wosz) [bn])).log =
      [((flBase + sx s <<< 4).toNat, 8, bytesVal .ld bn)] := by
  simp only [popKeep, evalBlocks, evalBlock, SegEvalState.init]; pop_simp

theorem empty_log (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) :
    (evalBlocks popEmpty (SegEvalState.init (popRegs sp s b bits wosz) [bn])).log =
      [((flBase + sx s <<< 4).toNat, 8, bytesVal .ld bn), (Layout.sym_bf_small_map, 4, bits &&& (BestFitRemnant.bit s ^^^ 18446744073709551615#64))] := by
  simp only [popEmpty, evalBlocks, evalBlock, SegEvalState.init]; pop_simp
  exact ⟨rfl, rfl⟩

def nextOf (b : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m b.toNat 8

/-- The pop's stores: the slot takes the successor; an emptied list clears its bit. -/
def popLog (s b bits : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List WEntry :=
  [((slotS s).toNat, 8, nextOf b m)] ++
    (if nextOf b m = 0#64 then
      [(Layout.sym_bf_small_map, 4, bits &&& (BestFitRemnant.bit s ^^^ 18446744073709551615#64))] else [])

structure PopInput (sp s b bits wosz : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (popRegs sp s b bits wosz)
  small : s.toNat ≤ 16
  block : ReadWindow b 8

structure PopPost (sp s b bits wosz : BitVec 64) (before after : Config) : Prop where
  pc : PCAt splitPc after
  registers : GHolds after.σ (splitRegs sp b wosz)
  memory : after.σ.mem = writeLog before.σ.mem (popLog s b bits before.σ.mem)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10, 11, 12, 13, 14, 15, 16, 17], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem body74bc : (blk bf_allocateX74bcFSeg).body = (blk bf_allocateX74bcTSeg).body := rfl

theorem acc74bc (m : Std.ExtHashMap Nat (BitVec 8)) (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8))
    (lds : List (List (BitVec 8))) (small : s.toNat ≤ 16) (block : ReadWindow b 8) (pins : LPins8 m b.toNat bn) :
    AccessPlan m (popRegs sp s b bits wosz) (bn :: lds) (blk bf_allocateX74bcTSeg).body := by
  simp only [blk, bf_allocateX74bcTSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply block.ld rfl (by pop_simp)
    simpa [stepMemM, mkLine, decodeM, stepLdsM] using pins
  · apply (BestFitRemnant.slot_window small).sd rfl
    show _ = BestFitRemnant.slot s
    rw [← slot_of small]; pop_simp

theorem pop_src (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    srcVal 16 (runGM (blk bf_allocateX74bcTSeg).body (popRegs sp s b bits wosz) (bn :: lds)) = bytesVal .ld bn := by
  pop_simp

structure Split (sp b wosz : BitVec 64) (L : GRegs) : Prop where
  sp : lookupG 2 L = some sp
  b : lookupG 11 L = some b
  wosz : lookupG 14 L = some wosz

theorem keep_regs (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) :
    Split sp b wosz (evalBlocks popKeep (SegEvalState.init (popRegs sp s b bits wosz) [bn])).regs := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [popKeep, evalBlocks, evalBlock, SegEvalState.init] <;> pop_simp

theorem empty_regs (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) :
    Split sp b wosz (evalBlocks popEmpty (SegEvalState.init (popRegs sp s b bits wosz) [bn])).regs := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [popEmpty, evalBlocks, evalBlock, SegEvalState.init] <;> pop_simp

theorem keep_pc (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) :
    evalBlocksPC popPc (SegEvalState.init (popRegs sp s b bits wosz) [bn]) popKeep = splitPc := by
  simp only [evalBlocksPC, popKeep, chainEndPC, SegEvalState.init, endPCB, tgtPCT]; pop_simp; rfl

theorem empty_pc (sp s b bits wosz : BitVec 64) (bn : List (BitVec 8)) :
    evalBlocksPC popPc (SegEvalState.init (popRegs sp s b bits wosz) [bn]) popEmpty = splitPc := by
  simp only [evalBlocksPC, popEmpty, chainEndPC, SegEvalState.init, endPCB, tgtPCT]; pop_simp; rfl

theorem split_holds {c : Config} {sp b wosz : BitVec 64} {L : GRegs} (split : Split sp b wosz L)
    (held : GHolds c.σ L) : GHolds c.σ (splitRegs sp b wosz) :=
  ⟨gholds_lookup _ held split.sp, gholds_lookup _ held split.b, gholds_lookup _ held split.wosz, True.intro⟩

theorem pop {sp s b bits wosz c} (input : PopInput sp s b bits wosz c) :
    FnSummary popPc (fun d => d = c) (PopPost sp s b bits wosz c) := by
  let m := c.σ.mem
  let bn := Primitives.read8 m b.toNat
  have small := input.small
  have keys : KeysOK (keysG (popRegs sp s b bits wosz)) := by change KeysOK [2, 10, 11, 12, 13, 14, 15]; decide
  have access := acc74bc m sp s b bits wosz bn [] small input.block (read8_pins _ _)
  have src := pop_src sp s b bits wosz bn []
  have nextEq : bytesVal .ld bn = nextOf b m := read8_value _ _
  by_cases emptied : nextOf b m = 0#64
  · have chainA : ChainAccess m (popRegs sp s b bits wosz) [bn] popEmpty := by
      apply ChainAccess.cons ⟨by rw [body74bc]; exact access, ?_⟩
      · rw [body74bc]
        apply ChainAccess.cons (b := blk bf_allocateX74ccSeg) ⟨?_, by simp [blk, bf_allocateX74ccSeg, TermFactsO]⟩
          ChainAccess.nil
        simp only [blk, bf_allocateX74ccSeg, List.getD_cons_zero, AccessPlan]
        chain_facts True.intro
        apply BestFitRemnant.map_write.sw rfl
        pop_simp
      · rw [body74bc]
        change guardB bop.BNE (srcVal 16 _) (srcVal 0 _) = false
        rw [src, nextEq, emptied]; rfl
    have summary := block_summary popEmpty popPc (popRegs sp s b bits wosz) [bn] c
      ⟨input.good, input.minstret, input.registers, keys,
        chainPlan_facts (code_of input.code (by
          intro x h; simp only [popEmpty, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp [allBlocks])) chainA,
        by change ChainOK popPc [2, 10, 11, 12, 13, 14, 15] popEmpty; decide, input.tick⟩
    apply summary.weaken (fun _ h => h)
    intro d post
    refine ⟨?_, split_holds (empty_regs _ _ _ _ _ _) post.regs, ?_, post.good, post.tick, post.minstret,
      post.output, fun r noise outside => post.frame r noise (fun n hn => outside n (by
        have h : ∀ n ∈ wrChain popEmpty, n ∈ [10, 11, 12, 13, 14, 15, 16, 17] := by decide
        exact h n hn))⟩
    · rw [PCAt, post.pc, empty_pc]
    · rw [post.memory, empty_log, popLog, if_pos emptied, nextEq, slotS, ← slot_of small]
      rfl
  · have chainA : ChainAccess m (popRegs sp s b bits wosz) [bn] popKeep := by
      apply ChainAccess.cons ⟨access, ?_⟩ ChainAccess.nil
      change guardB bop.BNE (srcVal 16 _) (srcVal 0 _) = true
      rw [src, nextEq]
      simp only [guardB, bne_iff_ne, ne_eq]
      exact emptied
    have summary := block_summary popKeep popPc (popRegs sp s b bits wosz) [bn] c
      ⟨input.good, input.minstret, input.registers, keys,
        chainPlan_facts (code_of input.code (by
          intro x h; simp only [popKeep, List.mem_cons, List.not_mem_nil, or_false] at h
          subst h; simp [allBlocks])) chainA,
        by change ChainOK popPc [2, 10, 11, 12, 13, 14, 15] popKeep; decide, input.tick⟩
    apply summary.weaken (fun _ h => h)
    intro d post
    refine ⟨?_, split_holds (keep_regs _ _ _ _ _ _) post.regs, ?_, post.good, post.tick, post.minstret,
      post.output, fun r noise outside => post.frame r noise (fun n hn => outside n (by
        have h : ∀ n ∈ wrChain popKeep, n ∈ [10, 11, 12, 13, 14, 15, 16, 17] := by decide
        exact h n hn))⟩
    · rw [PCAt, post.pc, keep_pc]
    · rw [post.memory, keep_log, popLog, if_neg emptied, nextEq, slotS, ← slot_of small]
      rfl

end OCaml.Vm.Gc.BestFitNext
