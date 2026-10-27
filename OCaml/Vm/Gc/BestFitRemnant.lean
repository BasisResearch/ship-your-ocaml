import OCaml.Vm.Gc.Generated.BestFitRemnant
import OCaml.Vm.Gc.BestFitSmall
import OCaml.Vm.Gc.BfShape
import OCaml.Vm.Gc.FfsLowest
import OCaml.Vm.Sim.LogWindow

/-! # `bf_insert_remnant_small`

The split's remnant `v` (a free block of `w = Wosize_val v` words, `w ≤ 16`)
goes back on small list `w` (`0x8000603c`): nothing when `w = 0`, nothing in
the sweep phase when `v` lies at or above `caml_gc_sweep_hp` (the sweeper
will find it); otherwise `caml_fl_cur_wsz += 1 + w`, `v` is pushed at the
list's head (its first word links the old head), the merge cursor moves to
`v` when it was the list's own slot, and bit `w - 1` of `bf_small_map` is
set. -/
namespace OCaml.Vm.Gc.BestFitRemnant
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def blk (s : List BBlock) : BBlock := s.getD 0 {body := [], term := none}

/-! ## The insertion tail (`0x8000605c`) -/

def insertPc : BitVec 64 := 0x8000605c#64
def insertRegs (ra v w : BitVec 64) : GRegs := [(1, ra), (10, v), (15, w)]
def plain : List BBlock :=
  [blk bf_insert_remnant_smallX605cFSeg, blk bf_insert_remnant_smallX6098Seg, blk bf_insert_remnant_smallX60b8Seg]
def repaired : List BBlock :=
  [blk bf_insert_remnant_smallX605cTSeg, blk bf_insert_remnant_smallX60ccSeg, blk bf_insert_remnant_smallX6098Seg,
    blk bf_insert_remnant_smallX60b8Seg]

def slot (w : BitVec 64) : BitVec 64 := BestFitSmall.slot w

/-- `1 << (w - 1)` as `sllw` computes it. -/
def bit (w : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (Sail.shift_bits_left (1#32)
    (BitVec.extractLsb 4 0 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (w + 18446744073709551615#64))))))

theorem shift4 (w : BitVec 64) : Sail.shift_bits_left w 4#6 = w <<< 4 := rfl
theorem log16 : Nat.log2 16 = 4 := by decide

macro "rem_simp" : tactic => `(tactic|
  simp [blk, bf_insert_remnant_smallX605cFSeg, bf_insert_remnant_smallX605cTSeg, bf_insert_remnant_smallX6098Seg,
    bf_insert_remnant_smallX60ccSeg, bf_insert_remnant_smallX60b8Seg, insertRegs, slot, BestFitSmall.slot,
    runGM, wlogM, wentryM, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    widthOfM, shamtOf, Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    Layout.sym_caml_fl_cur_wsz, Layout.sym_bf_small_fl, Layout.sym_bf_small_map, Layout.bf_small_size,
    BitVec.sub_eq_add_neg, shift4, log16, ldsRunM])

theorem insert_log (ra v w : BitVec 64) (bc bh bm : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    wlogM (blk bf_insert_remnant_smallX605cFSeg).body (insertRegs ra v w) (bc :: bh :: bm :: lds) =
      [(Layout.sym_caml_fl_cur_wsz, 8, bytesVal .ld bc + 1#64 + w), (v.toNat, 8, bytesVal .ld bh),
       ((slot w).toNat, 8, v)] := by
  rem_simp

theorem plain_log (ra v w : BitVec 64) (bc bh bm bp : List (BitVec 8)) :
    (evalBlocks plain (SegEvalState.init (insertRegs ra v w) [bc, bh, bm, bp])).log =
      [(Layout.sym_caml_fl_cur_wsz, 8, bytesVal .ld bc + 1#64 + w), (v.toNat, 8, bytesVal .ld bh),
       ((slot w).toNat, 8, v), (Layout.sym_bf_small_map, 4, bit w ||| bytesVal .lw bp)] := by
  simp only [plain, evalBlocks, evalBlock, SegEvalState.init]
  rem_simp
  rfl

theorem lpins8_applyW {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {b : List (BitVec 8)} {e : WEntry}
    (pins : LPins8 m a b) (width : e.2.1 = 8) (apart : e.1 + 8 ≤ a ∨ a + 8 ≤ e.1) : LPins8 (applyW m e) a b := by
  have same : ∀ i < 8, (applyW m e)[a + i]? = m[a + i]? := fun i hi =>
    applyW_getElem_disjoint m e (a + i) (by omega) (by omega)
  have s0 : (applyW m e)[a]? = m[a]? := applyW_getElem_disjoint m e a (by omega) (by omega)
  simp only [LPins8] at pins ⊢
  rw [s0, same 1 (by omega), same 2 (by omega), same 3 (by omega), same 4 (by omega),
    same 5 (by omega), same 6 (by omega), same 7 (by omega)]
  simpa using pins

macro "addr_simp" : tactic => `(tactic|
  simp [eaddrM, mkLine, decodeM, insertRegs, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, imm20Of, shamtOf,
    Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, slot,
    BestFitSmall.slot, shift4, log16, Layout.sym_caml_fl_cur_wsz, Layout.sym_bf_small_fl, Layout.sym_bf_small_map,
    Layout.off_bf_small_merge, Layout.bf_small_size, BitVec.sub_eq_add_neg])

theorem insert_access (m : Std.ExtHashMap Nat (BitVec 8)) (ra v w : BitVec 64) (bc bh bm : List (BitVec 8))
    (lds : List (List (BitVec 8)))
    (curWrite : WriteWindow (BitVec.ofNat 64 Layout.sym_caml_fl_cur_wsz) 8)
    (slotWrite : WriteWindow (slot w) 8) (mergeRead : ReadWindow (slot w + 8#64) 8) (vWrite : WriteWindow v 8)
    (curPins : LPins8 m Layout.sym_caml_fl_cur_wsz bc) (headPins : LPins8 m (slot w).toNat bh)
    (mergePins : LPins8 m (slot w + 8#64).toNat bm)
    (mergeCur : Layout.sym_caml_fl_cur_wsz + 8 ≤ (slot w + 8#64).toNat ∨
      (slot w + 8#64).toNat + 8 ≤ Layout.sym_caml_fl_cur_wsz)
    (mergeV : v.toNat + 8 ≤ (slot w + 8#64).toNat ∨ (slot w + 8#64).toNat + 8 ≤ v.toNat) :
    AccessPlan m (insertRegs ra v w) (bc :: bh :: bm :: lds) (blk bf_insert_remnant_smallX605cFSeg).body := by
  simp only [blk, bf_insert_remnant_smallX605cFSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply curWrite.read.ld rfl (by addr_simp)
    simpa [stepMemM, mkLine, decodeM, stepLdsM, Layout.sym_caml_fl_cur_wsz] using curPins
  · apply slotWrite.read.ld rfl (by addr_simp)
    simpa [stepMemM, mkLine, decodeM, stepLdsM] using headPins
  · apply curWrite.sd rfl (by addr_simp)
  · apply vWrite.sd rfl (by addr_simp)
  · apply mergeRead.ld rfl (by addr_simp)
    simp only [stepMemM, mkLine, decodeM]
    refine lpins8_applyW (lpins8_applyW ?_ (by simp [wentryM, widthOfM]) ?_) (by simp [wentryM, widthOfM]) ?_
    · simpa [stepLdsM, mkLine, decodeM] using mergePins
    · simp only [wentryM]
      addr_simp
      simp [slot, BestFitSmall.slot, shift4, log16, Layout.sym_caml_fl_cur_wsz, Layout.sym_bf_small_fl,
        Layout.bf_small_size] at mergeCur
      omega
    · simp only [wentryM]
      addr_simp
      simp [slot, BestFitSmall.slot, shift4, log16, Layout.sym_bf_small_fl, Layout.bf_small_size] at mergeV
      omega
  · apply slotWrite.sd rfl (by addr_simp)

/-- The registers after the insertion block. -/
def inserted (ra v w : BitVec 64) (bc bh bm : List (BitVec 8)) (lds : List (List (BitVec 8))) : GRegs :=
  runGM (blk bf_insert_remnant_smallX605cFSeg).body (insertRegs ra v w) (bc :: bh :: bm :: lds)

structure InsertedSrc (ra v w : BitVec 64) (bm : List (BitVec 8)) (L : GRegs) : Prop where
  merge : srcVal 13 L = bytesVal .ld bm
  slot : srcVal 14 L = slot w
  v : srcVal 10 L = v
  w : srcVal 15 L = w
  ra : srcVal 1 L = ra

theorem inserted_src (ra v w : BitVec 64) (bc bh bm : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    InsertedSrc ra v w bm (inserted ra v w bc bh bm lds) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [inserted] <;> rem_simp

theorem repaired_log (ra v w : BitVec 64) (bc bh bm bp : List (BitVec 8)) :
    (evalBlocks repaired (SegEvalState.init (insertRegs ra v w) [bc, bh, bm, bp])).log =
      [(Layout.sym_caml_fl_cur_wsz, 8, bytesVal .ld bc + 1#64 + w), (v.toNat, 8, bytesVal .ld bh),
       ((slot w).toNat, 8, v), ((bytesVal .ld bm + 8#64).toNat, 8, v),
       (Layout.sym_bf_small_map, 4, bit w ||| bytesVal .lw bp)] := by
  simp only [repaired, evalBlocks, evalBlock, SegEvalState.init]
  rem_simp
  rfl

theorem same_body : (blk bf_insert_remnant_smallX605cTSeg).body = (blk bf_insert_remnant_smallX605cFSeg).body := rfl

theorem slot_eq (w : BitVec 64) : slot w = BfShape.slot w.toNat := by
  simp only [slot, BfShape.slot, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem slot_nat {w : BitVec 64} (hi : w.toNat ≤ 16) : (slot w).toNat = Layout.sym_bf_small_fl + 16 * w.toNat := by
  rw [slot_eq]; exact BfShape.slot_toNat _ (by simpa only [Layout.bf_small_count] using hi)

theorem merge_nat {w : BitVec 64} (hi : w.toNat ≤ 16) :
    (slot w + 8#64).toNat = Layout.sym_bf_small_fl + 16 * w.toNat + 8 := by
  rw [BitVec.toNat_add, slot_nat hi]; simp only [BitVec.toNat_ofNat, Layout.sym_bf_small_fl]; omega

/-! ## Statics -/

theorem cur_write : WriteWindow (BitVec.ofNat 64 Layout.sym_caml_fl_cur_wsz) 8 := by
  constructor <;> simp [Layout.sym_caml_fl_cur_wsz, Layout.sym_tohost]

theorem map_write : WriteWindow (BitVec.ofNat 64 Layout.sym_bf_small_map) 4 := by
  constructor <;> simp [Layout.sym_bf_small_map, Layout.sym_tohost]

theorem slot_window {w : BitVec 64} (hi : w.toNat ≤ 16) : WriteWindow (slot w) 8 := by
  rw [slot_eq]; exact BfShape.slot_write _ (by simpa only [Layout.bf_small_count] using hi)

theorem merge_window {w : BitVec 64} (hi : w.toNat ≤ 16) : WriteWindow (slot w + 8#64) 8 := by
  have h := merge_nat hi
  constructor <;> rw [h] <;> simp only [Layout.sym_bf_small_fl, Layout.sym_tohost] <;> omega

/-! ## The insertion tail as a summary -/

def insertLoads (w : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m Layout.sym_caml_fl_cur_wsz, read8 m (slot w).toNat, read8 m (slot w + 8#64).toNat,
    read4 m Layout.sym_bf_small_map]

/-- The list's head and merge cursor before the insertion. -/
def head (w : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (slot w).toNat 8
def cursor (w : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (slot w + 8#64).toNat 8

/-- The insertion's stores. -/
def insertLog (v w : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List WEntry :=
  [(Layout.sym_caml_fl_cur_wsz, 8, bytesT m Layout.sym_caml_fl_cur_wsz 8 + 1#64 + w), (v.toNat, 8, head w m),
    ((slot w).toNat, 8, v)] ++
  (if cursor w m = slot w then [((slot w + 8#64).toNat, 8, v)] else []) ++
  [(Layout.sym_bf_small_map, 4, bit w ||| bytesVal .lw (read4 m Layout.sym_bf_small_map))]

structure InsertInput (ra v w : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ x, c.σ.regs.get? Register.minstret = some x
  code : Code.Bf_insert_remnant_smallLoaded c.σ.mem
  registers : GHolds c.σ (insertRegs ra v w)
  aligned : ra.toNat % 4 = 0
  positive : 1 ≤ w.toNat
  small : w.toNat ≤ 16
  heap : Vsa.Sim.DlHeap.heapStart ≤ v.toNat
  remnant : WriteWindow v 8

structure InsertPost (ra v w : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  memory : after.σ.mem = writeLog before.σ.mem (insertLog v w before.σ.mem)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ x, after.σ.regs.get? Register.minstret = some x
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [11, 12, 13, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

def allBlocks : List BBlock :=
  [blk bf_insert_remnant_smallX603cTSeg, blk bf_insert_remnant_smallX603cFSeg, blk bf_insert_remnant_smallX604cTSeg,
    blk bf_insert_remnant_smallX604cFSeg, blk bf_insert_remnant_smallX605cTSeg, blk bf_insert_remnant_smallX605cFSeg,
    blk bf_insert_remnant_smallX6098Seg, blk bf_insert_remnant_smallX60b8Seg, blk bf_insert_remnant_smallX60bcTSeg,
    blk bf_insert_remnant_smallX60bcFSeg, blk bf_insert_remnant_smallX60c8Seg, blk bf_insert_remnant_smallX60ccSeg]

theorem all_code {mem : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Bf_insert_remnant_smallLoaded mem) :
    ChainCode mem allBlocks := by
  intro b member
  simp only [allBlocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [blk, bf_insert_remnant_smallX603cTSeg, bf_insert_remnant_smallX603cFSeg,
    bf_insert_remnant_smallX604cTSeg, bf_insert_remnant_smallX604cFSeg, bf_insert_remnant_smallX605cTSeg,
    bf_insert_remnant_smallX605cFSeg, bf_insert_remnant_smallX6098Seg, bf_insert_remnant_smallX60b8Seg,
    bf_insert_remnant_smallX60bcTSeg, bf_insert_remnant_smallX60bcFSeg, bf_insert_remnant_smallX60c8Seg,
    bf_insert_remnant_smallX60ccSeg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts code with "Vsa.Sim.Code.bf_insert_remnant_small_at_"

theorem code_of {mem : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Bf_insert_remnant_smallLoaded mem)
    {bs : List BBlock} (sub : ∀ b ∈ bs, b ∈ allBlocks) : ChainCode mem bs :=
  fun b h => all_code code b (sub b h)

theorem sub_plain : ∀ b ∈ plain, b ∈ allBlocks := by
  intro b h; simp only [plain, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [allBlocks]
theorem sub_repaired : ∀ b ∈ repaired, b ∈ allBlocks := by
  intro b h; simp only [repaired, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [allBlocks]

theorem plain_pc (ra v w : BitVec 64) (bc bh bm bp : List (BitVec 8)) (aligned : ra.toNat % 4 = 0) :
    evalBlocksPC insertPc (SegEvalState.init (insertRegs ra v w) [bc, bh, bm, bp]) plain = ra := by
  simp only [evalBlocksPC, plain, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0]
  rem_simp
  have h := ret_tgt ra aligned
  rwa [FfsLowest.add_zero12] at h

theorem repaired_pc (ra v w : BitVec 64) (bc bh bm bp : List (BitVec 8)) (aligned : ra.toNat % 4 = 0) :
    evalBlocksPC insertPc (SegEvalState.init (insertRegs ra v w) [bc, bh, bm, bp]) repaired = ra := by
  simp only [evalBlocksPC, repaired, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0]
  rem_simp
  have h := ret_tgt ra aligned
  rwa [FfsLowest.add_zero12] at h

theorem fix_regs (L : GRegs) (lds : List (List (BitVec 8))) :
    runGM (blk bf_insert_remnant_smallX60ccSeg).body L lds = L := rfl

theorem fix_log (L : GRegs) (lds : List (List (BitVec 8))) :
    wlogM (blk bf_insert_remnant_smallX60ccSeg).body L lds = [((srcVal 13 L + 8#64).toNat, 8, srcVal 10 L)] := by
  simp [blk, bf_insert_remnant_smallX60ccSeg, wlogM, wentryM, eaddrM, mkLine, decodeM, widthOfM, stepGM, wvalM,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem fix_access (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (lds : List (List (BitVec 8))) (x : BitVec 64)
    (merge : srcVal 13 L = x) (window : WriteWindow (x + 8#64) 8) :
    AccessPlan m L lds (blk bf_insert_remnant_smallX60ccSeg).body := by
  simp only [blk, bf_insert_remnant_smallX60ccSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  apply window.sd rfl
  simp [eaddrM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, merge]

theorem ret_body (L : GRegs) (lds : List (List (BitVec 8))) :
    runGM (blk bf_insert_remnant_smallX60b8Seg).body L lds = L := rfl

theorem map_src_ra (ra v w : BitVec 64) (bc bh bm : List (BitVec 8)) (lds lds' : List (List (BitVec 8))) :
    srcVal 1 (runGM (blk bf_insert_remnant_smallX6098Seg).body (inserted ra v w bc bh bm lds) lds') = ra := by
  simp only [inserted]; rem_simp

theorem map_access (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (bp : List (BitVec 8))
    (lds : List (List (BitVec 8))) (pins : LPins4 m Layout.sym_bf_small_map bp) :
    AccessPlan m L (bp :: lds) (blk bf_insert_remnant_smallX6098Seg).body := by
  simp only [blk, bf_insert_remnant_smallX6098Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply map_write.read.lw rfl (by addr_simp)
    simpa [stepMemM, mkLine, decodeM, stepLdsM, Layout.sym_bf_small_map] using pins
  · apply map_write.sw rfl (by addr_simp)

theorem map_outside {v w : BitVec 64} (small : w.toNat ≤ 16) (heap : Vsa.Sim.DlHeap.heapStart ≤ v.toNat)
    (log : List WEntry)
    (member : ∀ e ∈ log, e.1 = Layout.sym_caml_fl_cur_wsz ∨ e.1 = v.toNat ∨ e.1 = (slot w).toNat ∨
      e.1 = (slot w + 8#64).toNat)
    (width : ∀ e ∈ log, e.2.1 = 8) : OutLRange log Layout.sym_bf_small_map 4 := by
  apply outLRange_of_forall
  intro e h
  have hw := width e h
  rcases member e h with h1 | h1 | h1 | h1 <;> rw [h1] <;>
    simp only [slot_nat small, merge_nat small, Layout.sym_bf_small_map, Layout.sym_caml_fl_cur_wsz,
      Layout.sym_bf_small_fl, Vsa.Sim.DlHeap.heapStart] at heap ⊢ <;> omega

/-- **The insertion tail**: the counter, the push, the cursor repair and the bitmap. -/
theorem insert_tail {ra v w c} (input : InsertInput ra v w c) :
    FnSummary insertPc (fun d => d = c) (InsertPost ra v w c) := by
  have small := input.small
  have heap := input.heap
  have mergeApart : ∀ x, x = Layout.sym_caml_fl_cur_wsz ∨ x = v.toNat →
      x + 8 ≤ (slot w + 8#64).toNat ∨ (slot w + 8#64).toNat + 8 ≤ x := by
    intro x hx
    rcases hx with rfl | rfl <;>
      simp only [merge_nat small, Layout.sym_caml_fl_cur_wsz, Layout.sym_bf_small_fl,
        Vsa.Sim.DlHeap.heapStart] at heap ⊢ <;> omega
  have access := insert_access c.σ.mem ra v w (read8 c.σ.mem Layout.sym_caml_fl_cur_wsz)
    (read8 c.σ.mem (slot w).toNat) (read8 c.σ.mem (slot w + 8#64).toNat) [read4 c.σ.mem Layout.sym_bf_small_map]
    cur_write (slot_window small) (merge_window small).read input.remnant (read8_pins _ _) (read8_pins _ _)
    (read8_pins _ _) (mergeApart _ (Or.inl rfl)) (mergeApart _ (Or.inr rfl))
  have src := inserted_src ra v w (read8 c.σ.mem Layout.sym_caml_fl_cur_wsz) (read8 c.σ.mem (slot w).toNat)
    (read8 c.σ.mem (slot w + 8#64).toNat) [read4 c.σ.mem Layout.sym_bf_small_map]
  have firstLog := insert_log ra v w (read8 c.σ.mem Layout.sym_caml_fl_cur_wsz) (read8 c.σ.mem (slot w).toNat)
    (read8 c.σ.mem (slot w + 8#64).toNat) [read4 c.σ.mem Layout.sym_bf_small_map]
  have keys : KeysOK (keysG (insertRegs ra v w)) := by change KeysOK [1, 10, 15]; decide
  by_cases atSlot : cursor w c.σ.mem = slot w
  · -- the cursor was the slot: repair it
    have cursorEq : bytesVal .ld (Primitives.read8 c.σ.mem (slot w + 8#64).toNat) = slot w := by
      rw [read8_value]; exact atSlot
    have chainA : ChainAccess c.σ.mem (insertRegs ra v w) (insertLoads w c.σ.mem) repaired := by
      simp only [insertLoads, repaired]
      apply ChainAccess.cons ⟨by rw [same_body]; exact access, ?_⟩
      · rw [same_body]
        change ChainAccess _ (inserted ra v w _ _ _ _) _ _
        rw [firstLog]
        apply ChainAccess.cons ⟨fix_access _ _ _ (slot w) (by rw [src.merge, cursorEq]) (merge_window small), trivial⟩
        rw [fix_regs, fix_log, src.merge, src.v, cursorEq]
        apply ChainAccess.cons ⟨map_access _ _ _ _ (lpins4_writeLog (lpins4_writeLog (read4_pins _ _)
          (map_outside small heap _
            (by intro e h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl | rfl <;> simp)
            (by intro e h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl | rfl <;> rfl)))
          (map_outside small heap _
            (by intro e h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                subst h; simp)
            (by intro e h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                subst h; rfl))), trivial⟩
        apply ChainAccess.cons ⟨by simp [blk, bf_insert_remnant_smallX60b8Seg, AccessPlan], ?_⟩ ChainAccess.nil
        change (Sail.BitVec.update (srcVal 1 _ + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
        rw [ret_body, map_src_ra, ret_tgt ra input.aligned]; exact input.aligned
      · change guardB bop.BEQ (srcVal 13 (runGM (blk bf_insert_remnant_smallX605cTSeg).body _ _))
          (srcVal 14 (runGM (blk bf_insert_remnant_smallX605cTSeg).body _ _)) = true
        rw [same_body]
        change guardB bop.BEQ (srcVal 13 (inserted ra v w _ _ _ _)) (srcVal 14 (inserted ra v w _ _ _ _)) = true
        rw [src.merge, src.slot]
        simp only [guardB]
        exact beq_iff_eq.mpr cursorEq
    have summary := block_summary repaired insertPc (insertRegs ra v w) (insertLoads w c.σ.mem) c
      ⟨input.good, input.minstret, input.registers, keys,
        chainPlan_facts (code_of input.code sub_repaired) chainA,
        by change ChainOK insertPc [1, 10, 15] repaired; decide, input.tick⟩
    apply summary.weaken (fun _ h => h)
    intro after post
    refine ⟨?_, ?_, post.good, post.tick, post.minstret, post.output, ?_⟩
    · rw [PCAt, post.pc, insertLoads, repaired_pc _ _ _ _ _ _ _ input.aligned]
    · rw [post.memory, insertLoads, repaired_log, cursorEq]
      simp only [insertLog, head, if_pos atSlot, read8_value, List.nil_append, List.cons_append,
        List.append_nil]
    · intro r noise outside
      exact post.frame r noise (fun n hn => outside n (by
        have h : ∀ n ∈ wrChain repaired, n ∈ [11, 12, 13, 14, 15] := by decide
        exact h n hn))
  · have chainA : ChainAccess c.σ.mem (insertRegs ra v w) (insertLoads w c.σ.mem) plain := by
      simp only [insertLoads, plain]
      apply ChainAccess.cons ⟨access, ?_⟩
      · change ChainAccess _ (inserted ra v w _ _ _ _) _ _
        rw [firstLog]
        apply ChainAccess.cons ⟨map_access _ _ _ _ (lpins4_writeLog (read4_pins _ _) (map_outside small heap _
          (by intro e h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl <;> simp)
          (by intro e h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl <;> rfl))), trivial⟩
        apply ChainAccess.cons ⟨by simp [blk, bf_insert_remnant_smallX60b8Seg, AccessPlan], ?_⟩ ChainAccess.nil
        change (Sail.BitVec.update (srcVal 1 _ + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
        rw [ret_body, map_src_ra, ret_tgt ra input.aligned]; exact input.aligned
      · change guardB bop.BEQ (srcVal 13 (inserted ra v w _ _ _ _)) (srcVal 14 (inserted ra v w _ _ _ _)) = false
        rw [src.merge, src.slot]
        simp only [guardB, read8_value]
        exact beq_eq_false_iff_ne.mpr atSlot
    have summary := block_summary plain insertPc (insertRegs ra v w) (insertLoads w c.σ.mem) c
      ⟨input.good, input.minstret, input.registers, keys,
        chainPlan_facts (code_of input.code sub_plain) chainA,
        by change ChainOK insertPc [1, 10, 15] plain; decide, input.tick⟩
    apply summary.weaken (fun _ h => h)
    intro after post
    refine ⟨?_, ?_, post.good, post.tick, post.minstret, post.output, ?_⟩
    · rw [PCAt, post.pc, insertLoads, plain_pc _ _ _ _ _ _ _ input.aligned]
    · rw [post.memory, insertLoads, plain_log]
      simp only [insertLog, head, if_neg atSlot, read8_value, List.nil_append, List.cons_append,
        List.append_nil]
    · intro r noise outside
      exact post.frame r noise (fun n hn => outside n (by
        have h : ∀ n ∈ wrChain plain, n ∈ [11, 12, 13, 14, 15] := by decide
        exact h n hn))

/-! ## The head (`0x8000603c`): zero size, sweep-phase deferral -/

def pc : BitVec 64 := 0x8000603c#64
def entryRegs (ra v : BitVec 64) : GRegs := [(1, ra), (10, v)]

/-- `Wosize_val v`, the remnant's size (`srli 10` of its header). -/
def size (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m (v - 8#64).toNat 8 >>> 10
/-- `caml_gc_phase`, sign-extended (`lw`). -/
def phase (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 :=
  bytesVal .lw (read4 m Layout.sym_caml_gc_phase)
def sweepHp (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 := bytesT m Layout.sym_caml_gc_sweep_hp 8

/-- The sweeper will find `v` (`Phase_sweep` and `Hp_val v ≥ caml_gc_sweep_hp`). -/
def deferred (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  phase m = 2#64 ∧ sweepHp m ≤ v - 8#64

def zeroC : List BBlock := [blk bf_insert_remnant_smallX603cTSeg, blk bf_insert_remnant_smallX60b8Seg]
def directC : List BBlock := [blk bf_insert_remnant_smallX603cFSeg, blk bf_insert_remnant_smallX604cFSeg]
def sweptC : List BBlock := [blk bf_insert_remnant_smallX603cFSeg, blk bf_insert_remnant_smallX604cTSeg,
  blk bf_insert_remnant_smallX60bcTSeg, blk bf_insert_remnant_smallX60b8Seg]
def lateC : List BBlock := [blk bf_insert_remnant_smallX603cFSeg, blk bf_insert_remnant_smallX604cTSeg,
  blk bf_insert_remnant_smallX60bcFSeg, blk bf_insert_remnant_smallX60c8Seg]

macro "head_simp" : tactic => `(tactic|
  simp [blk, bf_insert_remnant_smallX603cTSeg, bf_insert_remnant_smallX603cFSeg, bf_insert_remnant_smallX604cTSeg,
    bf_insert_remnant_smallX604cFSeg, bf_insert_remnant_smallX60bcTSeg, bf_insert_remnant_smallX60bcFSeg,
    bf_insert_remnant_smallX60c8Seg, bf_insert_remnant_smallX60b8Seg, entryRegs,
    runGM, wlogM, wentryM, eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    widthOfM, shamtOf, Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    Layout.sym_caml_gc_phase, Layout.sym_caml_gc_sweep_hp, BitVec.sub_eq_add_neg, ldsRunM])

theorem head_a5 (ra v : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    srcVal 15 (runGM (blk bf_insert_remnant_smallX603cFSeg).body (entryRegs ra v) (b :: lds)) =
      bytesVal .ld b >>> 10 := by
  head_simp
  rfl

theorem body603 : (blk bf_insert_remnant_smallX603cTSeg).body = (blk bf_insert_remnant_smallX603cFSeg).body := rfl
theorem body604 : (blk bf_insert_remnant_smallX604cTSeg).body = (blk bf_insert_remnant_smallX604cFSeg).body := rfl
theorem body60bc : (blk bf_insert_remnant_smallX60bcTSeg).body = (blk bf_insert_remnant_smallX60bcFSeg).body := rfl

/-- Registers after each head block. -/
def r1 (ra v : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8))) : GRegs :=
  runGM (blk bf_insert_remnant_smallX603cFSeg).body (entryRegs ra v) (b :: lds)
def r2 (ra v : BitVec 64) (b bp : List (BitVec 8)) (lds : List (List (BitVec 8))) : GRegs :=
  runGM (blk bf_insert_remnant_smallX604cFSeg).body (r1 ra v b (bp :: lds)) (bp :: lds)
def r3 (ra v : BitVec 64) (b bp bs : List (BitVec 8)) (lds : List (List (BitVec 8))) : GRegs :=
  runGM (blk bf_insert_remnant_smallX60bcFSeg).body (r2 ra v b bp (bs :: lds)) (bs :: lds)

structure Kept (ra v : BitVec 64) (b : List (BitVec 8)) (L : GRegs) : Prop where
  ra : srcVal 1 L = ra
  v : srcVal 10 L = v
  size : srcVal 15 L = bytesVal .ld b >>> 10

theorem kept1 (ra v : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8))) : Kept ra v b (r1 ra v b lds) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r1] <;> head_simp <;> rfl

theorem kept2 (ra v : BitVec 64) (b bp : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    Kept ra v b (r2 ra v b bp lds) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r2, r1] <;> head_simp <;> rfl

theorem kept3 (ra v : BitVec 64) (b bp bs : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    Kept ra v b (r3 ra v b bp bs lds) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r3, r2, r1] <;> head_simp <;> rfl

theorem phase_src (ra v : BitVec 64) (b bp : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    srcVal 12 (r2 ra v b bp lds) = bytesVal .lw bp ∧ srcVal 13 (r2 ra v b bp lds) = 2#64 := by
  refine ⟨?_, ?_⟩ <;> simp only [r2, r1] <;> head_simp

theorem sweep_src (ra v : BitVec 64) (b bp bs : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    srcVal 14 (r3 ra v b bp bs lds) = v - 8#64 ∧ srcVal 13 (r3 ra v b bp bs lds) = bytesVal .ld bs := by
  refine ⟨?_, ?_⟩ <;> simp only [r3, r2, r1] <;> head_simp

theorem phase_read : ReadWindow (BitVec.ofNat 64 Layout.sym_caml_gc_phase) 4 := by
  constructor <;> simp [Layout.sym_caml_gc_phase, Layout.sym_tohost]

theorem sweep_read : ReadWindow (BitVec.ofNat 64 Layout.sym_caml_gc_sweep_hp) 8 := by
  constructor <;> simp [Layout.sym_caml_gc_sweep_hp, Layout.sym_tohost]

theorem acc603 (m : Std.ExtHashMap Nat (BitVec 8)) (ra v : BitVec 64) (b : List (BitVec 8))
    (lds : List (List (BitVec 8))) (window : ReadWindow (v - 8#64) 8) (pins : LPins8 m (v - 8#64).toNat b) :
    AccessPlan m (entryRegs ra v) (b :: lds) (blk bf_insert_remnant_smallX603cFSeg).body := by
  simp only [blk, bf_insert_remnant_smallX603cFSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  apply window.ld rfl (by head_simp)
  simpa [stepMemM, mkLine, decodeM, stepLdsM] using pins

theorem acc604 (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (bp : List (BitVec 8))
    (lds : List (List (BitVec 8))) (pins : LPins4 m Layout.sym_caml_gc_phase bp) :
    AccessPlan m L (bp :: lds) (blk bf_insert_remnant_smallX604cFSeg).body := by
  simp only [blk, bf_insert_remnant_smallX604cFSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  apply phase_read.lw rfl (by head_simp)
  simpa [stepMemM, mkLine, decodeM, stepLdsM, Layout.sym_caml_gc_phase] using pins

theorem acc60bc (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (bs : List (BitVec 8))
    (lds : List (List (BitVec 8))) (pins : LPins8 m Layout.sym_caml_gc_sweep_hp bs) :
    AccessPlan m L (bs :: lds) (blk bf_insert_remnant_smallX60bcFSeg).body := by
  simp only [blk, bf_insert_remnant_smallX60bcFSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  apply sweep_read.ld rfl (by head_simp)
  simpa [stepMemM, mkLine, decodeM, stepLdsM, Layout.sym_caml_gc_sweep_hp] using pins

/-- `v` goes back on its list. -/
def Inserts (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop := size v m ≠ 0 ∧ ¬ deferred v m

instance (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Decidable (Inserts v m) := by
  unfold Inserts deferred; infer_instance

/-- The whole call's stores. -/
def effect (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List WEntry :=
  if Inserts v m then insertLog v (size v m) m else []

structure Input (ra v : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ x, c.σ.regs.get? Register.minstret = some x
  code : Code.Bf_insert_remnant_smallLoaded c.σ.mem
  registers : GHolds c.σ (entryRegs ra v)
  aligned : ra.toNat % 4 = 0
  header : ReadWindow (v - 8#64) 8
  remnant : WriteWindow v 8
  heap : Vsa.Sim.DlHeap.heapStart ≤ v.toNat
  small : (size v c.σ.mem).toNat ≤ 16

/-- `bf_insert_remnant_small(v)` has returned. -/
structure Post (ra v : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  memory : after.σ.mem = writeLog before.σ.mem (effect v before.σ.mem)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ x, after.σ.regs.get? Register.minstret = some x
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [11, 12, 13, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem sub_chain {bs : List BBlock} (h : ∀ b ∈ bs, b ∈ allBlocks) : ∀ b ∈ bs, b ∈ allBlocks := h

theorem size_eq (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    bytesVal .ld (Primitives.read8 m (v - 8#64).toNat) >>> 10 = size v m := by
  rw [read8_value]; rfl

theorem phase_eq (m : Std.ExtHashMap Nat (BitVec 8)) :
    bytesVal .lw (read4 m Layout.sym_caml_gc_phase) = phase m := rfl

theorem sweep_eq (m : Std.ExtHashMap Nat (BitVec 8)) :
    bytesVal .ld (Primitives.read8 m Layout.sym_caml_gc_sweep_hp) = sweepHp m := by
  rw [read8_value]; rfl

theorem ret_ok (ra : BitVec 64) (aligned : ra.toNat % 4 = 0) (L : GRegs) (lds : List (List (BitVec 8)))
    (lookup : srcVal 1 L = ra) : TermFactsO (runGM (blk bf_insert_remnant_smallX60b8Seg).body L lds)
      (blk bf_insert_remnant_smallX60b8Seg).term := by
  change (Sail.BitVec.update (srcVal 1 _ + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat
    % 4 = 0
  rw [ret_body, lookup, ret_tgt ra aligned]; exact aligned

theorem ret_access (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (lds : List (List (BitVec 8))) :
    AccessPlan m L lds (blk bf_insert_remnant_smallX60b8Seg).body := by
  simp [blk, bf_insert_remnant_smallX60b8Seg, AccessPlan]

theorem frame_of {before after : Config} {bs : List BBlock} (written : ∀ n ∈ wrChain bs, n ∈ [11, 12, 13, 14, 15])
    (post : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ wrChain bs, (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [11, 12, 13, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r :=
  fun r noise outside => post r noise (fun n hn => outside n (written n hn))

theorem zero_case {ra v c} (input : Input ra v c) (zero : size v c.σ.mem = 0) :
    FnSummary pc (fun d => d = c) (Post ra v c) := by
  let b := Primitives.read8 c.σ.mem (v - 8#64).toNat
  have chainA : ChainAccess c.σ.mem (entryRegs ra v) [b] zeroC := by
    simp only [zeroC]
    apply ChainAccess.cons ⟨by rw [body603]; exact acc603 _ _ _ _ _ input.header (read8_pins _ _), ?_⟩
    · rw [body603]
      change ChainAccess _ (r1 ra v b []) _ _
      exact ChainAccess.cons ⟨ret_access _ _ _, ret_ok ra input.aligned _ _ (kept1 ra v b []).ra⟩ ChainAccess.nil
    · rw [body603]
      change guardB bop.BEQ (srcVal 15 (r1 ra v b [])) (srcVal 0 (r1 ra v b [])) = true
      rw [(kept1 ra v b []).size, size_eq]
      simp only [guardB, zero]; rfl
  have summary := block_summary zeroC pc (entryRegs ra v) [b] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [1, 10]; decide,
      chainPlan_facts (code_of input.code (by
        intro x h; simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp [allBlocks])) chainA,
      by change ChainOK pc [1, 10] zeroC; decide, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have none : ¬ Inserts v c.σ.mem := fun h => h.1 zero
  refine ⟨?_, ?_, post.good, post.tick, post.minstret, post.output, frame_of (by decide) post.frame⟩
  · rw [PCAt, post.pc]
    simp only [evalBlocksPC, zeroC, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0]
    head_simp
    have h := ret_tgt ra input.aligned
    rwa [FfsLowest.add_zero12] at h
  · rw [post.memory, effect, if_neg none]
    simp only [zeroC, evalBlocks, evalBlock, SegEvalState.init]
    head_simp

theorem guard603F (ra v : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (nonzero : bytesVal .ld b >>> 10 ≠ 0#64) :
    TermFactsO (runGM (blk bf_insert_remnant_smallX603cFSeg).body (entryRegs ra v) (b :: lds))
      (blk bf_insert_remnant_smallX603cFSeg).term := by
  change guardB bop.BEQ (srcVal 15 (r1 ra v b lds)) (srcVal 0 (r1 ra v b lds)) = false
  rw [(kept1 ra v b lds).size]
  simp only [guardB]
  exact beq_eq_false_iff_ne.mpr nonzero

theorem swept_case {ra v c} (input : Input ra v c) (nonzero : size v c.σ.mem ≠ 0)
    (sweep : phase c.σ.mem = 2#64) (above : sweepHp c.σ.mem ≤ v - 8#64) :
    FnSummary pc (fun d => d = c) (Post ra v c) := by
  let b := Primitives.read8 c.σ.mem (v - 8#64).toNat
  let bp := read4 c.σ.mem Layout.sym_caml_gc_phase
  let bs := Primitives.read8 c.σ.mem Layout.sym_caml_gc_sweep_hp
  have chainA : ChainAccess c.σ.mem (entryRegs ra v) [b, bp, bs] sweptC := by
    simp only [sweptC]
    apply ChainAccess.cons ⟨acc603 _ _ _ _ _ input.header (read8_pins _ _),
      guard603F ra v b _ (by rw [size_eq]; exact nonzero)⟩
    change ChainAccess _ (r1 ra v b [bp, bs]) _ _
    apply ChainAccess.cons ⟨by rw [body604]; exact acc604 _ _ _ _ (read4_pins _ _), ?_⟩
    · rw [body604]
      change ChainAccess _ (r2 ra v b bp [bs]) _ _
      apply ChainAccess.cons ⟨by rw [body60bc]; exact acc60bc _ _ _ _ (read8_pins _ _), ?_⟩
      · rw [body60bc]
        change ChainAccess _ (r3 ra v b bp bs []) _ _
        exact ChainAccess.cons ⟨ret_access _ _ _, ret_ok ra input.aligned _ _ (kept3 ra v b bp bs []).ra⟩
          ChainAccess.nil
      · rw [body60bc]
        change guardB bop.BGEU (srcVal 14 (r3 ra v b bp bs [])) (srcVal 13 (r3 ra v b bp bs [])) = true
        rw [(sweep_src ra v b bp bs []).1, (sweep_src ra v b bp bs []).2, sweep_eq]
        simp only [guardB]
        have h := BitVec.le_def.mp above
        simp only [Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, decide_eq_true_eq, ge_iff_le]
        exact Int.ofNat_le.mpr h
    · rw [body604]
      change guardB bop.BEQ (srcVal 12 (r2 ra v b bp [bs])) (srcVal 13 (r2 ra v b bp [bs])) = true
      rw [(phase_src ra v b bp [bs]).1, (phase_src ra v b bp [bs]).2, phase_eq]
      simp only [guardB, sweep]; rfl
  have summary := block_summary sweptC pc (entryRegs ra v) [b, bp, bs] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [1, 10]; decide,
      chainPlan_facts (code_of input.code (by
        intro x h; simp only [sweptC, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp [allBlocks])) chainA,
      by change ChainOK pc [1, 10] sweptC; decide, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have none : ¬ Inserts v c.σ.mem := fun h => h.2 ⟨sweep, above⟩
  refine ⟨?_, ?_, post.good, post.tick, post.minstret, post.output, frame_of (by decide) post.frame⟩
  · rw [PCAt, post.pc]
    simp only [evalBlocksPC, sweptC, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0]
    head_simp
    have h := ret_tgt ra input.aligned
    rwa [FfsLowest.add_zero12] at h
  · rw [post.memory, effect, if_neg none]
    simp only [sweptC, evalBlocks, evalBlock, SegEvalState.init]
    head_simp

structure Looks (ra v : BitVec 64) (b : List (BitVec 8)) (L : GRegs) : Prop where
  ra : lookupG 1 L = some ra
  v : lookupG 10 L = some v
  size : lookupG 15 L = some (bytesVal .ld b >>> 10)

theorem looks2 (ra v : BitVec 64) (b bp : List (BitVec 8)) : Looks ra v b (r2 ra v b bp []) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r2, r1] <;> head_simp <;> rfl

theorem looks3 (ra v : BitVec 64) (b bp bs : List (BitVec 8)) : Looks ra v b (r3 ra v b bp bs []) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r3, r2, r1] <;> head_simp <;> rfl

theorem direct_regs (ra v : BitVec 64) (b bp : List (BitVec 8)) :
    (evalBlocks directC (SegEvalState.init (entryRegs ra v) [b, bp])).regs = r2 ra v b bp [] := rfl

theorem late_regs (ra v : BitVec 64) (b bp bs : List (BitVec 8)) :
    (evalBlocks lateC (SegEvalState.init (entryRegs ra v) [b, bp, bs])).regs = r3 ra v b bp bs [] := rfl

theorem direct_pc (ra v : BitVec 64) (b bp : List (BitVec 8)) :
    evalBlocksPC pc (SegEvalState.init (entryRegs ra v) [b, bp]) directC = insertPc := by
  simp only [evalBlocksPC, directC, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0]
  head_simp; rfl

theorem late_pc (ra v : BitVec 64) (b bp bs : List (BitVec 8)) :
    evalBlocksPC pc (SegEvalState.init (entryRegs ra v) [b, bp, bs]) lateC = insertPc := by
  simp only [evalBlocksPC, lateC, chainEndPC, SegEvalState.init, endPCB, tgtPCT, nextPC0]
  head_simp; rfl

theorem direct_log (ra v : BitVec 64) (b bp : List (BitVec 8)) :
    (evalBlocks directC (SegEvalState.init (entryRegs ra v) [b, bp])).log = [] := by
  simp only [directC, evalBlocks, evalBlock, SegEvalState.init]; head_simp

theorem late_log (ra v : BitVec 64) (b bp bs : List (BitVec 8)) :
    (evalBlocks lateC (SegEvalState.init (entryRegs ra v) [b, bp, bs])).log = [] := by
  simp only [lateC, evalBlocks, evalBlock, SegEvalState.init]; head_simp

/-- From the head's fall-through into the insertion tail. -/
theorem into_tail {c mid : Config} {bs : List BBlock} {lds : List (List (BitVec 8))}
    {ra v : BitVec 64} (input : Input ra v c) (nonzero : size v c.σ.mem ≠ 0) (inserts : Inserts v c.σ.mem)
    (post : BlockPost bs pc (entryRegs ra v) lds c mid) (atTail : PCAt insertPc mid)
    (looks : Looks ra v (Primitives.read8 c.σ.mem (v - 8#64).toNat) (evalBlocks bs (SegEvalState.init (entryRegs ra v) lds)).regs)
    (log : (evalBlocks bs (SegEvalState.init (entryRegs ra v) lds)).log = [])
    (written : ∀ n ∈ wrChain bs, n ∈ [11, 12, 13, 14, 15]) :
    ∃ after, Steps mid after ∧ Post ra v c after := by
  have memory : mid.σ.mem = c.σ.mem := by rw [post.memory, log]; rfl
  have w15 := looks.size
  rw [size_eq] at w15
  have tailInput : InsertInput ra v (size v c.σ.mem) mid :=
    ⟨post.good, post.tick, post.minstret, memory ▸ input.code,
      ⟨gholds_lookup _ post.regs looks.ra, gholds_lookup _ post.regs looks.v, gholds_lookup _ post.regs w15,
        True.intro⟩, input.aligned,
      by have := nonzero; rcases Nat.eq_zero_or_pos (size v c.σ.mem).toNat with h | h
         · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) nonzero
         · exact h,
      input.small, input.heap, input.remnant⟩
  obtain ⟨after, run, tail⟩ := (insert_tail tailInput).run mid ⟨atTail, rfl⟩
  refine ⟨after, run, tail.pc, ?_, tail.good, tail.tick, tail.minstret, tail.output.trans post.output, ?_⟩
  · rw [tail.memory, memory, effect, if_pos inserts]
  · intro r noise outside
    exact (tail.frame r noise outside).trans (frame_of written post.frame r noise outside)

theorem direct_case {ra v c} (input : Input ra v c) (nonzero : size v c.σ.mem ≠ 0)
    (notSweep : phase c.σ.mem ≠ 2#64) : FnSummary pc (fun d => d = c) (Post ra v c) := by
  let b := Primitives.read8 c.σ.mem (v - 8#64).toNat
  let bp := read4 c.σ.mem Layout.sym_caml_gc_phase
  have chainA : ChainAccess c.σ.mem (entryRegs ra v) [b, bp] directC := by
    simp only [directC]
    apply ChainAccess.cons ⟨acc603 _ _ _ _ _ input.header (read8_pins _ _),
      guard603F ra v b _ (by rw [size_eq]; exact nonzero)⟩
    change ChainAccess _ (r1 ra v b [bp]) _ _
    apply ChainAccess.cons ⟨acc604 _ _ _ _ (read4_pins _ _), ?_⟩ ChainAccess.nil
    change guardB bop.BEQ (srcVal 12 (r2 ra v b bp [])) (srcVal 13 (r2 ra v b bp [])) = false
    rw [(phase_src ra v b bp []).1, (phase_src ra v b bp []).2, phase_eq]
    simp only [guardB]
    exact beq_eq_false_iff_ne.mpr notSweep
  have summary := block_summary directC pc (entryRegs ra v) [b, bp] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [1, 10]; decide,
      chainPlan_facts (code_of input.code (by
        intro x h; simp only [directC, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp [allBlocks])) chainA,
      by change ChainOK pc [1, 10] directC; decide, input.tick⟩
  constructor
  rintro c0 ⟨pc0, rfl⟩
  obtain ⟨mid, run, post⟩ := summary.run c0 ⟨pc0, rfl⟩
  have atTail : PCAt insertPc mid := by rw [PCAt, post.pc, direct_pc]
  obtain ⟨after, run2, done⟩ := into_tail input nonzero ⟨nonzero, fun h => notSweep h.1⟩ post atTail
    (by rw [direct_regs]; exact looks2 ra v b bp) (direct_log ra v b bp) (by decide)
  exact ⟨after, run.trans run2, done⟩

theorem late_case {ra v c} (input : Input ra v c) (nonzero : size v c.σ.mem ≠ 0)
    (sweep : phase c.σ.mem = 2#64) (below : ¬ sweepHp c.σ.mem ≤ v - 8#64) :
    FnSummary pc (fun d => d = c) (Post ra v c) := by
  let b := Primitives.read8 c.σ.mem (v - 8#64).toNat
  let bp := read4 c.σ.mem Layout.sym_caml_gc_phase
  let bs := Primitives.read8 c.σ.mem Layout.sym_caml_gc_sweep_hp
  have chainA : ChainAccess c.σ.mem (entryRegs ra v) [b, bp, bs] lateC := by
    simp only [lateC]
    apply ChainAccess.cons ⟨acc603 _ _ _ _ _ input.header (read8_pins _ _),
      guard603F ra v b _ (by rw [size_eq]; exact nonzero)⟩
    change ChainAccess _ (r1 ra v b [bp, bs]) _ _
    apply ChainAccess.cons ⟨by rw [body604]; exact acc604 _ _ _ _ (read4_pins _ _), ?_⟩
    · rw [body604]
      change ChainAccess _ (r2 ra v b bp [bs]) _ _
      apply ChainAccess.cons ⟨acc60bc _ _ _ _ (read8_pins _ _), ?_⟩
      · change ChainAccess _ (r3 ra v b bp bs []) _ _
        exact ChainAccess.cons ⟨by simp [blk, bf_insert_remnant_smallX60c8Seg, AccessPlan], trivial⟩
          ChainAccess.nil
      · change guardB bop.BGEU (srcVal 14 (r3 ra v b bp bs [])) (srcVal 13 (r3 ra v b bp bs [])) = false
        rw [(sweep_src ra v b bp bs []).1, (sweep_src ra v b bp bs []).2, sweep_eq]
        have h : ¬ (sweepHp c.σ.mem).toNat ≤ (v - 8#64).toNat := fun h => below (BitVec.le_def.mpr h)
        simp only [guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, decide_eq_false_iff_not, ge_iff_le]
        exact fun h' => h (Int.ofNat_le.mp h')
    · rw [body604]
      change guardB bop.BEQ (srcVal 12 (r2 ra v b bp [bs])) (srcVal 13 (r2 ra v b bp [bs])) = true
      rw [(phase_src ra v b bp [bs]).1, (phase_src ra v b bp [bs]).2, phase_eq]
      simp only [guardB, sweep]; rfl
  have summary := block_summary lateC pc (entryRegs ra v) [b, bp, bs] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [1, 10]; decide,
      chainPlan_facts (code_of input.code (by
        intro x h; simp only [lateC, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp [allBlocks])) chainA,
      by change ChainOK pc [1, 10] lateC; decide, input.tick⟩
  constructor
  rintro c0 ⟨pc0, rfl⟩
  obtain ⟨mid, run, post⟩ := summary.run c0 ⟨pc0, rfl⟩
  have atTail : PCAt insertPc mid := by rw [PCAt, post.pc, late_pc]
  obtain ⟨after, run2, done⟩ := into_tail input nonzero ⟨nonzero, fun h => below h.2⟩ post atTail
    (by rw [late_regs]; exact looks3 ra v b bp bs) (late_log ra v b bp bs) (by decide)
  exact ⟨after, run.trans run2, done⟩

/-- **`bf_insert_remnant_small(v)`**: `v` goes back on list `Wosize_val v` unless it is
empty or the sweeper will find it (`Inserts`). -/
theorem insert {ra v c} (input : Input ra v c) : FnSummary pc (fun d => d = c) (Post ra v c) := by
  by_cases zero : size v c.σ.mem = 0
  · exact zero_case input zero
  · by_cases sweep : phase c.σ.mem = 2#64
    · by_cases above : sweepHp c.σ.mem ≤ v - 8#64
      · exact swept_case input zero sweep above
      · exact late_case input zero sweep above
    · exact direct_case input zero sweep

/-- The wrapper's complete write footprint, including both cursor branches.
The phase/zero-size return paths write nothing. -/
def writeWindows (v w : BitVec 64) : List W :=
  [⟨Layout.sym_caml_fl_cur_wsz,Layout.sym_caml_fl_cur_wsz + 8⟩,
   ⟨v.toNat,v.toNat + 8⟩,⟨(slot w).toNat,(slot w).toNat + 8⟩,
   ⟨(slot w + 8#64).toNat,(slot w + 8#64).toNat + 8⟩,
   ⟨Layout.sym_bf_small_map,Layout.sym_bf_small_map + 4⟩]

/-- Footprint of the actual insertion, for either merge-cursor branch. -/
theorem insertLog_inside (v w : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    LogInW (writeWindows v w) (insertLog v w m) := by
  unfold insertLog
  split <;> apply logInW_of_forall
  all_goals intro e member
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  · rcases member with ((rfl | rfl | rfl) | rfl) | rfl
    all_goals simp [writeWindows,InsideW]
  · rcases member with (rfl | rfl | rfl) | rfl
    all_goals simp_all [writeWindows,InsideW]

theorem effect_inside (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    LogInW (writeWindows v (size v m)) (effect v m) := by
  unfold effect
  split
  · exact insertLog_inside v (size v m) m
  · trivial

/-- Caller readback uses the named footprint rather than assuming that the
remnant helper preserves arbitrary saved words or free-list observations. -/
theorem Post.read {ra v before after a n} (post : Post ra v before after)
    (outside : OutWRange (writeWindows v (size v before.σ.mem)) a n) :
    bytesT after.σ.mem a n = bytesT before.σ.mem a n := by
  rw [post.memory]
  exact bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (effect_inside v before.σ.mem) outside)

/-- The helper's static stores are below the heap. A heap observation only
needs separation from the remnant's link word. -/
theorem writeWindows_out_heap {v w : BitVec 64} {a n : Nat}
    (small : w.toNat ≤ 16) (heap : Vsa.Sim.DlHeap.heapStart ≤ a)
    (apart : a + n ≤ v.toNat ∨ v.toNat + 8 ≤ a) :
    OutWRange (writeWindows v w) a n := by
  have hs := slot_nat small
  have hm := merge_nat small
  simp only [writeWindows,OutWRange]
  refine ⟨?_,apart,?_,?_,?_,True.intro⟩
  all_goals simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz,
    Layout.sym_bf_small_fl,Layout.sym_bf_small_map] at heap hs hm ⊢
  all_goals omega

/-- No wrapper branch writes allocator instructions. -/
theorem Post.allocator_code {ra v before after} (post : Post ra v before after)
    (code : Code.Bf_allocateLoaded before.σ.mem)
    (heap : Vsa.Sim.DlHeap.heapStart ≤ v.toNat) (small : (size v before.σ.mem).toNat ≤ 16) :
    Code.Bf_allocateLoaded after.σ.mem := by
  apply Code.bf_allocate_transport code
  intro a lo hi
  rw [post.memory]
  apply writeLog_out
  apply outL_of_range (OCaml.Vm.Sim.outLRange_of_windows (effect_inside v before.σ.mem) ?_)
    (Nat.le_refl a) (by omega : a < a + 1)
  have hs := slot_nat small
  have hm := merge_nat small
  simp only [writeWindows,OutWRange]
  simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz,
    Layout.sym_bf_small_fl,Layout.sym_bf_small_map] at heap hs hm ⊢
  exact ⟨by omega,by omega,by omega,by omega,by omega,True.intro⟩

/-- Exact accounting selected by the wrapper's real zero/sweep tests. -/
theorem counter_effect (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (heap : Vsa.Sim.DlHeap.heapStart ≤ v.toNat) (small : (size v m).toNat ≤ 16) :
    bytesT (writeLog m (effect v m)) Layout.sym_caml_fl_cur_wsz 8 =
      if Inserts v m then bytesT m Layout.sym_caml_fl_cur_wsz 8 + 1#64 + size v m
      else bytesT m Layout.sym_caml_fl_cur_wsz 8 := by
  unfold effect
  split
  · have hs := slot_nat small
    have hm := merge_nat small
    unfold insertLog
    split
    all_goals apply word_writeLog_at _ _ 0 _ _ rfl
    all_goals apply outLRange_of_forall
    all_goals intro e member
    all_goals simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    · rcases member with rfl | rfl | rfl | rfl
      all_goals simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz,
        Layout.sym_bf_small_fl,Layout.sym_bf_small_map] at heap hs hm ⊢
      all_goals omega
    · rcases member with rfl | rfl | rfl
      all_goals simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz,
        Layout.sym_bf_small_fl,Layout.sym_bf_small_map] at heap hs hm ⊢
      all_goals omega
  · rfl


/-- Bounded scalar certificate for the native SLLW bit. -/
theorem bit32 {w : BitVec 64} (lo : 1 ≤ w.toNat) (hi : w.toNat ≤ 16) :
    (bit w).setWidth 32 = 1#32 <<< (w.toNat-1) := by
  have cert : ∀ n < 17, 1 ≤ n →
      (bit (BitVec.ofNat 64 n)).setWidth 32 = 1#32 <<< (n-1) := by decide
  have eq : w = BitVec.ofNat 64 w.toNat := by simp
  conv => lhs; rw [eq]
  exact cert _ (by omega) lo

/-- Readbacks of the actual head/link/map stores, without expanding memory. -/
structure InsertReadbacks (v w : BitVec 64) (m m' : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  head : bytesT m' (slot w).toNat 8 = v
  link : bytesT m' v.toNat 8 = BestFitRemnant.head w m
  bits : BfShape.mapBits m' = BfShape.mapBits m ||| (1#32 <<< (w.toNat-1))

theorem insert_readbacks {v w : BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)}
    (lo : 1 ≤ w.toNat) (hi : w.toNat ≤ 16)
    (heap : Vsa.Sim.DlHeap.heapStart ≤ v.toNat) :
    InsertReadbacks v w m (writeLog m (insertLog v w m)) := by
  have hs := slot_nat hi
  have hm := merge_nat hi
  constructor
  · unfold insertLog
    split
    all_goals apply word_writeLog_at _ _ 2 _ _ rfl
    all_goals apply outLRange_of_forall
    all_goals intro e member
    all_goals simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      List.mem_cons,List.not_mem_nil,or_false] at member
    · rcases member with rfl | rfl
      all_goals dsimp only
      all_goals rw [hs]
      · rw [hm]; omega
      · simp only [Layout.sym_bf_small_map,Layout.sym_bf_small_fl] at hs ⊢; omega
    · subst member
      dsimp only
      rw [hs]
      simp only [Layout.sym_bf_small_map,Layout.sym_bf_small_fl]; omega
  · unfold insertLog
    split
    all_goals apply word_writeLog_at _ _ 1 _ _ rfl
    all_goals apply outLRange_of_forall
    all_goals intro e member
    all_goals simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      List.mem_cons,List.not_mem_nil,or_false] at member
    · rcases member with rfl | rfl | rfl
      all_goals dsimp only
      · rw [hs]; simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_fl] at heap ⊢; omega
      · rw [hm]; simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_fl] at heap ⊢; omega
      · simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_map] at heap ⊢; omega
    · rcases member with rfl | rfl
      all_goals dsimp only
      · rw [hs]; simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_fl] at heap ⊢; omega
      · simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_map] at heap ⊢; omega
  · rw [BfShape.mapBits,insertLog,writeLog_append,writeLog_append,word32_writeLog,
      BitVec.setWidth_or,bit32 lo hi]
    rw [BitVec.or_comm]
    congr 1
    simp only [read4_value,Functions.sign_extend,Sail.BitVec.signExtend,BfShape.mapBits]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
    simp only [hi,show i < 64 by omega,decide_true,ite_true,Bool.true_and]

/-- Original helper-entry separation of the new link from the represented
free blocks' link and header windows. The route derives it from physical
extents; this is not an assumption about the returned lists. -/
structure InsertApart (v : BitVec 64) (lists : Nat → List (BitVec 64)) : Prop where
  links : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ lists t,
    x.toNat+8 ≤ v.toNat ∨ v.toNat+8 ≤ x.toNat
  headers : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ lists t,
    Vsa.Sim.DlHeap.heapStart ≤ (x-8#64).toNat ∧
    ((x-8#64).toNat+8 ≤ v.toNat ∨ v.toNat+8 ≤ (x-8#64).toNat)

/-- Actual insertion preserves the represented lists, headers and bitmap. -/
theorem insert_representation {v w m lists} (lo : 1 ≤ w.toNat) (hi : w.toNat ≤ 16)
    (heap : Vsa.Sim.DlHeap.heapStart + 8 ≤ v.toNat) (window : ReadWindow v 8)
    (shape : BfShape.SmallShape m lists) (headers : BfShape.SmallHeaders m lists)
    (map : BfShape.MapConsistent m lists) (apart : InsertApart v lists)
    (headerNat : (v-8#64).toNat = v.toNat-8)
    (size : bytesT m (v-8#64).toNat 8 >>> (10 : Nat) = w) :
    let m' := writeLog m (insertLog v w m)
    BfShape.SmallShape m' (BfShape.inserted lists w.toNat v) ∧
    BfShape.SmallHeaders m' (BfShape.inserted lists w.toNat v) ∧
    BfShape.MapConsistent m' (BfShape.inserted lists w.toNat v) := by
  have read := insert_readbacks (m := m) lo hi (by omega : Vsa.Sim.DlHeap.heapStart ≤ v.toNat)
  have frame : ∀ a n, OutWRange (writeWindows v w) a n →
      bytesT (writeLog m (insertLog v w m)) a n = bytesT m a n :=
    fun a n h => bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (insertLog_inside v w m) h)
  have oldHeaders := headers.congr (fun t lt ht x hx => frame _ _
    (writeWindows_out_heap hi (apart.headers t lt ht x hx).1 (apart.headers t lt ht x hx).2))
  refine ⟨shape.push ?_ window (by omega) ?_ ?_ ?_ ?_,oldHeaders.push ?_,map.set lo hi read.bits⟩
  · intro eq
    rw [eq] at heap
    simp only [BitVec.toNat_ofNat,Vsa.Sim.DlHeap.heapStart] at heap
    omega
  · simpa only [← slot_eq] using read.head
  · simpa only [head,slot_eq] using read.link
  · intro t lt ht ne
    apply frame
    have hs := slot_nat hi
    have hm := merge_nat hi
    have ht' := BfShape.slot_toNat t ht
    simp only [Layout.bf_small_count] at ht
    simp only [writeWindows,OutWRange]
    rw [ht',hs,hm]
    simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz,
      Layout.sym_bf_small_fl,Layout.sym_bf_small_map] at heap ⊢
    refine ⟨by omega,by omega,?_,by omega,by omega,True.intro⟩
    by_cases h : t < w.toNat <;> omega
  · intro t lt ht x hx
    exact frame _ _ (writeWindows_out_heap hi (shape.heap t lt ht x hx) (apart.links t lt ht x hx))
  · rw [frame _ _ (writeWindows_out_heap hi (by rw [headerNat]; omega)
      (by rw [headerNat]; exact Or.inl (by omega))),size]
    simp

/-- The wrapper's final list family retains zero-word and sweep deferral. -/
def finalLists (v : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (lists : Nat → List (BitVec 64)) : Nat → List (BitVec 64) :=
  if Inserts v m then BfShape.inserted lists (size v m).toNat v else lists


/-- Memory form of the wrapper rule, using its exact branch-dependent log. -/
theorem effect_representation {v m lists}
    (small : (size v m).toNat ≤ 16)
    (heap : Vsa.Sim.DlHeap.heapStart + 8 ≤ v.toNat) (window : ReadWindow v 8)
    (shape : BfShape.SmallShape m lists) (headers : BfShape.SmallHeaders m lists)
    (map : BfShape.MapConsistent m lists) (apart : InsertApart v lists)
    (headerNat : (v-8#64).toNat = v.toNat-8) :
    BfShape.SmallShape (writeLog m (effect v m)) (finalLists v m lists) ∧
    BfShape.SmallHeaders (writeLog m (effect v m)) (finalLists v m lists) ∧
    BfShape.MapConsistent (writeLog m (effect v m)) (finalLists v m lists) := by
  unfold finalLists effect
  by_cases ins : Inserts v m
  · rw [if_pos ins,if_pos ins]
    have positive : 1 ≤ (size v m).toNat := by
      have nz : (size v m).toNat ≠ 0 := by
        intro h
        apply ins.1
        apply BitVec.eq_of_toNat_eq
        simpa using h
      omega
    exact insert_representation positive small heap window shape headers map apart headerNat rfl
  · rw [if_neg ins,if_neg ins]
    exact ⟨shape,headers,map⟩

/-- All wrapper branches preserve representation in the actual returned memory. -/
theorem Post.representation {ra v before after lists} (post : Post ra v before after)
    (small : (size v before.σ.mem).toNat ≤ 16)
    (heap : Vsa.Sim.DlHeap.heapStart + 8 ≤ v.toNat) (window : ReadWindow v 8)
    (shape : BfShape.SmallShape before.σ.mem lists)
    (headers : BfShape.SmallHeaders before.σ.mem lists)
    (map : BfShape.MapConsistent before.σ.mem lists) (apart : InsertApart v lists)
    (headerNat : (v-8#64).toNat = v.toNat-8) :
    BfShape.SmallShape after.σ.mem (finalLists v before.σ.mem lists) ∧
    BfShape.SmallHeaders after.σ.mem (finalLists v before.σ.mem lists) ∧
    BfShape.MapConsistent after.σ.mem (finalLists v before.σ.mem lists) := by
  rw [post.memory]
  exact effect_representation small heap window shape headers map apart headerNat

end OCaml.Vm.Gc.BestFitRemnant
