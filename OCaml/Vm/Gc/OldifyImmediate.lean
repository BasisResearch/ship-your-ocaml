import OCaml.Vm.Gc.Generated.Immediate
import OCaml.Vm.Gc.OldifySaved
import OCaml.Vm.Gc.OldifyReturned

/-! # `caml_oldify_one` on an immediate value

The entry's parity branch is taken: the prologue saves `s0`, `s1`, `ra`, the
root store `*p = v` follows, and the three words are restored before `ret`
(blocks `0x80009a70` taken and `0x80009b80`, `Immediate.blocks`). The whole
call is `OldifyReturned` with the root holding the value. -/
namespace OCaml.Vm.Gc.OldifyImmediate
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def head : BBlock := caml_oldify_oneX9a70TSeg.getD 0 {body := [], term := none}
def ret : BBlock := caml_oldify_oneX9b80Seg.getD 0 {body := [], term := none}
def blocks := [head, ret]

theorem blocks_eq : Immediate.blocks = blocks := rfl

theorem chain_ok : ChainOK OldifyEntry.pc OldifyEntry.entryKeys blocks := by decide

theorem code_facts {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_oldify_oneLoaded mem) :
    ChainCode mem blocks := by
  intro b hb
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  all_goals constructor
  all_goals simp only [head, ret, caml_oldify_oneX9a70TSeg, caml_oldify_oneX9b80Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_oldify_one_at_"

theorem head_body : head.body = OldifyEntry.headBlock.body := rfl

/-- The registers at `0x80009b80`, with the frame pointer as a variable
(`afterHead R = regsAt (frameSp R) R`). -/
def regsAt (sp : BitVec 64) (R : Nat → BitVec 64) : GRegs :=
  [(9,R 11),(8,R 10),(15,R 10 &&& 1#64),(2,sp),
   (1,R 1),(10,R 10),(11,R 11),(18,R 18),(19,R 19),(20,R 20),
   (21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

theorem afterHead_eq (R : Nat → BitVec 64) : OldifyEntry.afterHead R = regsAt (OldifyEntry.frameSp R) R := rfl

/-- The memory after the three saves. -/
def saved (R : Nat → BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog m (OldifyEntry.saveLog OldifyEntry.headSlots R)

/-- The epilogue's loads: `ra`, `s0`, `s1` from the saved slots. -/
def loadsAt (sp : BitVec 64) (mm : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 mm (sp + 104#64).toNat, read8 mm (sp + 96#64).toNat, read8 mm (sp + 88#64).toNat]

def loads (R : Nat → BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  loadsAt (OldifyEntry.frameSp R) (saved R m)

/-- The root store. -/
def effect (R : Nat → BitVec 64) : List WEntry := [((R 11).toNat, 8, R 10)]

theorem ret_log (sp : BitVec 64) (R : Nat → BitVec 64) (l1 l2 l3 : List (BitVec 8)) :
    wlogM ret.body (regsAt sp R) [l1, l2, l3] = effect R := by
  simp [ret, caml_oldify_oneX9b80Seg, regsAt, effect,
    wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

/-- The registers after the epilogue: `sp` popped, `s1`, `s0`, `ra` reloaded. -/
def restored (sp : BitVec 64) (R : Nat → BitVec 64) (l1 l2 l3 : List (BitVec 8)) : GRegs :=
  [(2, sp + 112#64), (9, bytesVal .ld l3), (8, bytesVal .ld l2), (1, bytesVal .ld l1),
   (15, R 10 &&& 1#64), (10, R 10), (11, R 11), (18, R 18), (19, R 19), (20, R 20),
   (21, R 21), (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

theorem ret_regs (sp : BitVec 64) (R : Nat → BitVec 64) (l1 l2 l3 : List (BitVec 8)) :
    runGM ret.body (regsAt sp R) [l1, l2, l3] = restored sp R l1 l2 l3 := by
  simp [ret, caml_oldify_oneX9b80Seg, regsAt, restored,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

/-- The epilogue's scalar accesses: the root store, then the three reloads,
which miss the root window. -/
theorem ret_access (sp : BitVec 64) (R : Nat → BitVec 64) (mm : Std.ExtHashMap Nat (BitVec 8))
    (windows : ∀ off ∈ [104, 96, 88], ReadWindow (sp + BitVec.ofNat 64 off) 8)
    (destination : WriteWindow (R 11) 8)
    (outside : ∀ off ∈ [104, 96, 88], OutLRange (effect R) (sp + BitVec.ofNat 64 off).toNat 8) :
    AccessPlan mm (regsAt sp R) (loadsAt sp mm) ret.body := by
  simp only [ret, caml_oldify_oneX9b80Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply destination.sd rfl
    simp [regsAt, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · apply (windows 104 (by decide)).ld rfl rfl
    simpa [stepMemM, wentryM, widthOfM, stepLdsM, eaddrM, mkLine, decodeM, regsAt,
      loadsAt, srcVal, lookupG, stepGM, wvalM, eraseG, effect, writeLog,
      Functions.sign_extend, Sail.BitVec.signExtend] using
      lpins8_writeLog (read8_pins mm (sp + 104#64).toNat) (outside 104 (by decide))
  · apply (windows 96 (by decide)).ld rfl rfl
    simpa [stepMemM, wentryM, widthOfM, stepLdsM, eaddrM, mkLine, decodeM, regsAt,
      loadsAt, srcVal, lookupG, stepGM, wvalM, eraseG, effect, writeLog,
      Functions.sign_extend, Sail.BitVec.signExtend] using
      lpins8_writeLog (read8_pins mm (sp + 96#64).toNat) (outside 96 (by decide))
  · apply (windows 88 (by decide)).ld rfl rfl
    simpa [stepMemM, wentryM, widthOfM, stepLdsM, eaddrM, mkLine, decodeM, regsAt,
      loadsAt, srcVal, lookupG, stepGM, wvalM, eraseG, effect, writeLog,
      Functions.sign_extend, Sail.BitVec.signExtend] using
      lpins8_writeLog (read8_pins mm (sp + 88#64).toNat) (outside 88 (by decide))

theorem ret_control (sp : BitVec 64) (R : Nat → BitVec 64) (l1 l2 l3 : List (BitVec 8))
    (aligned : (bytesVal .ld l1).toNat % 4 = 0) :
    TermFactsO (runGM ret.body (regsAt sp R) [l1, l2, l3]) ret.term := by
  rw [ret_regs]
  exact return_facts _ rfl rfl rfl rfl aligned

/-! The head block has no loads, so its facts hold for any load list. -/

theorem head_regsL (R : Nat → BitVec 64) (lds : List (List (BitVec 8))) :
    runGM head.body (OldifyEntry.regs R) lds = OldifyEntry.afterHead R := by
  change [(9,R 11 + 0),(8,R 10 + 0),(15,R 10 &&& 1#64),(2,OldifyEntry.frameSp R),
    (1,R 1),(10,R 10),(11,R 11),(18,R 18),(19,R 19),(20,R 20),
    (21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)] = _
  have zero (x : BitVec 64) : x + 0 = x := BitVec.add_zero x
  simp only [zero, OldifyEntry.afterHead]

theorem head_logL (R : Nat → BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM head.body (OldifyEntry.regs R) lds = OldifyEntry.saveLog OldifyEntry.headSlots R := rfl

theorem head_ldsL (lds : List (List (BitVec 8))) : ldsRunM head.body lds = lds := rfl

theorem head_accessL (R : Nat → BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8)) (lds : List (List (BitVec 8)))
    (windows : ∀ cell ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8) :
    AccessPlan mem (OldifyEntry.regs R) lds head.body := by
  simp only [head, caml_oldify_oneX9a70TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact (windows (8, 96) (by decide)).sd rfl rfl
  · exact (windows (9, 88) (by decide)).sd rfl rfl
  · exact (windows (1, 104) (by decide)).sd rfl rfl

theorem head_controlL (R : Nat → BitVec 64) (lds : List (List (BitVec 8))) (odd : (R 10).toNat % 2 = 1) :
    TermFactsO (runGM head.body (OldifyEntry.regs R) lds) head.term := by
  rw [head_regsL]
  have bit : R 10 &&& 1#64 = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_and] using odd
  simp [head, caml_oldify_oneX9a70TSeg, TermFactsO, TermFactsT,
    OldifyEntry.afterHead, srcVal, lookupG, bit, guardB]

/-- The immediate call's input: entry pins, the native save windows, an odd
argument, a writable root apart from the three reloaded slots, an aligned
return address. -/
structure Input (R : Nat → BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (OldifyEntry.regs R)
  windows : ∀ cell ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  odd : (R 10).toNat % 2 = 1
  rootWrite : WriteWindow (R 11) 8
  rootOutside : ∀ off ∈ [104, 96, 88],
    (R 11).toNat + 8 ≤ (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat ∨
      (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat + 8 ≤ (R 11).toNat
  aligned : (R 1).toNat % 4 = 0

/-- The call's memory effect: three saves, then the root store. -/
def callEffect (R : Nat → BitVec 64) : List WEntry :=
  OldifyEntry.saveLog OldifyEntry.headSlots R ++ effect R

structure Post (R : Nat → BitVec 64) (before after : Config) : Prop
    extends OldifyReturned R (callEffect R) before after where
  root : word after (R 11).toNat = R 10

def headShape : SaveBank.Shape OldifyEntry.headSlots :=
  ⟨(1, 104), by decide, by decide, by decide, by decide⟩

theorem head_windows {R : Nat → BitVec 64}
    (windows : ∀ cell ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8) :
    ∀ cell ∈ OldifyEntry.headSlots, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8 :=
  fun cell member => windows cell (List.mem_append_left _ member)

/-- The three saved words read back after the saves. -/
theorem saved_word {R : Nat → BitVec 64} (m : Std.ExtHashMap Nat (BitVec 8))
    (windows : ∀ cell ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8)
    (cell : Nat × Nat) (member : cell ∈ OldifyEntry.headSlots) :
    bytesT (saved R m) (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8 = R cell.1 :=
  headShape.read m (OldifyEntry.frameSp R) R (head_windows windows) cell member

theorem stack_restored (R : Nat → BitVec 64) : OldifyEntry.frameSp R + 112#64 = R 2 := by
  simp only [OldifyEntry.frameSp, OldifyReturn.frameSize, BitVec.add_neg_eq_sub, BitVec.sub_add_cancel]

/-- **`caml_oldify_one` on an immediate value**, entry to return. -/
theorem call {R c} (input : Input R c) : FnSummary OldifyEntry.pc (fun d => d = c) (Post R c) := by
  have w104 := saved_word c.σ.mem input.windows (1, 104) (by decide)
  have w96 := saved_word c.σ.mem input.windows (8, 96) (by decide)
  have w88 := saved_word c.σ.mem input.windows (9, 88) (by decide)
  simp only [] at w104 w96 w88
  have l1 : bytesVal .ld (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 104#64).toNat) = R 1 := by
    rw [read8_value]; exact w104
  have l2 : bytesVal .ld (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 96#64).toNat) = R 8 := by
    rw [read8_value]; exact w96
  have l3 : bytesVal .ld (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 88#64).toNat) = R 9 := by
    rw [read8_value]; exact w88
  have aligned : (bytesVal .ld (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 104#64).toNat)).toNat % 4 = 0 := by
    rw [l1]; exact input.aligned
  have rwin : ∀ off ∈ [104, 96, 88], ReadWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 off) 8 := by
    intro off member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact (input.windows (1, 104) (by decide)).read
    · exact (input.windows (8, 96) (by decide)).read
    · exact (input.windows (9, 88) (by decide)).read
  have outside : ∀ off ∈ [104, 96, 88], OutLRange (effect R) (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat 8 :=
    fun off member => ⟨Or.symm (input.rootOutside off member), True.intro⟩
  have access : ChainAccess c.σ.mem (OldifyEntry.regs R) (loads R c.σ.mem) blocks := by
    apply ChainAccess.cons ⟨head_accessL R c.σ.mem _ input.windows, head_controlL R _ input.odd⟩
    rw [head_logL, head_regsL, head_ldsL, afterHead_eq]
    exact ChainAccess.cons ⟨ret_access _ R (saved R c.σ.mem) rwin input.rootWrite outside,
      ret_control _ R _ _ _ aligned⟩ ChainAccess.nil
  have facts := chainPlan_facts (code_facts input.code) access
  have summary := block_summary blocks OldifyEntry.pc (OldifyEntry.regs R) (loads R c.σ.mem) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK OldifyEntry.entryKeys; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have log : (evalBlocks blocks (SegEvalState.init (OldifyEntry.regs R) (loads R c.σ.mem))).log = callEffect R := by
    simp only [blocks, evalBlocks, evalBlock, SegEvalState.init, head_logL, head_regsL, head_ldsL, afterHead_eq]
    rw [show loads R c.σ.mem = [_, _, _] from rfl, ret_log]
    rfl
  have regs : (evalBlocks blocks (SegEvalState.init (OldifyEntry.regs R) (loads R c.σ.mem))).regs =
      restored (OldifyEntry.frameSp R) R
        (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 104#64).toNat)
        (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 96#64).toNat)
        (read8 (saved R c.σ.mem) (OldifyEntry.frameSp R + 88#64).toNat) := by
    simp only [blocks, evalBlocks, evalBlock, SegEvalState.init, head_regsL, head_ldsL, afterHead_eq]
    rw [show loads R c.σ.mem = [_, _, _] from rfl, ret_regs]
  have endpoint : evalBlocksPC OldifyEntry.pc (SegEvalState.init (OldifyEntry.regs R) (loads R c.σ.mem)) blocks = R 1 := by
    simp only [blocks, evalBlocksPC, SegEvalState.init, chainEndPC, evalBlock, head_regsL, head_ldsL, afterHead_eq]
    rw [show loads R c.σ.mem = [_, _, _] from rfl]
    change Sail.BitVec.update (srcVal 1 (runGM ret.body (regsAt _ R) [_, _, _]) + 0#64) 0 0#1 = _
    rw [ret_regs]
    change Sail.BitVec.update (bytesVal .ld _ + 0#64) 0 0#1 = _
    rw [l1]
    exact ret_tgt _ input.aligned
  have memory : after.σ.mem = writeLog c.σ.mem (callEffect R) := by rw [post.memory, log]
  refine ⟨⟨post.good, post.minstret, post.tick, ?_, ?_, ?_, memory, post.output, ?_⟩, ?_⟩
  · exact image_after Code.caml_oldify_one_transport (by decide) input.code facts post
  · rw [PCAt, post.pc, endpoint]
  · have holds := post.regs
    rw [regs] at holds
    apply gholds_select holds
    intro n v member
    simp only [OldifyEntry.callerRegs, OldifyReturn.slots, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [restored, lookupG, l1, l2, l3, stack_restored, -BitVec.toNat_add]
  · intro r noise gprs
    exact post.frame r noise fun n hn => gprs n (by
      have small : ∀ n ∈ wrChain blocks, n < 32 := by decide
      exact small n hn)
  · rw [word, memory, callEffect, writeLog_append]
    exact word_writeLog_at _ _ 0 _ _ rfl True.intro

end OCaml.Vm.Gc.OldifyImmediate
