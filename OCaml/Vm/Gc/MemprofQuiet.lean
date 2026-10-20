import OCaml.Vm.Gc.Generated.MemprofYoungRoots
import OCaml.Vm.Gc.Generated.MemprofIterDefault
import OCaml.Vm.Gc.Generated.MemprofCallOnArray
import OCaml.Vm.Gc.Generated.MemprofEntryArray
import OCaml.Vm.Gc.ChainPlan
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.SaveBank
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.StackArithmetic
import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Primitives.Control
import OCaml.Vm.Primitives.IndirectCall
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.SymbolicAppend
import Vsa.Sim.GRegsFrame
import Vsa.Sim.ChainFactsTac

/-! # `caml_memprof_oldify_young_roots` with no tracked young block

With memprof idle (`entries_global` has `young_idx ≥ len`, the thread-context
hook is the default one, and the main context's entry array is likewise
empty) the call saves its frame, skips its loop, calls the hook
`th_ctx_iter_default`, which tail-jumps to `call_on_entry_array` and then to
`entry_array_oldify_young_roots` on the main context; that skips its loop and
returns, and the caller restores and returns.

Pieces: the head (`0x80029094` taken, `0x80029100`), the hook's `jalr`, the
two tail-jumping blocks, the entry array (`0x80028b44` taken, `0x80028ba0`),
the return (`0x80029118`). Both frames are one save bank over the lower frame
pointer `low = sp − 80`. -/
namespace OCaml.Vm.Gc.MemprofQuiet
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def headBlock : BBlock := caml_memprof_oldify_young_rootsX9094TSeg.getD 0 {body := [], term := none}
def hookBlock : BBlock := caml_memprof_oldify_young_rootsX9100Seg.getD 0 {body := [], term := none}
def retBlock : BBlock := caml_memprof_oldify_young_rootsX9118Seg.getD 0 {body := [], term := none}
def iterBlock : BBlock := th_ctx_iter_defaultX89bcSeg.getD 0 {body := [], term := none}
def onArrayBlock : BBlock := call_on_entry_arrayX882cSeg.getD 0 {body := [], term := none}
def arrayBlock : BBlock := entry_array_oldify_young_rootsX8b44TSeg.getD 0 {body := [], term := none}
def arrayRetBlock : BBlock := entry_array_oldify_young_rootsX8ba0Seg.getD 0 {body := [], term := none}

def pc : BitVec 64 := 0x80029094#64
def callPc : BitVec 64 := 0x80029114#64
def retPc : BitVec 64 := 0x80029118#64
def iterPc : BitVec 64 := 0x800289bc#64
def onArrayPc : BitVec 64 := 0x8002882c#64
def arrayPc : BitVec 64 := 0x80028b44#64

/-- `entries_global`: its `len` at `+24`, `young_idx` at `+32`. -/
def globals : BitVec 64 := 0x80063b20#64
def hookAddr : Nat := 0x800648d0
def localAddr : Nat := 0x800648d8

/-- The caller's frame pointer and the entry array's below it. -/
def frame (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551568#64
def low (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551536#64

/-! ## The head: saves, the `entries_global` test, the hook load -/

def regs (sp s1 s2 ra : BitVec 64) : GRegs := [(2, sp), (18, s2), (1, ra), (9, s1)]

def afterHead (fsp ra : BitVec 64) (l1 l2 : List (BitVec 8)) : GRegs :=
  [(14, arrayPc), (15, bytesVal .ld l2), (9, bytesVal .ld l1), (18, globals), (2, fsp), (1, ra)]

def atCall (fsp ra : BitVec 64) (l1 l3 : List (BitVec 8)) : GRegs :=
  [(10, onArrayPc), (11, fsp), (15, bytesVal .ld l3), (14, arrayPc), (9, bytesVal .ld l1), (18, globals),
   (2, fsp), (1, ra)]

theorem head_regs (sp s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM headBlock.body (regs sp s1 s2 ra) (l1 :: l2 :: rest) = afterHead (frame sp) ra l1 l2 := by
  simp [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, regs, afterHead, frame, globals, arrayPc,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem hook_regs (fsp ra : BitVec 64) (l1 l2 l3 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM hookBlock.body (afterHead fsp ra l1 l2) (l3 :: rest) = atCall fsp ra l1 l3 := by
  simp [hookBlock, caml_memprof_oldify_young_rootsX9100Seg, afterHead, atCall, globals, arrayPc, onArrayPc,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

def headLog (sp s1 s2 ra : BitVec 64) : List WEntry :=
  [((frame sp + 16#64).toNat, 8, s2), ((frame sp + 40#64).toNat, 8, ra), ((frame sp + 24#64).toNat, 8, s1),
   ((frame sp + 8#64).toNat, 8, 0#64), ((frame sp + 0#64).toNat, 8, arrayPc)]

/-- The head's first ten instructions leave the registers of the whole head
(its last two are stores). -/
theorem prefix_regs (sp s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM (headBlock.body.take 10) (regs sp s1 s2 ra) (l1 :: l2 :: rest) = afterHead (frame sp) ra l1 l2 := by
  simp [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, regs, afterHead, frame, globals, arrayPc,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem head_log (sp s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    wlogM headBlock.body (regs sp s1 s2 ra) (l1 :: l2 :: rest) = headLog sp s1 s2 ra := by
  rw [← List.take_append_drop 10 headBlock.body, wlogM_append, prefix_regs]
  rfl

theorem hook_log (fsp ra : BitVec 64) (l1 l2 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    wlogM hookBlock.body (afterHead fsp ra l1 l2) lds = [] := rfl

theorem head_lds (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    ldsRunM headBlock.body (l1 :: l2 :: rest) = rest := rfl

theorem hook_lds (l3 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    ldsRunM hookBlock.body (l3 :: rest) = rest := rfl

/-! ## The hook's two tail jumps -/

/-- An indirect `jr rs` with offset zero to an aligned target. -/
theorem jump_facts (t : TInstr) {L : GRegs} {r : Nat} {tgt : BitVec 64}
    (hk : t.kind = .jr) (hs : t.rs1 = r) (hi : t.imm12 = 0#12)
    (hr : srcVal r L = tgt) (ha : tgt.toNat % 4 = 0) : TermFactsO L (some t) := by
  simp only [TermFactsO, TermFactsT, hk, hs, hi]
  rw [hr, ret_tgt tgt ha]
  exact ha

/-- At the hook: `a0` the callback, `a1` the frame, the rest carried. -/
def atIter (fsp idx : BitVec 64) : GRegs :=
  [(10, onArrayPc), (11, fsp), (2, fsp), (1, retPc), (18, globals), (9, idx)]

def afterIter (fsp idx ctx : BitVec 64) : GRegs :=
  [(10, ctx), (15, onArrayPc), (11, fsp), (2, fsp), (1, retPc), (18, globals), (9, idx)]

theorem iter_regs (fsp idx : BitVec 64) (l : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM iterBlock.body (atIter fsp idx) (l :: rest) = afterIter fsp idx (bytesVal .ld l) := by
  simp [iterBlock, th_ctx_iter_defaultX89bcSeg, atIter, afterIter,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem iter_log (fsp idx : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM iterBlock.body (atIter fsp idx) lds = [] := rfl

def afterOnArray (fsp idx ctx : BitVec 64) (l l' : List (BitVec 8)) : GRegs :=
  [(10, ctx + 16#64), (11, bytesVal .ld l'), (15, bytesVal .ld l), (2, fsp), (1, retPc), (18, globals), (9, idx)]

theorem onArray_regs (fsp idx ctx : BitVec 64) (l l' : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM onArrayBlock.body (afterIter fsp idx ctx) (l :: l' :: rest) = afterOnArray fsp idx ctx l l' := by
  simp [onArrayBlock, call_on_entry_arrayX882cSeg, afterIter, afterOnArray,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem onArray_log (fsp idx ctx : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM onArrayBlock.body (afterIter fsp idx ctx) lds = [] := rfl

/-! ## The main context's entry array -/

def atArray (fsp idx arr : BitVec 64) : GRegs := [(2, fsp), (1, retPc), (9, idx), (10, arr)]

def afterArray (fsp arr : BitVec 64) (l l' : List (BitVec 8)) : GRegs :=
  [(15, bytesVal .ld l'), (9, bytesVal .ld l), (2, fsp + 18446744073709551584#64), (1, retPc), (10, arr)]

theorem array_regs (fsp idx arr : BitVec 64) (l l' : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM arrayBlock.body (atArray fsp idx arr) (l :: l' :: rest) = afterArray fsp arr l l' := by
  simp [arrayBlock, entry_array_oldify_young_rootsX8b44TSeg, atArray, afterArray,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

def arrayLog (fsp idx : BitVec 64) : List WEntry :=
  [((fsp + 18446744073709551584#64 + 24#64).toNat, 8, retPc), ((fsp + 18446744073709551584#64 + 8#64).toNat, 8, idx)]

theorem array_log (fsp idx arr : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM arrayBlock.body (atArray fsp idx arr) lds = arrayLog fsp idx := rfl

def afterArrayRet (fsp arr : BitVec 64) (l' r1 r2 : List (BitVec 8)) : GRegs :=
  [(2, fsp + 18446744073709551584#64 + 32#64), (9, bytesVal .ld r2), (1, bytesVal .ld r1), (15, bytesVal .ld l'),
   (10, arr)]

theorem arrayRet_regs (fsp arr : BitVec 64) (l l' r1 r2 : List (BitVec 8)) :
    runGM arrayRetBlock.body (afterArray fsp arr l l') [r1, r2] = afterArrayRet fsp arr l' r1 r2 := by
  simp [arrayRetBlock, entry_array_oldify_young_rootsX8ba0Seg, afterArray, afterArrayRet,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem arrayRet_log (fsp arr : BitVec 64) (l l' : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    wlogM arrayRetBlock.body (afterArray fsp arr l l') lds = [] := rfl

/-! ## The caller's return -/

def restored (fsp : BitVec 64) (r1 r2 r3 : List (BitVec 8)) : GRegs :=
  [(2, fsp + 48#64), (18, bytesVal .ld r3), (9, bytesVal .ld r2), (1, bytesVal .ld r1)]

theorem ret_regs (fsp : BitVec 64) (r1 r2 r3 : List (BitVec 8)) :
    runGM retBlock.body [(2, fsp)] [r1, r2, r3] = restored fsp r1 r2 r3 := by
  simp [retBlock, caml_memprof_oldify_young_rootsX9118Seg, restored,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem ret_log (fsp : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM retBlock.body [(2, fsp)] lds = [] := rfl

/-! ## One save bank over `low` -/

/-- Re-associate a stack address between two frame bases. -/
theorem shift (sp a b c d : BitVec 64) (h : a + b = c + d) : sp + a + b = sp + c + d := by
  rw [BitVec.add_assoc, h, ← BitVec.add_assoc]

theorem frame_add (sp : BitVec 64) (k : Nat) :
    frame sp + BitVec.ofNat 64 k = low sp + BitVec.ofNat 64 (k + 32) := by
  apply shift
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem array_frame (sp : BitVec 64) : frame sp + 18446744073709551584#64 = low sp := by
  rw [frame, low, BitVec.add_assoc]
  rfl

/-- The saved words, keyed by cell (registers for the caller's saves, `0` for
the zero word, `14` for the callback, `101`/`109` for the entry array's). -/
def bankR (s1 s2 ra idx : BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 18 then s2 else if n = 1 then ra else if n = 9 then s1 else if n = 14 then arrayPc
  else if n = 101 then retPc else if n = 109 then idx else 0#64

def headSlots : List (Nat × Nat) := [(18, 48), (1, 72), (9, 56), (0, 40), (14, 32)]
def arraySlots : List (Nat × Nat) := [(101, 24), (109, 8)]
def bankSlots : List (Nat × Nat) := headSlots ++ arraySlots

def headShape : SaveBank.Shape headSlots := ⟨(1, 72), by decide, by decide, by decide, by decide⟩
def arrayShape : SaveBank.Shape arraySlots := ⟨(101, 24), by decide, by decide, by decide, by decide⟩
def bankShape : SaveBank.Shape bankSlots := ⟨(1, 72), by decide, by decide, by decide, by decide⟩

theorem headLog_bank (sp s1 s2 ra idx : BitVec 64) :
    headLog sp s1 s2 ra = SaveBank.log (low sp) (bankR s1 s2 ra idx) headSlots := by
  simp only [headLog, SaveBank.log, headSlots, List.map_cons, List.map_nil]
  rw [frame_add sp 16, frame_add sp 40, frame_add sp 24,
    frame_add sp 8, show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, frame_add sp 0]
  rfl

theorem arrayLog_bank (sp s1 s2 ra idx : BitVec 64) :
    arrayLog (frame sp) idx = SaveBank.log (low sp) (bankR s1 s2 ra idx) arraySlots := by
  simp only [arrayLog, SaveBank.log, arraySlots, List.map_cons, List.map_nil, array_frame]
  rfl

/-- The head's store windows, from the bank's. -/
theorem head_windows {sp : BitVec 64} (saves : ∀ cell ∈ bankSlots, WriteWindow (low sp + BitVec.ofNat 64 cell.2) 8) :
    ∀ off ∈ [16, 40, 24, 8, 0], WriteWindow (frame sp + BitVec.ofNat 64 off) 8 := by
  intro off member
  rw [frame_add]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact saves (18, 48) (by decide)
  · exact saves (1, 72) (by decide)
  · exact saves (9, 56) (by decide)
  · exact saves (0, 40) (by decide)
  · exact saves (14, 32) (by decide)

/-! ## Access plans and branches -/

theorem outLRange_take : ∀ (log : List WEntry) (n a w : Nat), OutLRange log a w → OutLRange (log.take n) a w
  | [], _, _, _, _ => by simp [OutLRange]
  | _ :: _, 0, _, _, _ => trivial
  | _ :: log, n + 1, a, w, ⟨h, t⟩ => ⟨h, outLRange_take log n a w t⟩

theorem prefix6_regs (sp s1 s2 ra : BitVec 64) (lds : List (List (BitVec 8))) :
    runGM (headBlock.body.take 6) (regs sp s1 s2 ra) lds = [(18, globals), (2, frame sp), (1, ra), (9, s1)] := by
  simp [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, regs, frame, globals,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem prefix7_regs (sp s1 s2 ra : BitVec 64) (l1 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM (headBlock.body.take 7) (regs sp s1 s2 ra) (l1 :: rest) =
      [(9, bytesVal .ld l1), (18, globals), (2, frame sp), (1, ra)] := by
  simp [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, regs, frame, globals,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem prefix11_regs (sp s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM (headBlock.body.take 11) (regs sp s1 s2 ra) (l1 :: l2 :: rest) = afterHead (frame sp) ra l1 l2 := by
  simp [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, regs, afterHead, frame, globals, arrayPc,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem head_access (sp s1 s2 ra : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (rest : List (List (BitVec 8)))
    (windows : ∀ off ∈ [16, 40, 24, 8, 0], WriteWindow (frame sp + BitVec.ofNat 64 off) 8)
    (r40 : ReadWindow 0x80063b40#64 8) (r38 : ReadWindow 0x80063b38#64 8)
    (out40 : OutLRange (headLog sp s1 s2 ra) 0x80063b40 8)
    (out38 : OutLRange (headLog sp s1 s2 ra) 0x80063b38 8) :
    AccessPlan m (regs sp s1 s2 ra) (read8 m 0x80063b40 :: read8 m 0x80063b38 :: rest) headBlock.body := by
  simp only [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact (windows 16 (by decide)).sd rfl rfl
  · exact (windows 40 (by decide)).sd rfl rfl
  · exact (windows 24 (by decide)).sd rfl rfl
  · refine r40.ld rfl ?_ ?_
    · change eaddrM _ (runGM (headBlock.body.take 6) (regs sp s1 s2 ra) _) = _
      rw [prefix6_regs]
      simp [globals, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
    · change LPins8 (memAfter m (headBlock.body.take 6) (regs sp s1 s2 ra) _) _ _
      rw [memAfter_eq, show wlogM (headBlock.body.take 6) (regs sp s1 s2 ra)
        (read8 m 0x80063b40 :: read8 m 0x80063b38 :: rest) = (headLog sp s1 s2 ra).take 3 from rfl]
      exact lpins8_writeLog (read8_pins m 0x80063b40) (outLRange_take _ 3 _ _ out40)
  · refine r38.ld rfl ?_ ?_
    · change eaddrM _ (runGM (headBlock.body.take 7) (regs sp s1 s2 ra) (_ :: rest)) = _
      rw [prefix7_regs]
      simp [globals, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
    · change LPins8 (memAfter m (headBlock.body.take 7) (regs sp s1 s2 ra) _) _ _
      rw [memAfter_eq, show wlogM (headBlock.body.take 7) (regs sp s1 s2 ra)
        (read8 m 0x80063b40 :: read8 m 0x80063b38 :: rest) = (headLog sp s1 s2 ra).take 3 from rfl]
      exact lpins8_writeLog (read8_pins m 0x80063b38) (outLRange_take _ 3 _ _ out38)
  · refine (windows 8 (by decide)).sd rfl ?_
    change eaddrM _ (runGM (headBlock.body.take 10) (regs sp s1 s2 ra) (_ :: _ :: rest)) = _
    rw [prefix_regs]
    simp [afterHead, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · refine (windows 0 (by decide)).sd rfl ?_
    change eaddrM _ (runGM (headBlock.body.take 11) (regs sp s1 s2 ra) (_ :: _ :: rest)) = _
    rw [prefix11_regs]
    simp [afterHead, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]

theorem head_control (sp s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (quiet : (bytesVal .ld l2).toNat ≤ (bytesVal .ld l1).toNat) :
    TermFactsO (runGM headBlock.body (regs sp s1 s2 ra) (l1 :: l2 :: rest)) headBlock.term := by
  rw [head_regs]
  simpa [headBlock, caml_memprof_oldify_young_rootsX9094TSeg, TermFactsO, TermFactsT, afterHead, srcVal, lookupG,
    guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt] using quiet

theorem hook_access (fsp ra : BitVec 64) (l1 l2 : List (BitVec 8)) (m : Std.ExtHashMap Nat (BitVec 8))
    (rest : List (List (BitVec 8))) (window : ReadWindow 0x800648d0#64 8) :
    AccessPlan m (afterHead fsp ra l1 l2) (read8 m hookAddr :: rest) hookBlock.body := by
  simp only [hookBlock, caml_memprof_oldify_young_rootsX9100Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  refine window.ld rfl ?_ (read8_pins _ _)
  simp [afterHead, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

def headBlocks : List BBlock := [headBlock, hookBlock]

theorem head_chain_ok : ChainOK pc [2, 18, 1, 9] headBlocks := by decide

theorem head_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_memprof_oldify_young_rootsLoaded mem) :
    ChainCode mem (headBlocks ++ [retBlock]) := by
  intro b hb
  simp only [headBlocks, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [headBlock, hookBlock, retBlock, caml_memprof_oldify_young_rootsX9094TSeg,
    caml_memprof_oldify_young_rootsX9100Seg, caml_memprof_oldify_young_rootsX9118Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_memprof_oldify_young_roots_at_"

def headLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp s1 s2 ra : BitVec 64) : List (List (BitVec 8)) :=
  [read8 m 0x80063b40, read8 m 0x80063b38, read8 (writeLog m (headLog sp s1 s2 ra)) hookAddr]

theorem head_eval_regs (m : Std.ExtHashMap Nat (BitVec 8)) (sp s1 s2 ra : BitVec 64) :
    (evalBlocks headBlocks (SegEvalState.init (regs sp s1 s2 ra) (headLoads m sp s1 s2 ra))).regs =
      atCall (frame sp) ra (read8 m 0x80063b40) (read8 (writeLog m (headLog sp s1 s2 ra)) hookAddr) := by
  simp only [headBlocks, evalBlocks, evalBlock, SegEvalState.init, headLoads, head_regs, head_lds, hook_regs]

theorem head_eval_log (m : Std.ExtHashMap Nat (BitVec 8)) (sp s1 s2 ra : BitVec 64) :
    (evalBlocks headBlocks (SegEvalState.init (regs sp s1 s2 ra) (headLoads m sp s1 s2 ra))).log =
      headLog sp s1 s2 ra := by
  simp only [headBlocks, evalBlocks, evalBlock, SegEvalState.init, headLoads, head_regs, head_lds, head_log,
    hook_log, List.append_nil, List.nil_append]

theorem head_eval_pc (m : Std.ExtHashMap Nat (BitVec 8)) (sp s1 s2 ra : BitVec 64) :
    evalBlocksPC pc (SegEvalState.init (regs sp s1 s2 ra) (headLoads m sp s1 s2 ra)) headBlocks = callPc := rfl

/-! ## The tail jumps, the entry array and the return: access, branches, evaluation -/

theorem iter_access (fsp idx : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (rest : List (List (BitVec 8)))
    (window : ReadWindow 0x800648d8#64 8) :
    AccessPlan m (atIter fsp idx) (read8 m localAddr :: rest) iterBlock.body := by
  simp only [iterBlock, th_ctx_iter_defaultX89bcSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  refine window.ld rfl ?_ (read8_pins _ _)
  simp [atIter, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem iter_control (fsp idx : BitVec 64) (l : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    TermFactsO (runGM iterBlock.body (atIter fsp idx) (l :: rest)) iterBlock.term := by
  rw [iter_regs]
  exact jump_facts (tgt := onArrayPc) _ rfl rfl rfl rfl (by decide)

theorem iter_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Th_ctx_iter_defaultLoaded mem) :
    ChainCode mem [iterBlock] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  constructor
  all_goals simp only [iterBlock, th_ctx_iter_defaultX89bcSeg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.th_ctx_iter_default_at_"

theorem iter_chain_ok : ChainOK iterPc [10, 11, 2, 1, 18, 9] [iterBlock] := by decide

theorem iter_eval_pc (fsp idx : BitVec 64) (l : List (BitVec 8)) :
    evalBlocksPC iterPc (SegEvalState.init (atIter fsp idx) [l]) [iterBlock] = onArrayPc := by
  simp only [evalBlocksPC, SegEvalState.init, chainEndPC, endPCB]
  change Sail.BitVec.update (srcVal 15 (runGM iterBlock.body (atIter fsp idx) [l]) + 0#64) 0 0#1 = _
  rw [iter_regs]
  change Sail.BitVec.update (onArrayPc + 0#64) 0 0#1 = onArrayPc
  exact ret_tgt onArrayPc (by decide)

theorem onArray_access (fsp idx ctx : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (rest : List (List (BitVec 8))) (w0 : ReadWindow fsp 8) (w8 : ReadWindow (fsp + 8#64) 8) :
    AccessPlan m (afterIter fsp idx ctx) (read8 m fsp.toNat :: read8 m (fsp + 8#64).toNat :: rest)
      onArrayBlock.body := by
  simp only [onArrayBlock, call_on_entry_arrayX882cSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · refine w0.ld rfl ?_ (read8_pins _ _)
    simp [afterIter, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · refine w8.ld rfl ?_ (read8_pins _ _)
    simp [afterIter, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]

theorem onArray_control (fsp idx ctx : BitVec 64) (l l' : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (target : bytesVal .ld l = arrayPc) :
    TermFactsO (runGM onArrayBlock.body (afterIter fsp idx ctx) (l :: l' :: rest)) onArrayBlock.term := by
  rw [onArray_regs]
  exact jump_facts _ rfl rfl rfl target (by rw [arrayPc]; decide)

theorem onArray_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Call_on_entry_arrayLoaded mem) :
    ChainCode mem [onArrayBlock] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  constructor
  all_goals simp only [onArrayBlock, call_on_entry_arrayX882cSeg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.call_on_entry_array_at_"

theorem onArray_chain_ok : ChainOK onArrayPc [10, 15, 11, 2, 1, 18, 9] [onArrayBlock] := by decide

theorem onArray_eval_pc (fsp idx ctx : BitVec 64) (l l' : List (BitVec 8)) (target : bytesVal .ld l = arrayPc) :
    evalBlocksPC onArrayPc (SegEvalState.init (afterIter fsp idx ctx) [l, l']) [onArrayBlock] = arrayPc := by
  simp only [evalBlocksPC, SegEvalState.init, chainEndPC, endPCB]
  change Sail.BitVec.update (srcVal 15 (runGM onArrayBlock.body (afterIter fsp idx ctx) [l, l']) + 0#64) 0 0#1 = _
  rw [onArray_regs]
  change Sail.BitVec.update (bytesVal .ld l + 0#64) 0 0#1 = _
  rw [target]
  exact ret_tgt arrayPc (by decide)

theorem array_access (fsp idx arr : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (rest : List (List (BitVec 8)))
    (w24 : WriteWindow (fsp + 18446744073709551584#64 + 24#64) 8)
    (w8 : WriteWindow (fsp + 18446744073709551584#64 + 8#64) 8)
    (r32 : ReadWindow (arr + 32#64) 8) (r24 : ReadWindow (arr + 24#64) 8) :
    AccessPlan m (atArray fsp idx arr)
      (read8 (writeLog m (arrayLog fsp idx)) (arr + 32#64).toNat ::
        read8 (writeLog m (arrayLog fsp idx)) (arr + 24#64).toNat :: rest) arrayBlock.body := by
  simp only [arrayBlock, entry_array_oldify_young_rootsX8b44TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact w24.sd rfl rfl
  · exact w8.sd rfl rfl
  · refine r32.ld rfl rfl ?_
    change LPins8 (memAfter m (arrayBlock.body.take 3) (atArray fsp idx arr) _) _ _
    rw [memAfter_eq, show wlogM (arrayBlock.body.take 3) (atArray fsp idx arr) _ = arrayLog fsp idx from rfl]
    exact read8_pins _ _
  · refine r24.ld rfl rfl ?_
    change LPins8 (memAfter m (arrayBlock.body.take 4) (atArray fsp idx arr) _) _ _
    rw [memAfter_eq, show wlogM (arrayBlock.body.take 4) (atArray fsp idx arr) _ = arrayLog fsp idx from rfl]
    exact read8_pins _ _

theorem array_control (fsp idx arr : BitVec 64) (l l' : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (quiet : (bytesVal .ld l').toNat ≤ (bytesVal .ld l).toNat) :
    TermFactsO (runGM arrayBlock.body (atArray fsp idx arr) (l :: l' :: rest)) arrayBlock.term := by
  rw [array_regs]
  simpa [arrayBlock, entry_array_oldify_young_rootsX8b44TSeg, TermFactsO, TermFactsT, afterArray, srcVal, lookupG,
    guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt] using quiet

theorem arrayRet_access (fsp arr : BitVec 64) (l l' : List (BitVec 8)) (m : Std.ExtHashMap Nat (BitVec 8))
    (w24 : ReadWindow (fsp + 18446744073709551584#64 + 24#64) 8)
    (w8 : ReadWindow (fsp + 18446744073709551584#64 + 8#64) 8) :
    AccessPlan m (afterArray fsp arr l l')
      [read8 m (fsp + 18446744073709551584#64 + 24#64).toNat, read8 m (fsp + 18446744073709551584#64 + 8#64).toNat]
      arrayRetBlock.body := by
  simp only [arrayRetBlock, entry_array_oldify_young_rootsX8ba0Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact w24.ld rfl rfl (read8_pins _ _)
  · exact w8.ld rfl rfl (read8_pins _ _)

theorem arrayRet_control (fsp arr : BitVec 64) (l l' r1 r2 : List (BitVec 8)) (link : bytesVal .ld r1 = retPc) :
    TermFactsO (runGM arrayRetBlock.body (afterArray fsp arr l l') [r1, r2]) arrayRetBlock.term := by
  rw [arrayRet_regs]
  exact return_facts _ rfl rfl rfl link (by rw [retPc]; decide)

def arrayBlocks : List BBlock := [arrayBlock, arrayRetBlock]

theorem array_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Entry_array_oldify_young_rootsLoaded mem) :
    ChainCode mem arrayBlocks := by
  intro b hb
  simp only [arrayBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  all_goals constructor
  all_goals simp only [arrayBlock, arrayRetBlock, entry_array_oldify_young_rootsX8b44TSeg,
    entry_array_oldify_young_rootsX8ba0Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.entry_array_oldify_young_roots_at_"

theorem array_chain_ok : ChainOK arrayPc [2, 1, 9, 10] arrayBlocks := by decide

theorem ret_access (fsp : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (windows : ∀ off ∈ [40, 24, 16], ReadWindow (fsp + BitVec.ofNat 64 off) 8) :
    AccessPlan m [(2, fsp)]
      [read8 m (fsp + 40#64).toNat, read8 m (fsp + 24#64).toNat, read8 m (fsp + 16#64).toNat] retBlock.body := by
  simp only [retBlock, caml_memprof_oldify_young_rootsX9118Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact (windows 40 (by decide)).ld rfl rfl (read8_pins _ _)
  · exact (windows 24 (by decide)).ld rfl rfl (read8_pins _ _)
  · exact (windows 16 (by decide)).ld rfl rfl (read8_pins _ _)

theorem ret_control (fsp ra : BitVec 64) (r1 r2 r3 : List (BitVec 8)) (link : bytesVal .ld r1 = ra)
    (aligned : ra.toNat % 4 = 0) :
    TermFactsO (runGM retBlock.body [(2, fsp)] [r1, r2, r3]) retBlock.term := by
  rw [ret_regs]
  exact return_facts _ rfl rfl rfl link aligned

theorem ret_chain_ok : ChainOK retPc [2] [retBlock] := by decide

theorem array_lds (l l' : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    ldsRunM arrayBlock.body (l :: l' :: rest) = rest := rfl

/-! ## The hook call -/

def hookCall : IndirectCallInstr := ⟨0x80029114#64, 0x000780e7#32, 0xe7#8, 0x80#8, 0x07#8, 0x00#8, 0x000#12, 15⟩

theorem hook_shape : IndirectShape hookCall := by constructor <;> decide

theorem hook_decode : IndirectDecode hookCall := by
  intro s hm hp he
  exact Vsa.Sim.ElfDecode.decode_000780e7 s hm hp he

theorem hook_link : hookCall.link = retPc := by decide

theorem hook_target : hookCall.target iterPc = iterPc := ret_tgt iterPc (by decide)

theorem hook_pins {c : Config} (h : Code.Caml_memprof_oldify_young_rootsLoaded c.σ.mem) : IndirectPins hookCall c := by
  obtain ⟨h0, h1, h2, h3⟩ := Code.caml_memprof_oldify_young_roots_at_80029114 h
  exact ⟨h0, h1, h2, h3⟩

/-- The registers carried across the hook's `jalr`. -/
def carried (fsp idx : BitVec 64) : GRegs :=
  [(10, onArrayPc), (11, fsp), (15, iterPc), (2, fsp), (18, globals), (9, idx)]

/-! ## The code images, kept by every piece's stack stores -/

structure CodeAt (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  memprof : Code.Caml_memprof_oldify_young_rootsLoaded m
  iter : Code.Th_ctx_iter_defaultLoaded m
  onArray : Code.Call_on_entry_arrayLoaded m
  array : Code.Entry_array_oldify_young_rootsLoaded m

theorem CodeAt.after {bs entry regs loads before after} (code : CodeAt before.σ.mem)
    (facts : ChainFacts before.σ.mem before.σ.mem regs loads bs)
    (post : BlockPost bs entry regs loads before after) : CodeAt after.σ.mem :=
  ⟨image_after Code.caml_memprof_oldify_young_roots_transport (by decide) code.memprof facts post,
   image_after Code.th_ctx_iter_default_transport (by decide) code.iter facts post,
   image_after Code.call_on_entry_array_transport (by decide) code.onArray facts post,
   image_after Code.entry_array_oldify_young_roots_transport (by decide) code.array facts post⟩

/-! ## Reading through the save bank -/

theorem bank_out {sp : BitVec 64} {R : Nat → BitVec 64} {slots : List (Nat × Nat)} {a : Nat}
    (top : WriteWindow (low sp + BitVec.ofNat 64 72) 8) (bounded : ∀ cell ∈ slots, cell.2 ≤ 72)
    (apart : a + 8 ≤ (low sp).toNat ∨ (low sp).toNat + 80 ≤ a) :
    OutLRange (SaveBank.log (low sp) R slots) a 8 := by
  apply outLRange_of_forall
  intro e member
  obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp member
  have address := stack_address (low sp) cell.2 72 (stack_bound _ 72 (by decide) top) (bounded cell hc)
  have small := bounded cell hc
  dsimp only
  omega

/-- The whole effect: both frames' saves. -/
def bankLog (sp s1 s2 ra idx : BitVec 64) : List WEntry := SaveBank.log (low sp) (bankR s1 s2 ra idx) bankSlots

theorem bankLog_split (sp s1 s2 ra idx : BitVec 64) :
    bankLog sp s1 s2 ra idx = headLog sp s1 s2 ra ++ arrayLog (frame sp) idx := by
  rw [headLog_bank sp s1 s2 ra idx, arrayLog_bank sp s1 s2 ra idx, bankLog, bankSlots, SaveBank.log,
    SaveBank.log, SaveBank.log, List.map_append]

theorem iter_eval_regs (fsp idx : BitVec 64) (l : List (BitVec 8)) :
    (evalBlocks [iterBlock] (SegEvalState.init (atIter fsp idx) [l])).regs = afterIter fsp idx (bytesVal .ld l) := by
  simp only [evalBlocks, evalBlock, SegEvalState.init, iter_regs]

theorem onArray_eval_regs (fsp idx ctx : BitVec 64) (l l' : List (BitVec 8)) :
    (evalBlocks [onArrayBlock] (SegEvalState.init (afterIter fsp idx ctx) [l, l'])).regs =
      afterOnArray fsp idx ctx l l' := by
  simp only [evalBlocks, evalBlock, SegEvalState.init, onArray_regs]

/-! ## The whole quiet call -/

/-- The words the quiet path reads outside its frames: `entries_global`'s
`young_idx` and `len`, the hook, `local`, and the main context's entry
array's `young_idx` and `len` (`ctx + 16` is the array). -/
def reads (ctx : BitVec 64) : List (BitVec 64) :=
  [0x80063b40#64, 0x80063b38#64, 0x800648d0#64, 0x800648d8#64, ctx + 16#64 + 32#64, ctx + 16#64 + 24#64]

/-- The quiet call's input: memprof tracks no young block. -/
structure Input (sp s1 s2 ra ctx : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : CodeAt c.σ.mem
  registers : GHolds c.σ (regs sp s1 s2 ra)
  saves : ∀ cell ∈ bankSlots, WriteWindow (low sp + BitVec.ofNat 64 cell.2) 8
  windows : ∀ a ∈ reads ctx, ReadWindow a 8
  apart : ∀ a ∈ reads ctx, a.toNat + 8 ≤ (low sp).toNat ∨ (low sp).toNat + 80 ≤ a.toNat
  /-- the default thread-context iterator -/
  hook : bytesT c.σ.mem hookAddr 8 = iterPc
  /-- the main context -/
  context : bytesT c.σ.mem localAddr 8 = ctx
  /-- `entries_global.young_idx ≥ len` -/
  quietGlobal : (bytesT c.σ.mem 0x80063b38 8).toNat ≤ (bytesT c.σ.mem 0x80063b40 8).toNat
  /-- the main context's entries likewise -/
  quietMain : (bytesT c.σ.mem (ctx + 16#64 + 24#64).toNat 8).toNat ≤
    (bytesT c.σ.mem (ctx + 16#64 + 32#64).toNat 8).toNat
  aligned : ra.toNat % 4 = 0

/-- The registers the quiet call may change. -/
def writes : List Nat := [1, 2, 9, 10, 11, 14, 15, 18]

structure Post (sp s1 s2 ra : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : PCAt ra after
  registers : GHolds after.σ [(2, sp), (9, s1), (18, s2)]
  memory : after.σ.mem = writeLog before.σ.mem (bankLog sp s1 s2 ra (bytesT before.σ.mem 0x80063b40 8))
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem frame_restore (sp : BitVec 64) : frame sp + 48#64 = sp := by
  rw [frame, BitVec.add_assoc]
  have : (18446744073709551568#64 + 48#64 : BitVec 64) = 0#64 := by decide
  rw [this, BitVec.add_zero]

theorem array_restore (fsp : BitVec 64) : fsp + 18446744073709551584#64 + 32#64 = fsp := by
  rw [BitVec.add_assoc]
  have : (18446744073709551584#64 + 32#64 : BitVec 64) = 0#64 := by decide
  rw [this, BitVec.add_zero]

theorem read_out {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} {a : Nat} (out : OutLRange log a 8) :
    bytesVal .ld (read8 (writeLog m log) a) = bytesT m a 8 := by
  rw [read8_value, bytesT_writeLog_out _ out]

/-- A state between pieces: at `here` with registers `L` and memory `mem`,
everything else as at the call's entry `c0`. -/
structure Stage (c0 : Config) (here : BitVec 64) (L : GRegs) (mem : Std.ExtHashMap Nat (BitVec 8)) (d : Config) :
    Prop where
  good : GoodState d.σ
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  code : CodeAt d.σ.mem
  pc : PCAt here d
  regs : GHolds d.σ L
  memory : d.σ.mem = mem
  output : d.σ.sailOutput = c0.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) → d.σ.regs.get? r = c0.σ.regs.get? r

theorem mem_reads {ctx a : BitVec 64} (h : a = 0x80063b40#64 ∨ a = 0x80063b38#64 ∨ a = 0x800648d0#64 ∨
    a = 0x800648d8#64 ∨ a = ctx + 16#64 + 32#64 ∨ a = ctx + 16#64 + 24#64) : a ∈ reads ctx := by
  simp only [reads, List.mem_cons, List.not_mem_nil, or_false]
  exact h

theorem out_head {sp s1 s2 ra ctx c0 a} (input : Input sp s1 s2 ra ctx c0) (h : a ∈ reads ctx) :
    OutLRange (headLog sp s1 s2 ra) a.toNat 8 := by
  rw [headLog_bank sp s1 s2 ra 0#64]
  exact bank_out (input.saves (1, 72) (by decide)) (by decide) (input.apart a h)

theorem out_array {sp s1 s2 ra ctx c0 a} (idx : BitVec 64) (input : Input sp s1 s2 ra ctx c0) (h : a ∈ reads ctx) :
    OutLRange (arrayLog (frame sp) idx) a.toNat 8 := by
  rw [arrayLog_bank sp s1 s2 ra idx]
  exact bank_out (input.saves (1, 72) (by decide)) (by decide) (input.apart a h)

/-- The head, from the entry to the hook's `jalr`. -/
theorem stage_head {sp s1 s2 ra ctx c0} (input : Input sp s1 s2 ra ctx c0) (pcAt : PCAt pc c0) :
    ∃ d, Steps c0 d ∧ Stage c0 callPc (carried (frame sp) (bytesT c0.σ.mem 0x80063b40 8))
      (writeLog c0.σ.mem (headLog sp s1 s2 ra)) d := by
  have r40 := mem_reads (ctx := ctx) (Or.inl rfl)
  have r38 := mem_reads (ctx := ctx) (Or.inr (Or.inl rfl))
  have rHook := mem_reads (ctx := ctx) (Or.inr (Or.inr (Or.inl rfl)))
  have access1 : ChainAccess c0.σ.mem (regs sp s1 s2 ra) (headLoads c0.σ.mem sp s1 s2 ra) headBlocks := by
    apply ChainAccess.cons ⟨head_access sp s1 s2 ra _ _ (head_windows input.saves) (input.windows _ r40)
      (input.windows _ r38) (out_head input r40) (out_head input r38),
      head_control sp s1 s2 ra _ _ _ (by rw [read8_value, read8_value]; exact input.quietGlobal)⟩
    rw [head_regs, head_log, head_lds]
    exact ChainAccess.cons ⟨hook_access _ ra _ _ _ _ (input.windows _ rHook), trivial⟩ ChainAccess.nil
  have facts := chainPlan_facts (fun b hb => head_code input.code.memprof b (List.mem_append_left _ hb)) access1
  obtain ⟨d, run, post⟩ := (block_summary headBlocks pc (regs sp s1 s2 ra) (headLoads c0.σ.mem sp s1 s2 ra) c0
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2, 18, 1, 9]; decide, facts, head_chain_ok,
      input.tick⟩).run c0 ⟨pcAt, rfl⟩
  have outHook : OutLRange (headLog sp s1 s2 ra) hookAddr 8 := out_head input rHook
  have holds := post.regs
  rw [head_eval_regs] at holds
  unfold atCall at holds
  rw [read_out outHook, input.hook, read8_value] at holds
  refine ⟨d, run, post.good, post.minstret, post.tick, input.code.after facts post, ?_, ?_, ?_, post.output, ?_⟩
  · rw [PCAt, post.pc, head_eval_pc]
  · apply gholds_select holds
    intro n v member
    simp only [carried, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h <;> cases h <;> rfl
  · rw [post.memory, head_eval_log]
  · intro r noise out
    exact post.frame r noise (fun n hn => out n (by revert n hn; decide))

/-- The hook's `jalr` into `th_ctx_iter_default`. -/
theorem stage_hook {c0 d fsp idx mem} (st : Stage c0 callPc (carried fsp idx) mem d) :
    ∃ e, Steps d e ∧ Stage c0 iterPc (atIter fsp idx) mem e := by
  obtain ⟨e, run, post⟩ := (indirect_summary hook_shape hook_decode d (hook_pins st.code.memprof) st.good
    st.tick st.minstret (carried fsp idx) st.regs
    (by change KeysOK [10, 11, 15, 2, 18, 9]; decide) (by change ∀ n ∈ [10, 11, 15, 2, 18, 9], n ≠ 1; decide)
    iterPc rfl (by rw [hook_target]; decide)).run d ⟨st.pc, rfl⟩
  rw [hook_target, hook_link] at post
  have holds : GHolds e.σ ((1, retPc) :: carried fsp idx) := ⟨post.ra, post.registers⟩
  have same : e.σ.mem = d.σ.mem := by rw [post.mem]; rfl
  refine ⟨e, run, post.good, post.minstret, post.tick, by rw [same]; exact st.code, post.pc, ?_,
    by rw [same]; exact st.memory, post.output.trans st.output, ?_⟩
  · apply gholds_select holds
    intro n v member
    simp only [atIter, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h <;> cases h <;> rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => by change n ∈ ([] : List Nat) at hn; cases hn) (out 1 (by decide))]
    exact st.frame r noise out

/-- `th_ctx_iter_default`: load the main context, tail-jump to the callback. -/
theorem stage_iter {sp s1 s2 ra ctx c0 d idx} (input : Input sp s1 s2 ra ctx c0)
    (st : Stage c0 iterPc (atIter (frame sp) idx) (writeLog c0.σ.mem (headLog sp s1 s2 ra)) d) :
    ∃ e, Steps d e ∧ Stage c0 onArrayPc (afterIter (frame sp) idx ctx) (writeLog c0.σ.mem (headLog sp s1 s2 ra)) e := by
  have rLocal := mem_reads (ctx := ctx) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have access : ChainAccess d.σ.mem (atIter (frame sp) idx) [read8 d.σ.mem localAddr] [iterBlock] :=
    ChainAccess.cons ⟨iter_access _ _ _ [] (input.windows _ rLocal), iter_control _ _ _ []⟩ ChainAccess.nil
  have facts := chainPlan_facts (iter_code st.code.iter) access
  obtain ⟨e, run, post⟩ := (block_summary [iterBlock] iterPc (atIter (frame sp) idx) [read8 d.σ.mem localAddr] d
    ⟨st.good, st.minstret, st.regs, by change KeysOK [10, 11, 2, 1, 18, 9]; decide, facts, iter_chain_ok,
      st.tick⟩).run d ⟨st.pc, rfl⟩
  have outLocal : OutLRange (headLog sp s1 s2 ra) localAddr 8 := out_head input rLocal
  have ctxVal : bytesVal .ld (read8 d.σ.mem localAddr) = ctx := by
    rw [st.memory, read_out outLocal, input.context]
  have holds := post.regs
  rw [iter_eval_regs, ctxVal] at holds
  refine ⟨e, run, post.good, post.minstret, post.tick, st.code.after facts post, ?_, holds, ?_,
    post.output.trans st.output, ?_⟩
  · rw [PCAt, post.pc, iter_eval_pc]
  · rw [post.memory, ← st.memory]; rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide))]
    exact st.frame r noise out

/-- `call_on_entry_array`: load the callback and its data from the caller's
frame, tail-jump to `entry_array_oldify_young_roots` on `ctx + 16`. -/
theorem stage_onArray {sp s1 s2 ra ctx c0 d idx} (input : Input sp s1 s2 ra ctx c0)
    (st : Stage c0 onArrayPc (afterIter (frame sp) idx ctx) (writeLog c0.σ.mem (headLog sp s1 s2 ra)) d) :
    ∃ e, Steps d e ∧ Stage c0 arrayPc (atArray (frame sp) idx (ctx + 16#64))
      (writeLog c0.σ.mem (headLog sp s1 s2 ra)) e := by
  have e0 : frame sp = low sp + BitVec.ofNat 64 32 := by
    have h := frame_add sp 0
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h
  have w0 : ReadWindow (frame sp) 8 := by rw [e0]; exact (input.saves (14, 32) (by decide)).read
  have w8 : ReadWindow (frame sp + 8#64) 8 := by rw [frame_add]; exact (input.saves (0, 40) (by decide)).read
  have headSaves : ∀ cell ∈ headSlots, WriteWindow (low sp + BitVec.ofNat 64 cell.2) 8 :=
    fun cell hc => input.saves cell (by rw [bankSlots]; exact List.mem_append_left _ hc)
  have target : bytesVal .ld (read8 d.σ.mem (frame sp).toNat) = arrayPc := by
    rw [read8_value, st.memory, headLog_bank sp s1 s2 ra idx, e0]
    exact headShape.read c0.σ.mem (low sp) (bankR s1 s2 ra idx) headSaves (14, 32) (by decide)
  have access : ChainAccess d.σ.mem (afterIter (frame sp) idx ctx)
      [read8 d.σ.mem (frame sp).toNat, read8 d.σ.mem (frame sp + 8#64).toNat] [onArrayBlock] :=
    ChainAccess.cons ⟨onArray_access _ _ _ _ [] w0 w8, onArray_control _ _ _ _ _ [] target⟩ ChainAccess.nil
  have facts := chainPlan_facts (onArray_code st.code.onArray) access
  obtain ⟨e, run, post⟩ := (block_summary [onArrayBlock] onArrayPc (afterIter (frame sp) idx ctx)
    [read8 d.σ.mem (frame sp).toNat, read8 d.σ.mem (frame sp + 8#64).toNat] d
    ⟨st.good, st.minstret, st.regs, by change KeysOK [10, 15, 11, 2, 1, 18, 9]; decide, facts, onArray_chain_ok,
      st.tick⟩).run d ⟨st.pc, rfl⟩
  have holds := post.regs
  rw [onArray_eval_regs] at holds
  refine ⟨e, run, post.good, post.minstret, post.tick, st.code.after facts post, ?_, ?_, ?_,
    post.output.trans st.output, ?_⟩
  · rw [PCAt, post.pc, onArray_eval_pc _ _ _ _ _ target]
  · apply gholds_select holds
    intro n v member
    simp only [atArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h <;> cases h <;> rfl
  · rw [post.memory, ← st.memory]; rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide))]
    exact st.frame r noise out

theorem array_eval_regs (fsp idx arr : BitVec 64) (l l' r1 r2 : List (BitVec 8)) :
    (evalBlocks arrayBlocks (SegEvalState.init (atArray fsp idx arr) [l, l', r1, r2])).regs =
      afterArrayRet fsp arr l' r1 r2 := by
  simp only [arrayBlocks, evalBlocks, evalBlock, SegEvalState.init, array_regs, array_lds, arrayRet_regs]

theorem array_eval_log (fsp idx arr : BitVec 64) (l l' r1 r2 : List (BitVec 8)) :
    (evalBlocks arrayBlocks (SegEvalState.init (atArray fsp idx arr) [l, l', r1, r2])).log = arrayLog fsp idx := by
  simp only [arrayBlocks, evalBlocks, evalBlock, SegEvalState.init, array_regs, array_lds, array_log, arrayRet_log,
    List.append_nil, List.nil_append]

theorem array_eval_pc (fsp idx arr : BitVec 64) (l l' r1 r2 : List (BitVec 8)) (link : bytesVal .ld r1 = retPc) :
    evalBlocksPC arrayPc (SegEvalState.init (atArray fsp idx arr) [l, l', r1, r2]) arrayBlocks = retPc := by
  simp only [arrayBlocks, evalBlocksPC, SegEvalState.init, chainEndPC, endPCB, array_regs, array_lds]
  change Sail.BitVec.update (srcVal 1 (runGM arrayRetBlock.body (afterArray fsp arr l l') [r1, r2]) + 0#64) 0 0#1 = _
  rw [arrayRet_regs]
  change Sail.BitVec.update (bytesVal .ld r1 + 0#64) 0 0#1 = _
  rw [link]
  exact ret_tgt retPc (by decide)

theorem ret_eval_regs (fsp : BitVec 64) (r1 r2 r3 : List (BitVec 8)) :
    (evalBlocks [retBlock] (SegEvalState.init [(2, fsp)] [r1, r2, r3])).regs = restored fsp r1 r2 r3 := by
  simp only [evalBlocks, evalBlock, SegEvalState.init, ret_regs]

theorem ret_eval_pc (fsp ra : BitVec 64) (r1 r2 r3 : List (BitVec 8)) (link : bytesVal .ld r1 = ra)
    (aligned : ra.toNat % 4 = 0) :
    evalBlocksPC retPc (SegEvalState.init [(2, fsp)] [r1, r2, r3]) [retBlock] = ra := by
  simp only [evalBlocksPC, SegEvalState.init, chainEndPC, endPCB]
  change Sail.BitVec.update (srcVal 1 (runGM retBlock.body [(2, fsp)] [r1, r2, r3]) + 0#64) 0 0#1 = _
  rw [ret_regs]
  change Sail.BitVec.update (bytesVal .ld r1 + 0#64) 0 0#1 = _
  rw [link]
  exact ret_tgt ra aligned

/-- `entry_array_oldify_young_roots` on the empty main context: save, test, return. -/
theorem stage_array {sp s1 s2 ra ctx c0 d idx} (input : Input sp s1 s2 ra ctx c0)
    (st : Stage c0 arrayPc (atArray (frame sp) idx (ctx + 16#64)) (writeLog c0.σ.mem (headLog sp s1 s2 ra)) d) :
    ∃ e, Steps d e ∧ Stage c0 retPc [(2, frame sp)] (writeLog c0.σ.mem (bankLog sp s1 s2 ra idx)) e := by
  have r32 := mem_reads (ctx := ctx) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have r24 := mem_reads (ctx := ctx) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have arraySaves : ∀ cell ∈ arraySlots, WriteWindow (low sp + BitVec.ofNat 64 cell.2) 8 :=
    fun cell hc => input.saves cell (by rw [bankSlots]; exact List.mem_append_right _ hc)
  have w24 : WriteWindow (frame sp + 18446744073709551584#64 + 24#64) 8 := by
    rw [array_frame]; exact arraySaves (101, 24) (by decide)
  have w8 : WriteWindow (frame sp + 18446744073709551584#64 + 8#64) 8 := by
    rw [array_frame]; exact arraySaves (109, 8) (by decide)
  have quiet : (bytesVal .ld (read8 (writeLog d.σ.mem (arrayLog (frame sp) idx)) (ctx + 16#64 + 24#64).toNat)).toNat ≤
      (bytesVal .ld (read8 (writeLog d.σ.mem (arrayLog (frame sp) idx)) (ctx + 16#64 + 32#64).toNat)).toNat := by
    rw [read_out (out_array idx input r24), read_out (out_array idx input r32), st.memory,
      bytesT_writeLog_out _ (out_head input r24), bytesT_writeLog_out _ (out_head input r32)]
    exact input.quietMain
  have link : bytesVal .ld (read8 (writeLog d.σ.mem (arrayLog (frame sp) idx))
      (frame sp + 18446744073709551584#64 + 24#64).toNat) = retPc := by
    rw [read8_value, arrayLog_bank sp s1 s2 ra idx, array_frame]
    exact arrayShape.read d.σ.mem (low sp) (bankR s1 s2 ra idx) arraySaves (101, 24) (by decide)
  have access : ChainAccess d.σ.mem (atArray (frame sp) idx (ctx + 16#64))
      [read8 (writeLog d.σ.mem (arrayLog (frame sp) idx)) (ctx + 16#64 + 32#64).toNat,
       read8 (writeLog d.σ.mem (arrayLog (frame sp) idx)) (ctx + 16#64 + 24#64).toNat,
       read8 (writeLog d.σ.mem (arrayLog (frame sp) idx)) (frame sp + 18446744073709551584#64 + 24#64).toNat,
       read8 (writeLog d.σ.mem (arrayLog (frame sp) idx)) (frame sp + 18446744073709551584#64 + 8#64).toNat]
      arrayBlocks := by
    apply ChainAccess.cons ⟨array_access _ _ _ _ _ w24 w8 (input.windows _ r32) (input.windows _ r24),
      array_control _ _ _ _ _ _ quiet⟩
    rw [array_regs, array_log, array_lds]
    exact ChainAccess.cons ⟨arrayRet_access _ _ _ _ _ w24.read w8.read, arrayRet_control _ _ _ _ _ _ link⟩
      ChainAccess.nil
  have facts := chainPlan_facts (array_code st.code.array) access
  obtain ⟨e, run, post⟩ := (block_summary arrayBlocks arrayPc (atArray (frame sp) idx (ctx + 16#64)) _ d
    ⟨st.good, st.minstret, st.regs, by change KeysOK [2, 1, 9, 10]; decide, facts, array_chain_ok,
      st.tick⟩).run d ⟨st.pc, rfl⟩
  have holds := post.regs
  rw [array_eval_regs] at holds
  unfold afterArrayRet at holds
  rw [array_restore] at holds
  refine ⟨e, run, post.good, post.minstret, post.tick, st.code.after facts post, ?_, ?_, ?_,
    post.output.trans st.output, ?_⟩
  · rw [PCAt, post.pc, array_eval_pc _ _ _ _ _ _ _ link]
  · exact ⟨holds.1, trivial⟩
  · rw [post.memory, array_eval_log, st.memory, ← writeLog_append, ← bankLog_split]
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide))]
    exact st.frame r noise out

/-- The caller's restores and return. -/
theorem stage_ret {sp s1 s2 ra ctx c0 d} (input : Input sp s1 s2 ra ctx c0)
    (st : Stage c0 retPc [(2, frame sp)]
      (writeLog c0.σ.mem (bankLog sp s1 s2 ra (bytesT c0.σ.mem 0x80063b40 8))) d) :
    ∃ e, Steps d e ∧ Post sp s1 s2 ra c0 e := by
  have back : ∀ cell ∈ bankSlots, bytesT d.σ.mem (low sp + BitVec.ofNat 64 cell.2).toNat 8 =
      bankR s1 s2 ra (bytesT c0.σ.mem 0x80063b40 8) cell.1 := by
    intro cell member
    rw [st.memory, bankLog]
    exact bankShape.read c0.σ.mem (low sp) _ input.saves cell member
  have b40 : bytesT d.σ.mem (frame sp + 40#64).toNat 8 = ra := by rw [frame_add]; exact back (1, 72) (by decide)
  have b24 : bytesT d.σ.mem (frame sp + 24#64).toNat 8 = s1 := by rw [frame_add]; exact back (9, 56) (by decide)
  have b16 : bytesT d.σ.mem (frame sp + 16#64).toNat 8 = s2 := by rw [frame_add]; exact back (18, 48) (by decide)
  have windows : ∀ off ∈ [40, 24, 16], ReadWindow (frame sp + BitVec.ofNat 64 off) 8 := by
    intro off member
    rw [frame_add]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact (input.saves (1, 72) (by decide)).read
    · exact (input.saves (9, 56) (by decide)).read
    · exact (input.saves (18, 48) (by decide)).read
  have link : bytesVal .ld (read8 d.σ.mem (frame sp + 40#64).toNat) = ra := by rw [read8_value, b40]
  have access : ChainAccess d.σ.mem [(2, frame sp)]
      [read8 d.σ.mem (frame sp + 40#64).toNat, read8 d.σ.mem (frame sp + 24#64).toNat,
       read8 d.σ.mem (frame sp + 16#64).toNat] [retBlock] :=
    ChainAccess.cons ⟨ret_access (frame sp) d.σ.mem windows, ret_control (frame sp) ra _ _ _ link input.aligned⟩
      ChainAccess.nil
  have facts := chainPlan_facts (fun b hb => head_code st.code.memprof b (List.mem_append_right _ hb)) access
  obtain ⟨e, run, post⟩ := (block_summary [retBlock] retPc [(2, frame sp)] _ d
    ⟨st.good, st.minstret, st.regs, by change KeysOK [2]; decide, facts, ret_chain_ok,
      st.tick⟩).run d ⟨st.pc, rfl⟩
  have holds := post.regs
  rw [ret_eval_regs] at holds
  unfold restored at holds
  rw [frame_restore, read8_value, read8_value, b16, b24] at holds
  refine ⟨e, run, post.good, post.minstret, post.tick, ?_, ?_, ?_, post.output.trans st.output, ?_⟩
  · rw [PCAt, post.pc, ret_eval_pc _ _ _ _ _ link input.aligned]
  · apply gholds_select holds
    intro n v member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h <;> cases h <;> rfl
  · rw [post.memory, ← st.memory]; rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide))]
    exact st.frame r noise out

/-- **`caml_memprof_oldify_young_roots` with memprof idle**, entry to return:
the two frames' saves are its only stores. -/
theorem call {sp s1 s2 ra ctx c} (input : Input sp s1 s2 ra ctx c) :
    FnSummary pc (fun d => d = c) (Post sp s1 s2 ra c) := by
  constructor
  rintro c0 ⟨pcAt, rfl⟩
  obtain ⟨d1, run1, st1⟩ := stage_head input pcAt
  obtain ⟨d2, run2, st2⟩ := stage_hook st1
  obtain ⟨d3, run3, st3⟩ := stage_iter input st2
  obtain ⟨d4, run4, st4⟩ := stage_onArray input st3
  obtain ⟨d5, run5, st5⟩ := stage_array input st4
  obtain ⟨d6, run6, post⟩ := stage_ret input st5
  exact ⟨d6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), post⟩

end OCaml.Vm.Gc.MemprofQuiet
