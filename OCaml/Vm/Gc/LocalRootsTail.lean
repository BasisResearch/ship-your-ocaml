import OCaml.Vm.Gc.StackLoop
import OCaml.Vm.Gc.FinalQuiet
import OCaml.Vm.Gc.MemprofQuiet

/-! # The tail of `caml_oldify_local_roots`, after the VM-stack loop

At the loop exit (`0x8000c7cc`) with no local C roots (`Caml_state->local_roots`
is NULL: a minor collection from the interpreter's poll holds none), the
function calls `caml_scan_global_young_roots(&caml_oldify_one)`,
`caml_final_oldify_young_roots()` and `caml_memprof_oldify_young_roots()`,
finds `caml_scan_roots_hook` NULL, restores its frame and returns.

The global scan is a supplied premise at its `jal` site (`scan`), in the style
of `SlotSite.slot`; the finaliser and memprof calls are `FinalQuiet.call` and
`MemprofQuiet.call`. -/
namespace OCaml.Vm.Gc.LocalRootsTail
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def exitBlock : BBlock := caml_oldify_local_rootsXc7ccTSeg.getD 0 {body := [], term := none}
def argBlock : BBlock := caml_oldify_local_rootsXc830Seg.getD 0 {body := [], term := none}
def hookBlock : BBlock := caml_oldify_local_rootsXc844TSeg.getD 0 {body := [], term := none}
def retBlock : BBlock := caml_oldify_local_rootsXc870Seg.getD 0 {body := [], term := none}

def exitPc : BitVec 64 := 0x8000c7cc#64
def hookPc : BitVec 64 := 0x8000c844#64
def oldifyPc : BitVec 64 := 0x80009a70#64
def hookAddr : Nat := 0x80064b18

/-- The registers at the loop exit: the domain pointer, the frame, `s0`,
`s1 = &Caml_state`, and the callee-saved `s3`–`s9`. -/
def exitRegs (R : Nat → BitVec 64) (dom fsp s0 : BitVec 64) : GRegs :=
  [(15, dom), (2, fsp), (8, s0), (9, StackScan.statePtr), (19, R 19), (20, R 20), (21, R 21),
   (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

def atScan (R : Nat → BitVec 64) (dom fsp s0 : BitVec 64) (l : List (BitVec 8)) : GRegs :=
  [(10, oldifyPc), (18, bytesVal .ld l), (15, dom), (2, fsp), (8, s0), (9, StackScan.statePtr), (19, R 19),
   (20, R 20), (21, R 21), (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

def exitBlocks : List BBlock := [exitBlock, argBlock]

theorem exit_eval_regs (R : Nat → BitVec 64) (dom fsp s0 : BitVec 64) (l : List (BitVec 8)) :
    (evalBlocks exitBlocks (SegEvalState.init (exitRegs R dom fsp s0) [l])).regs = atScan R dom fsp s0 l := by
  simp [exitBlocks, evalBlocks, evalBlock, SegEvalState.init, exitBlock, argBlock, caml_oldify_local_rootsXc7ccTSeg,
    caml_oldify_local_rootsXc830Seg, exitRegs, atScan, oldifyPc, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG,
    eraseG, mkLine, decodeM, imm20Of, ldsRunM, Functions.sign_extend, Sail.BitVec.signExtend]

theorem exit_eval_log (R : Nat → BitVec 64) (dom fsp s0 : BitVec 64) (l : List (BitVec 8)) :
    (evalBlocks exitBlocks (SegEvalState.init (exitRegs R dom fsp s0) [l])).log = [] := rfl

theorem exit_eval_pc (R : Nat → BitVec 64) (dom fsp s0 : BitVec 64) (l : List (BitVec 8)) :
    evalBlocksPC exitPc (SegEvalState.init (exitRegs R dom fsp s0) [l]) exitBlocks =
      LocalRootsSites.scanCall.pc := rfl

theorem exit_chain_ok : ChainOK exitPc [15, 2, 8, 9, 19, 20, 21, 22, 23, 24, 25] exitBlocks := by decide

theorem exit_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_oldify_local_rootsLoaded mem) :
    ChainCode mem exitBlocks := by
  intro b hb
  simp only [exitBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  all_goals constructor
  all_goals simp only [exitBlock, argBlock, caml_oldify_local_rootsXc7ccTSeg, caml_oldify_local_rootsXc830Seg,
    List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_oldify_local_roots_at_"

theorem exit_access (R : Nat → BitVec 64) (dom fsp s0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (window : ReadWindow (dom + 288#64) 8) (none : bytesT m (dom + 288#64).toNat 8 = 0#64) :
    ChainAccess m (exitRegs R dom fsp s0) [read8 m (dom + 288#64).toNat] exitBlocks := by
  refine ChainAccess.cons ⟨?_, ?_⟩ ?_
  · simp only [exitBlock, caml_oldify_local_rootsXc7ccTSeg, List.getD_cons_zero, AccessPlan]
    chain_facts True.intro
    refine window.ld rfl ?_ (read8_pins _ _)
    simp [exitRegs, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · simp [exitBlock, caml_oldify_local_rootsXc7ccTSeg, exitRegs, TermFactsO, TermFactsT, runGM, stepGM, stepLdsM,
      wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, guardB, read8_value,
      Functions.sign_extend, Sail.BitVec.signExtend]
    simpa [BitVec.toNat_add] using none
  · refine ChainAccess.cons ⟨?_, trivial⟩ ChainAccess.nil
    simp only [argBlock, caml_oldify_local_rootsXc830Seg, List.getD_cons_zero, AccessPlan]
    chain_facts True.intro

/-! ## The hook test and the epilogue -/

def hookBlocks : List BBlock := [hookBlock, retBlock]

def restored (fsp : BitVec 64) (l r1 r2 r3 r4 : List (BitVec 8)) : GRegs :=
  [(2, fsp + 48#64), (18, bytesVal .ld r4), (9, bytesVal .ld r3), (8, bytesVal .ld r2), (1, bytesVal .ld r1),
   (15, bytesVal .ld l)]

theorem hook_regs (fsp : BitVec 64) (l : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM hookBlock.body [(2, fsp)] (l :: rest) = [(15, bytesVal .ld l), (2, fsp)] := by
  simp [hookBlock, caml_oldify_local_rootsXc844TSeg, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG,
    eraseG, mkLine, decodeM, imm20Of, Functions.sign_extend, Sail.BitVec.signExtend]

theorem hook_lds (l : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    ldsRunM hookBlock.body (l :: rest) = rest := rfl

theorem ret_regs (fsp : BitVec 64) (l r1 r2 r3 r4 : List (BitVec 8)) :
    runGM retBlock.body [(15, bytesVal .ld l), (2, fsp)] [r1, r2, r3, r4] = restored fsp l r1 r2 r3 r4 := by
  simp [retBlock, caml_oldify_local_rootsXc870Seg, restored, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG,
    eraseG, mkLine, decodeM, Functions.sign_extend, Sail.BitVec.signExtend]

theorem hook_eval_regs (fsp : BitVec 64) (l r1 r2 r3 r4 : List (BitVec 8)) :
    (evalBlocks hookBlocks (SegEvalState.init [(2, fsp)] [l, r1, r2, r3, r4])).regs = restored fsp l r1 r2 r3 r4 := by
  simp only [hookBlocks, evalBlocks, evalBlock, SegEvalState.init]
  rw [hook_regs]
  exact ret_regs fsp l r1 r2 r3 r4

theorem hook_eval_log (fsp : BitVec 64) (l r1 r2 r3 r4 : List (BitVec 8)) :
    (evalBlocks hookBlocks (SegEvalState.init [(2, fsp)] [l, r1, r2, r3, r4])).log = [] := rfl

theorem hook_eval_pc (fsp ra : BitVec 64) (l r1 r2 r3 r4 : List (BitVec 8)) (link : bytesVal .ld r1 = ra)
    (aligned : ra.toNat % 4 = 0) :
    evalBlocksPC hookPc (SegEvalState.init [(2, fsp)] [l, r1, r2, r3, r4]) hookBlocks = ra := by
  simp only [hookBlocks, evalBlocksPC, SegEvalState.init, chainEndPC, endPCB]
  change Sail.BitVec.update (srcVal 1 (runGM retBlock.body (runGM hookBlock.body [(2, fsp)] [l, r1, r2, r3, r4])
    [r1, r2, r3, r4]) + 0#64) 0 0#1 = _
  rw [hook_regs, ret_regs]
  change Sail.BitVec.update (bytesVal .ld r1 + 0#64) 0 0#1 = _
  rw [link]
  exact ret_tgt ra aligned

theorem hook_chain_ok : ChainOK hookPc [2] hookBlocks := by decide

theorem hook_code {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_oldify_local_rootsLoaded mem) :
    ChainCode mem hookBlocks := by
  intro b hb
  simp only [hookBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  all_goals constructor
  all_goals simp only [hookBlock, retBlock, caml_oldify_local_rootsXc844TSeg, caml_oldify_local_rootsXc870Seg,
    List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_oldify_local_roots_at_"

theorem hook_access (fsp ra : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (hookRead : ReadWindow 0x80064b18#64 8) (none : bytesT m hookAddr 8 = 0#64)
    (windows : ∀ off ∈ [40, 32, 24, 16], ReadWindow (fsp + BitVec.ofNat 64 off) 8)
    (link : bytesT m (fsp + 40#64).toNat 8 = ra) (aligned : ra.toNat % 4 = 0) :
    ChainAccess m [(2, fsp)]
      [read8 m hookAddr, read8 m (fsp + 40#64).toNat, read8 m (fsp + 32#64).toNat, read8 m (fsp + 24#64).toNat,
       read8 m (fsp + 16#64).toNat] hookBlocks := by
  refine ChainAccess.cons ⟨?_, ?_⟩ ?_
  · simp only [hookBlock, caml_oldify_local_rootsXc844TSeg, List.getD_cons_zero, AccessPlan]
    chain_facts True.intro
    refine hookRead.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG, imm20Of,
      Functions.sign_extend, Sail.BitVec.signExtend]
  · rw [hook_regs]
    simp [hookBlock, caml_oldify_local_rootsXc844TSeg, TermFactsO, TermFactsT, srcVal, lookupG, guardB,
      read8_value, none]
  · rw [hook_regs, hook_lds]
    refine ChainAccess.cons ⟨?_, ?_⟩ ChainAccess.nil
    · simp only [retBlock, caml_oldify_local_rootsXc870Seg, List.getD_cons_zero, AccessPlan]
      chain_facts True.intro
      · exact (windows 40 (by decide)).ld rfl rfl (read8_pins _ _)
      · exact (windows 32 (by decide)).ld rfl rfl (read8_pins _ _)
      · exact (windows 24 (by decide)).ld rfl rfl (read8_pins _ _)
      · exact (windows 16 (by decide)).ld rfl rfl (read8_pins _ _)
    · rw [ret_regs]
      exact return_facts _ rfl rfl rfl (by change bytesVal .ld (read8 m (fsp + 40#64).toNat) = ra; rw [read8_value, link]) aligned

/-! ## Frame arithmetic: both callees' saves lie in `[fsp − 80, fsp)` -/

open MemprofQuiet (low shift bank_out) in
theorem final_frame_add (fsp : BitVec 64) (k : Nat) :
    FinalQuiet.frame fsp + BitVec.ofNat 64 k = MemprofQuiet.low fsp + BitVec.ofNat 64 (k + 48) := by
  apply MemprofQuiet.shift
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem frame_word_add (fsp : BitVec 64) (k : Nat) :
    fsp + BitVec.ofNat 64 k = MemprofQuiet.low fsp + BitVec.ofNat 64 (k + 80) := by
  rw [MemprofQuiet.low, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A read window bounds a small stack displacement away from wrapping. -/
theorem read_bound (base : BitVec 64) (off : Nat) (small : off < 0x80000000)
    (window : ReadWindow (base + BitVec.ofNat 64 off) 8) : base.toNat + off + 8 ≤ 0x100000000 := by
  have lower := window.lower
  have upper := window.upper
  have limit := base.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at lower upper
  omega

/-- The finaliser call's saves, apart from any word outside `[fsp − 80, fsp)`. -/
theorem final_out {fsp s0 s1 s2 ra : BitVec 64} {a : Nat}
    (top : WriteWindow (MemprofQuiet.low fsp + BitVec.ofNat 64 72) 8)
    (apart : a + 8 ≤ (MemprofQuiet.low fsp).toNat ∨ (MemprofQuiet.low fsp).toNat + 80 ≤ a) :
    OutLRange (FinalQuiet.entryLog fsp s0 s1 s2 ra) a 8 := by
  rw [FinalQuiet.entryLog_bank]
  apply outLRange_of_forall
  intro e member
  obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp member
  have small : cell.2 ≤ 24 := (show ∀ c ∈ FinalQuiet.slots, c.2 ≤ 24 by decide) cell hc
  have bound := stack_bound _ 72 (by decide) top
  dsimp only
  rw [final_frame_add, stack_address (MemprofQuiet.low fsp) (cell.2 + 48) 72 bound (by omega)]
  omega

/-- A frame word `fsp + k` lies above both callees' saves. -/
theorem word_apart {fsp : BitVec 64} {k : Nat} (small : k < 0x1000)
    (window : ReadWindow (fsp + BitVec.ofNat 64 k) 8) :
    (fsp + BitVec.ofNat 64 k).toNat + 8 ≤ (MemprofQuiet.low fsp).toNat ∨
      (MemprofQuiet.low fsp).toNat + 80 ≤ (fsp + BitVec.ofNat 64 k).toNat := by
  rw [frame_word_add] at window ⊢
  have bound := read_bound _ (k + 80) (by omega) window
  rw [stack_address _ (k + 80) (k + 80) bound (Nat.le_refl _)]
  omega

/-! ## The callee-saved registers `s3`–`s9` across the tail -/

def calleeSaved (R : Nat → BitVec 64) : GRegs :=
  [(19, R 19), (20, R 20), (21, R 21), (22, R 22), (23, R 23), (24, R 24), (25, R 25)]

theorem callee_kept {R : Nat → BitVec 64} {before after : MState} {writes : List Nat}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) → after.regs.get? r = before.regs.get? r)
    (range : ∀ n ∈ writes, 1 ≤ n ∧ n < 32 ∧ (n < 19 ∨ 25 < n))
    (holds : GHolds before (calleeSaved R)) : GHolds after (calleeSaved R) := by
  apply gholds_of_frame frame _ (by change KeysOK [19, 20, 21, 22, 23, 24, 25]; decide) ?_ ?_ holds
  · change ∀ n ∈ [19, 20, 21, 22, 23, 24, 25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · intro n hn m hm
    have r := range m hm
    have small : 19 ≤ n ∧ n ≤ 25 := by
      simp only [calleeSaved, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    exact gprReg_beq_false m r.2.1 n (by omega) r.1 (by omega) (by omega)

/-! ## The code images the tail runs -/

structure TailCode (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  localRoots : Code.Caml_oldify_local_rootsLoaded m
  final : Code.Caml_final_oldify_young_rootsLoaded m
  memprof : MemprofQuiet.CodeAt m

theorem TailCode.after {bs entry regs loads before after} (code : TailCode before.σ.mem)
    (facts : ChainFacts before.σ.mem before.σ.mem regs loads bs)
    (post : BlockPost bs entry regs loads before after) : TailCode after.σ.mem :=
  ⟨image_after Code.caml_oldify_local_roots_transport (by decide) code.localRoots facts post,
   image_after Code.caml_final_oldify_young_roots_transport (by decide) code.final facts post,
   code.memprof.after facts post⟩

/-- Stores at or above `tohost + 16` (the stack) keep every code image. -/
theorem TailCode.writeLog {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} (code : TailCode m)
    (high : ∀ e ∈ log, Layout.sym_tohost + 16 ≤ e.1) : TailCode (Vsa.Sim.writeLog m log) := by
  have h : ∀ e ∈ log, tohostAddr ≤ e.1 := fun e he => by
    have := high e he; simp only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] at this ⊢; omega
  exact ⟨image_writeLog Code.caml_oldify_local_roots_transport code.localRoots (fun e he => by
      have := h e he; simp only [tohostAddr, LibraryLayout.tohostAddr] at this ⊢; omega),
    image_writeLog Code.caml_final_oldify_young_roots_transport code.final (fun e he => by
      have := h e he; simp only [tohostAddr, LibraryLayout.tohostAddr] at this ⊢; omega),
    ⟨image_writeLog Code.caml_memprof_oldify_young_roots_transport code.memprof.memprof (fun e he => by
      have := h e he; simp only [tohostAddr, LibraryLayout.tohostAddr] at this ⊢; omega),
     image_writeLog Code.th_ctx_iter_default_transport code.memprof.iter (fun e he => by
      have := h e he; simp only [tohostAddr, LibraryLayout.tohostAddr] at this ⊢; omega),
     image_writeLog Code.call_on_entry_array_transport code.memprof.onArray (fun e he => by
      have := h e he; simp only [tohostAddr, LibraryLayout.tohostAddr] at this ⊢; omega),
     image_writeLog Code.entry_array_oldify_young_roots_transport code.memprof.array (fun e he => by
      have := h e he; simp only [tohostAddr, LibraryLayout.tohostAddr] at this ⊢; omega)⟩⟩

/-! ## The tail's interface -/

/-- The ABI's caller-saved registers (`t0`–`t6`, `a0`–`a7`). -/
def scratch : List Nat := [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- The registers the tail may change: `ra`, `sp`, `s0`–`s2` (restored from the
frame) and the scratch registers. -/
def tailWrites : List Nat := [1, 2, 8, 9, 18] ++ scratch

/-- `caml_scan_global_young_roots(&caml_oldify_one)`'s arguments and carried registers. -/
def scanArgs (R : Nat → BitVec 64) (fsp s0 : BitVec 64) : GRegs :=
  (10, oldifyPc) :: (2, fsp) :: (8, s0) :: (9, StackScan.statePtr) :: (18, 0#64) :: calleeSaved R

/-- The callee-saved registers each root callee keeps. -/
def keptRegs (R : Nat → BitVec 64) (fsp s0 : BitVec 64) : GRegs :=
  (2, fsp) :: (8, s0) :: (9, StackScan.statePtr) :: (18, 0#64) :: calleeSaved R

/-- The finaliser tables' words `FinalQuiet.call` reads. -/
def finalStatics : List Nat := [0x8006c060, 0x8006c068, 0x8006c080, 0x8006c088]

/-- The words the tail reads after the global scan: the finaliser tables,
memprof's words, the hook, and the saved frame. The scan keeps them. -/
def tailWords (ctx fsp : BitVec 64) : List Nat :=
  finalStatics ++ [hookAddr] ++ (MemprofQuiet.reads ctx).map BitVec.toNat ++
    [(fsp + 16#64).toNat, (fsp + 24#64).toNat, (fsp + 32#64).toNat, (fsp + 40#64).toNat]

/-- The tail's input at the loop exit. -/
structure TailInput (R : Nat → BitVec 64) (dom fsp s0 ra0 s0o s1o s2o ctx : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : TailCode c.σ.mem
  pc : PCAt exitPc c
  registers : GHolds c.σ (exitRegs R dom fsp s0)
  /-- no local C roots -/
  localRead : ReadWindow (dom + 288#64) 8
  localNone : bytesT c.σ.mem (dom + 288#64).toNat 8 = 0#64
  /-- the saved frame -/
  frameWords : ∀ off ∈ [40, 32, 24, 16], ReadWindow (fsp + BitVec.ofNat 64 off) 8
  savedRa : bytesT c.σ.mem (fsp + 40#64).toNat 8 = ra0
  savedS0 : bytesT c.σ.mem (fsp + 32#64).toNat 8 = s0o
  savedS1 : bytesT c.σ.mem (fsp + 24#64).toNat 8 = s1o
  savedS2 : bytesT c.σ.mem (fsp + 16#64).toNat 8 = s2o
  aligned : ra0.toNat % 4 = 0
  /-- the callees' frames below `fsp` -/
  saves : ∀ cell ∈ MemprofQuiet.bankSlots, WriteWindow (MemprofQuiet.low fsp + BitVec.ofNat 64 cell.2) 8
  finalSaves : ∀ off ∈ [16, 24, 8, 0], WriteWindow (FinalQuiet.frame fsp + BitVec.ofNat 64 off) 8
  /-- the finaliser tables, quiet -/
  finalReads : ReadWindow 0x8006c060#64 8 ∧ ReadWindow 0x8006c068#64 8 ∧ ReadWindow 0x8006c080#64 8 ∧
    ReadWindow 0x8006c088#64 8
  staticsApart : ∀ a ∈ finalStatics ++ [hookAddr],
    a + 8 ≤ (MemprofQuiet.low fsp).toNat ∨ (MemprofQuiet.low fsp).toNat + 80 ≤ a
  quietFirst : (bytesT c.σ.mem 0x8006c068 8).toNat ≤ (bytesT c.σ.mem 0x8006c060 8).toNat
  quietLast : (bytesT c.σ.mem 0x8006c088 8).toNat ≤ (bytesT c.σ.mem 0x8006c080 8).toNat
  /-- memprof idle -/
  memprofReads : ∀ a ∈ MemprofQuiet.reads ctx, ReadWindow a 8
  memprofApart : ∀ a ∈ MemprofQuiet.reads ctx,
    a.toNat + 8 ≤ (MemprofQuiet.low fsp).toNat ∨ (MemprofQuiet.low fsp).toNat + 80 ≤ a.toNat
  hook : bytesT c.σ.mem MemprofQuiet.hookAddr 8 = MemprofQuiet.iterPc
  context : bytesT c.σ.mem MemprofQuiet.localAddr 8 = ctx
  quietGlobal : (bytesT c.σ.mem 0x80063b38 8).toNat ≤ (bytesT c.σ.mem 0x80063b40 8).toNat
  quietMain : (bytesT c.σ.mem (ctx + 16#64 + 24#64).toNat 8).toNat ≤
    (bytesT c.σ.mem (ctx + 16#64 + 32#64).toNat 8).toNat
  /-- no `caml_scan_roots_hook` -/
  hookRead : ReadWindow 0x80064b18#64 8
  hookNone : bytesT c.σ.mem hookAddr 8 = 0#64

/-- The global scan's entry, as the tail reaches it from `c`. -/
structure ScanEntry (R : Nat → BitVec 64) (fsp s0 : BitVec 64) (c e : Config) : Prop where
  good : GoodState e.σ
  minstret : ∃ v, e.σ.regs.get? Register.minstret = some v
  tick : e.tick < 2
  code : TailCode e.σ.mem
  pc : PCAt LocalRootsSites.scanCall.target e
  registers : GHolds e.σ ((1, LocalRootsSites.scanCall.link) :: scanArgs R fsp s0)
  memory : e.σ.mem = c.σ.mem
  output : e.σ.sailOutput = c.σ.sailOutput

/-- What the tail needs back from the global scan: an ABI return keeping the
callee-saved registers, the code, and the words the tail reads next. -/
structure ScanBack (R : Nat → BitVec 64) (fsp s0 ctx : BitVec 64) (e d : Config) : Prop where
  good : GoodState d.σ
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  code : TailCode d.σ.mem
  pc : PCAt LocalRootsSites.scanCall.link d
  registers : GHolds d.σ (keptRegs R fsp s0)
  kept : ∀ w ∈ tailWords ctx fsp, bytesT d.σ.mem w 8 = bytesT e.σ.mem w 8
  output : d.σ.sailOutput = e.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ scratch, (gprReg n == r) = false) → d.σ.regs.get? r = e.σ.regs.get? r

/-- A state between the tail's pieces. -/
structure TStage (c0 : Config) (here : BitVec 64) (L : GRegs) (mem : Std.ExtHashMap Nat (BitVec 8)) (d : Config) :
    Prop where
  good : GoodState d.σ
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  code : TailCode d.σ.mem
  pc : PCAt here d
  regs : GHolds d.σ L
  memory : d.σ.mem = mem
  output : d.σ.sailOutput = c0.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ tailWrites, (gprReg n == r) = false) → d.σ.regs.get? r = c0.σ.regs.get? r

/-! ## The stages -/

theorem stage_exit {R dom fsp s0 ra0 s0o s1o s2o ctx c0} (input : TailInput R dom fsp s0 ra0 s0o s1o s2o ctx c0) :
    ∃ d, Steps c0 d ∧ TStage c0 LocalRootsSites.scanCall.pc (scanArgs R fsp s0) c0.σ.mem d := by
  have access := exit_access R dom fsp s0 c0.σ.mem input.localRead input.localNone
  have facts := chainPlan_facts (exit_code input.code.localRoots) access
  obtain ⟨d, run, post⟩ := (block_summary exitBlocks exitPc (exitRegs R dom fsp s0)
    [read8 c0.σ.mem (dom + 288#64).toNat] c0
    ⟨input.good, input.minstret, input.registers, by change KeysOK [15, 2, 8, 9, 19, 20, 21, 22, 23, 24, 25]; decide,
      facts, exit_chain_ok, input.tick⟩).run c0 ⟨input.pc, rfl⟩
  have holds := post.regs
  rw [exit_eval_regs] at holds
  unfold atScan at holds
  rw [read8_value, input.localNone] at holds
  refine ⟨d, run, post.good, post.minstret, post.tick, input.code.after facts post, ?_, ?_, ?_, post.output, ?_⟩
  · rw [PCAt, post.pc, exit_eval_pc]
  · apply gholds_select holds
    intro n v member
    simp only [scanArgs, calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl
  · rw [post.memory, exit_eval_log]; rfl
  · intro r noise out
    exact post.frame r noise (fun n hn => out n (by revert n hn; decide))

theorem stage_scan {R fsp s0 ctx c0 d} {Effect : Config → Config → Prop}
    (st : TStage c0 LocalRootsSites.scanCall.pc (scanArgs R fsp s0) c0.σ.mem d)
    (scan : ∀ e, ScanEntry R fsp s0 c0 e →
      FnSummary LocalRootsSites.scanCall.target (fun x => x = e) (fun x => ScanBack R fsp s0 ctx e x ∧ Effect e x)) :
    ∃ e d', Steps d d' ∧ ScanEntry R fsp s0 c0 e ∧ ScanBack R fsp s0 ctx e d' ∧ Effect e d' ∧
      TStage c0 LocalRootsSites.finalCall.pc (keptRegs R fsp s0) d'.σ.mem d' := by
  obtain ⟨e, run1, called⟩ := (call_summary LocalRootsSites.scanCall_shape LocalRootsSites.scanCall_decode d
    (LocalRootsSites.scanCall_pins st.code.localRoots) st.good st.tick st.minstret (scanArgs R fsp s0) st.regs
    (by change KeysOK [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]; decide)
    (by change ∀ n ∈ [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25], n ≠ 1; decide)).run d ⟨st.pc, rfl⟩
  have same : e.σ.mem = d.σ.mem := by rw [called.mem]; rfl
  have entry : ScanEntry R fsp s0 c0 e :=
    ⟨called.good, called.minstret, called.tick, by rw [same]; exact st.code, called.pc,
      ⟨called.ra, called.registers⟩, by rw [same, st.memory], called.output.trans st.output⟩
  obtain ⟨d', run2, back, effect⟩ := (scan e entry).run e ⟨entry.pc, rfl⟩
  refine ⟨e, d', run1.trans run2, entry, back, effect, back.good, back.minstret, back.tick, back.code,
    by rw [show LocalRootsSites.finalCall.pc = LocalRootsSites.scanCall.link by decide]; exact back.pc,
    back.registers, rfl, back.output.trans entry.output, ?_⟩
  intro r noise out
  rw [back.frame r noise (fun n hn => out n (by revert n hn; decide)),
    called.frame r noise (fun n hn => by change n ∈ ([] : List Nat) at hn; cases hn) (out 1 (by decide))]
  exact st.frame r noise out

def finalLog (fsp s0 : BitVec 64) : List WEntry :=
  FinalQuiet.entryLog fsp s0 StackScan.statePtr 0#64 LocalRootsSites.finalCall.link

theorem in_tailWords_static {ctx fsp : BitVec 64} {a : Nat} (h : a ∈ finalStatics ++ [hookAddr]) :
    a ∈ tailWords ctx fsp := by
  simp only [tailWords, List.mem_append] at h ⊢
  exact Or.inl (Or.inl h)

theorem in_tailWords_memprof {ctx fsp a : BitVec 64} (h : a ∈ MemprofQuiet.reads ctx) :
    a.toNat ∈ tailWords ctx fsp := by
  simp only [tailWords, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map_of_mem h))

theorem in_tailWords_frame {ctx fsp : BitVec 64} {k : Nat} (h : k ∈ [16, 24, 32, 40]) :
    (fsp + BitVec.ofNat 64 k).toNat ∈ tailWords ctx fsp := by
  simp only [tailWords, List.mem_append]
  refine Or.inr ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem keptRegs_split {σ : MState} {R : Nat → BitVec 64} {fsp s0 : BitVec 64}
    (four : GHolds σ [(2, fsp), (8, s0), (9, StackScan.statePtr), (18, 0#64)]) (callee : GHolds σ (calleeSaved R)) :
    GHolds σ (keptRegs R fsp s0) :=
  (gholds_append [(2, fsp), (8, s0), (9, StackScan.statePtr), (18, 0#64)] (calleeSaved R)).mpr ⟨four, callee⟩

theorem keptRegs_callee {σ : MState} {R : Nat → BitVec 64} {fsp s0 : BitVec 64}
    (holds : GHolds σ (keptRegs R fsp s0)) : GHolds σ (calleeSaved R) :=
  ((gholds_append [(2, fsp), (8, s0), (9, StackScan.statePtr), (18, 0#64)] (calleeSaved R)).mp holds).2

/-- `caml_final_oldify_young_roots`, no young finaliser. -/
theorem stage_final {R dom fsp s0 ra0 s0o s1o s2o ctx c0 d} {m : Std.ExtHashMap Nat (BitVec 8)}
    (input : TailInput R dom fsp s0 ra0 s0o s1o s2o ctx c0)
    (st : TStage c0 LocalRootsSites.finalCall.pc (keptRegs R fsp s0) m d)
    (same : ∀ w ∈ tailWords ctx fsp, bytesT m w 8 = bytesT c0.σ.mem w 8) :
    ∃ d', Steps d d' ∧ TStage c0 LocalRootsSites.memprofCall.pc (keptRegs R fsp s0) (writeLog m (finalLog fsp s0)) d' := by
  obtain ⟨e, run1, called⟩ := (call_summary LocalRootsSites.finalCall_shape LocalRootsSites.finalCall_decode d
    (LocalRootsSites.finalCall_pins st.code.localRoots) st.good st.tick st.minstret (keptRegs R fsp s0) st.regs
    (by change KeysOK [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]; decide)
    (by change ∀ n ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25], n ≠ 1; decide)).run d ⟨st.pc, rfl⟩
  have mem : e.σ.mem = m := by rw [called.mem, ← st.memory]; rfl
  have top := input.saves (1, 72) (by decide)
  have stat : ∀ a ∈ finalStatics, bytesT e.σ.mem a 8 = bytesT c0.σ.mem a 8 := fun a h => by
    rw [mem]; exact same a (in_tailWords_static (List.mem_append_left _ h))
  have holdsE : GHolds e.σ ((1, LocalRootsSites.finalCall.link) :: keptRegs R fsp s0) := ⟨called.ra, called.registers⟩
  have finalInput : FinalQuiet.Input fsp s0 StackScan.statePtr 0#64 LocalRootsSites.finalCall.link e :=
    { good := called.good, minstret := called.minstret, tick := called.tick
      code := by rw [mem, ← st.memory]; exact st.code.final
      registers := by
        apply gholds_select holdsE
        intro n v member
        simp only [FinalQuiet.regs, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with h | h | h | h | h <;> cases h <;> rfl
      saves := input.finalSaves
      reads := input.finalReads
      outside := fun a h => final_out top (input.staticsApart a (List.mem_append_left _ h))
      quietFirst := by rw [stat _ (by decide), stat _ (by decide)]; exact input.quietFirst
      quietLast := by rw [stat _ (by decide), stat _ (by decide)]; exact input.quietLast
      aligned := by decide }
  have target : LocalRootsSites.finalCall.target = FinalQuiet.pc := by decide
  obtain ⟨d', run2, post⟩ := (FinalQuiet.call finalInput).run e ⟨by rw [← target]; exact called.pc, rfl⟩
  have callee := callee_kept (R := R) post.frame (fun n hn => by revert n hn; decide)
    (keptRegs_callee called.registers)
  have high : ∀ x ∈ finalLog fsp s0, Layout.sym_tohost + 16 ≤ x.1 := by
    unfold finalLog
    rw [FinalQuiet.entryLog_bank]
    exact SaveBank.high (fun cell hc => input.finalSaves cell.2 (by revert cell hc; decide))
  refine ⟨d', run1.trans run2, post.good, post.minstret, post.tick, ?_, ?_, keptRegs_split post.registers callee, ?_,
    post.output.trans (called.output.trans st.output), ?_⟩
  · rw [post.memory, mem, ← st.memory]
    exact st.code.writeLog high
  · rw [show LocalRootsSites.memprofCall.pc = LocalRootsSites.finalCall.link by decide]; exact post.pc
  · rw [post.memory, mem]; rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide)),
      called.frame r noise (fun n hn => by change n ∈ ([] : List Nat) at hn; cases hn) (out 1 (by decide))]
    exact st.frame r noise out

def memprofIdx (m : Std.ExtHashMap Nat (BitVec 8)) (fsp s0 : BitVec 64) : BitVec 64 :=
  bytesT (writeLog m (finalLog fsp s0)) 0x80063b40 8

def memprofLog (m : Std.ExtHashMap Nat (BitVec 8)) (fsp s0 : BitVec 64) : List WEntry :=
  MemprofQuiet.bankLog fsp StackScan.statePtr 0#64 LocalRootsSites.memprofCall.link (memprofIdx m fsp s0)

/-- A word the tail reads, apart from the finaliser's saves, reads as at the loop exit. -/
theorem through_final {R dom fsp s0 ra0 s0o s1o s2o ctx c0} {m : Std.ExtHashMap Nat (BitVec 8)} {w : Nat}
    (input : TailInput R dom fsp s0 ra0 s0o s1o s2o ctx c0)
    (same : ∀ w ∈ tailWords ctx fsp, bytesT m w 8 = bytesT c0.σ.mem w 8) (member : w ∈ tailWords ctx fsp)
    (apart : w + 8 ≤ (MemprofQuiet.low fsp).toNat ∨ (MemprofQuiet.low fsp).toNat + 80 ≤ w) :
    bytesT (writeLog m (finalLog fsp s0)) w 8 = bytesT c0.σ.mem w 8 := by
  unfold finalLog
  rw [bytesT_writeLog_out _ (final_out (input.saves (1, 72) (by decide)) apart)]
  exact same w member

/-- `caml_memprof_oldify_young_roots`, memprof idle. -/
theorem stage_memprof {R dom fsp s0 ra0 s0o s1o s2o ctx c0 d} {m : Std.ExtHashMap Nat (BitVec 8)}
    (input : TailInput R dom fsp s0 ra0 s0o s1o s2o ctx c0)
    (st : TStage c0 LocalRootsSites.memprofCall.pc (keptRegs R fsp s0) (writeLog m (finalLog fsp s0)) d)
    (same : ∀ w ∈ tailWords ctx fsp, bytesT m w 8 = bytesT c0.σ.mem w 8) :
    ∃ d', Steps d d' ∧ TStage c0 hookPc (keptRegs R fsp s0)
      (writeLog (writeLog m (finalLog fsp s0)) (memprofLog m fsp s0)) d' := by
  obtain ⟨e, run1, called⟩ := (call_summary LocalRootsSites.memprofCall_shape LocalRootsSites.memprofCall_decode d
    (LocalRootsSites.memprofCall_pins st.code.localRoots) st.good st.tick st.minstret (keptRegs R fsp s0) st.regs
    (by change KeysOK [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]; decide)
    (by change ∀ n ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25], n ≠ 1; decide)).run d ⟨st.pc, rfl⟩
  have mem : e.σ.mem = writeLog m (finalLog fsp s0) := by rw [called.mem, ← st.memory]; rfl
  have word : ∀ a ∈ MemprofQuiet.reads ctx, bytesT e.σ.mem a.toNat 8 = bytesT c0.σ.mem a.toNat 8 := fun a h => by
    rw [mem]; exact through_final input same (in_tailWords_memprof h) (input.memprofApart a h)
  have r40 : (0x80063b40#64 : BitVec 64) ∈ MemprofQuiet.reads ctx := MemprofQuiet.mem_reads (Or.inl rfl)
  have r38 : (0x80063b38#64 : BitVec 64) ∈ MemprofQuiet.reads ctx := MemprofQuiet.mem_reads (Or.inr (Or.inl rfl))
  have rHook : (0x800648d0#64 : BitVec 64) ∈ MemprofQuiet.reads ctx :=
    MemprofQuiet.mem_reads (Or.inr (Or.inr (Or.inl rfl)))
  have rLocal : (0x800648d8#64 : BitVec 64) ∈ MemprofQuiet.reads ctx :=
    MemprofQuiet.mem_reads (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have r32 := MemprofQuiet.mem_reads (ctx := ctx) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have r24 := MemprofQuiet.mem_reads (ctx := ctx) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have holdsE : GHolds e.σ ((1, LocalRootsSites.memprofCall.link) :: keptRegs R fsp s0) :=
    ⟨called.ra, called.registers⟩
  have memprofInput : MemprofQuiet.Input fsp StackScan.statePtr 0#64 LocalRootsSites.memprofCall.link ctx e :=
    { good := called.good, minstret := called.minstret, tick := called.tick
      code := by rw [called.mem]; exact st.code.memprof
      registers := by
        apply gholds_select holdsE
        intro n v member
        simp only [MemprofQuiet.regs, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with h | h | h | h <;> cases h <;> rfl
      saves := input.saves
      windows := input.memprofReads
      apart := input.memprofApart
      hook := by rw [show MemprofQuiet.hookAddr = (0x800648d0#64 : BitVec 64).toNat from rfl, word _ rHook]; exact input.hook
      context := by
        rw [show MemprofQuiet.localAddr = (0x800648d8#64 : BitVec 64).toNat from rfl, word _ rLocal]; exact input.context
      quietGlobal := by
        rw [show (0x80063b38 : Nat) = (0x80063b38#64 : BitVec 64).toNat from rfl,
          show (0x80063b40 : Nat) = (0x80063b40#64 : BitVec 64).toNat from rfl, word _ r38, word _ r40]
        exact input.quietGlobal
      quietMain := by rw [word _ r24, word _ r32]; exact input.quietMain
      aligned := by decide }
  have target : LocalRootsSites.memprofCall.target = MemprofQuiet.pc := by decide
  obtain ⟨d', run2, post⟩ := (MemprofQuiet.call memprofInput).run e ⟨by rw [← target]; exact called.pc, rfl⟩
  have callee := callee_kept (R := R) post.frame (fun n hn => by revert n hn; decide)
    (keptRegs_callee called.registers)
  have s0kept : gprGet d'.σ 8 = some s0 := by
    have h := post.frame (gprReg 8) (by decide) (fun n hn => gprReg_beq_false n
      (by revert n hn; decide) 8 (by decide) (by revert n hn; decide) (by decide) (by revert n hn; decide))
    have before : gprGet e.σ 8 = some s0 := gholds_lookup _ called.registers rfl
    exact h.trans before
  have four : GHolds d'.σ [(2, fsp), (8, s0), (9, StackScan.statePtr), (18, 0#64)] := by
    obtain ⟨h2, h9, h18, -⟩ := post.registers
    exact ⟨h2, s0kept, h9, h18, trivial⟩
  have high : ∀ x ∈ memprofLog m fsp s0, Layout.sym_tohost + 16 ≤ x.1 := by
    unfold memprofLog MemprofQuiet.bankLog
    exact SaveBank.high input.saves
  refine ⟨d', run1.trans run2, post.good, post.minstret, post.tick, ?_, ?_, keptRegs_split four callee, ?_,
    post.output.trans (called.output.trans st.output), ?_⟩
  · rw [post.memory, mem]
    exact (st.memory ▸ st.code).writeLog high
  · rw [show hookPc = LocalRootsSites.memprofCall.link by decide]; exact post.pc
  · rw [post.memory, mem]; rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide)),
      called.frame r noise (fun n hn => by change n ∈ ([] : List Nat) at hn; cases hn) (out 1 (by decide))]
    exact st.frame r noise out

/-- The tail's result: returned to the caller's `ra` with the frame restored. -/
structure TailPost (R : Nat → BitVec 64) (fsp ra0 s0o s1o s2o : BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8))
    (c0 after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : PCAt ra0 after
  registers : GHolds after.σ ([(2, fsp + 48#64), (1, ra0), (8, s0o), (9, s1o), (18, s2o)] ++ calleeSaved R)
  memory : after.σ.mem = mem
  output : after.σ.sailOutput = c0.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ tailWrites, (gprReg n == r) = false) → after.σ.regs.get? r = c0.σ.regs.get? r

/-- `caml_scan_roots_hook` is NULL: restore the frame and return. -/
theorem stage_hook {R dom fsp s0 ra0 s0o s1o s2o ctx c0 d} {m : Std.ExtHashMap Nat (BitVec 8)}
    (input : TailInput R dom fsp s0 ra0 s0o s1o s2o ctx c0)
    (st : TStage c0 hookPc (keptRegs R fsp s0) (writeLog (writeLog m (finalLog fsp s0)) (memprofLog m fsp s0)) d)
    (same : ∀ w ∈ tailWords ctx fsp, bytesT m w 8 = bytesT c0.σ.mem w 8) :
    ∃ d', Steps d d' ∧ TailPost R fsp ra0 s0o s1o s2o
      (writeLog (writeLog m (finalLog fsp s0)) (memprofLog m fsp s0)) c0 d' := by
  have top := input.saves (1, 72) (by decide)
  have through : ∀ w ∈ tailWords ctx fsp,
      (w + 8 ≤ (MemprofQuiet.low fsp).toNat ∨ (MemprofQuiet.low fsp).toNat + 80 ≤ w) →
      bytesT d.σ.mem w 8 = bytesT c0.σ.mem w 8 := fun w member apart => by
    rw [st.memory, memprofLog, MemprofQuiet.bankLog,
      bytesT_writeLog_out _ (MemprofQuiet.bank_out top (by decide) apart)]
    exact through_final input same member apart
  have frameWord : ∀ k ∈ [16, 24, 32, 40], bytesT d.σ.mem (fsp + BitVec.ofNat 64 k).toNat 8 =
      bytesT c0.σ.mem (fsp + BitVec.ofNat 64 k).toNat 8 := fun k h =>
    through _ (in_tailWords_frame h) (word_apart (by revert k h; decide)
      (input.frameWords k (by revert k h; decide)))
  have hookWord : bytesT d.σ.mem hookAddr 8 = 0#64 := by
    rw [through _ (in_tailWords_static (by decide)) (input.staticsApart _ (by decide))]
    exact input.hookNone
  have w40 : bytesT d.σ.mem (fsp + 40#64).toNat 8 = ra0 := (frameWord 40 (by decide)).trans input.savedRa
  have w32 : bytesT d.σ.mem (fsp + 32#64).toNat 8 = s0o := (frameWord 32 (by decide)).trans input.savedS0
  have w24 : bytesT d.σ.mem (fsp + 24#64).toNat 8 = s1o := (frameWord 24 (by decide)).trans input.savedS1
  have w16 : bytesT d.σ.mem (fsp + 16#64).toNat 8 = s2o := (frameWord 16 (by decide)).trans input.savedS2
  have access := hook_access fsp ra0 d.σ.mem input.hookRead hookWord input.frameWords w40 input.aligned
  have facts := chainPlan_facts (hook_code st.code.localRoots) access
  have sp : GHolds d.σ [(2, fsp)] := ⟨st.regs.1, trivial⟩
  obtain ⟨d', run, post⟩ := (block_summary hookBlocks hookPc [(2, fsp)] _ d
    ⟨st.good, st.minstret, sp, by change KeysOK [2]; decide, facts, hook_chain_ok, st.tick⟩).run d ⟨st.pc, rfl⟩
  have holds := post.regs
  rw [hook_eval_regs] at holds
  unfold restored at holds
  rw [read8_value, read8_value, read8_value, read8_value, w40, w32, w24, w16] at holds
  have callee := callee_kept (R := R) post.frame (fun n hn => by revert n hn; decide) (keptRegs_callee st.regs)
  have five : GHolds d'.σ [(2, fsp + 48#64), (1, ra0), (8, s0o), (9, s1o), (18, s2o)] := by
    apply gholds_select holds
    intro n v member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h <;> cases h <;> rfl
  refine ⟨d', run, post.good, post.minstret, post.tick, ?_, (gholds_append _ _).mpr ⟨five, callee⟩, ?_,
    post.output.trans st.output, ?_⟩
  · rw [PCAt, post.pc, hook_eval_pc _ _ _ _ _ _ _ (by rw [read8_value, w40]) input.aligned]
  · rw [post.memory, hook_eval_log, ← st.memory]; rfl
  · intro r noise out
    rw [post.frame r noise (fun n hn => out n (by revert n hn; decide))]
    exact st.frame r noise out

/-- **The tail of `caml_oldify_local_roots`** from the VM-stack loop's exit to
its return, for any global scan supplied at its call (`scan`, with result
relation `Effect`): no local C roots, no young finaliser, memprof idle, no
scan hook. Memory is the scan's result with the two callees' stack saves. -/
theorem tail {R dom fsp s0 ra0 s0o s1o s2o ctx c} {Effect : Config → Config → Prop}
    (input : TailInput R dom fsp s0 ra0 s0o s1o s2o ctx c)
    (scan : ∀ e, ScanEntry R fsp s0 c e →
      FnSummary LocalRootsSites.scanCall.target (fun x => x = e) (fun x => ScanBack R fsp s0 ctx e x ∧ Effect e x)) :
    FnSummary exitPc (fun d => d = c) (fun after => ∃ e d, ScanEntry R fsp s0 c e ∧ ScanBack R fsp s0 ctx e d ∧
      Effect e d ∧ TailPost R fsp ra0 s0o s1o s2o
        (writeLog (writeLog d.σ.mem (finalLog fsp s0)) (memprofLog d.σ.mem fsp s0)) c after) := by
  constructor
  rintro c0 ⟨pcAt, rfl⟩
  obtain ⟨d1, run1, st1⟩ := stage_exit input
  obtain ⟨e, d2, run2, entry, back, effect, st2⟩ := stage_scan st1 scan
  have same : ∀ w ∈ tailWords ctx fsp, bytesT d2.σ.mem w 8 = bytesT c0.σ.mem w 8 := fun w h => by
    rw [back.kept w h, entry.memory]
  obtain ⟨d3, run3, st3⟩ := stage_final input st2 same
  obtain ⟨d4, run4, st4⟩ := stage_memprof input st3 same
  obtain ⟨d5, run5, post⟩ := stage_hook input st4 same
  exact ⟨d5, run1.trans (run2.trans (run3.trans (run4.trans run5))), e, d2, entry, back, effect, post⟩

end OCaml.Vm.Gc.LocalRootsTail
