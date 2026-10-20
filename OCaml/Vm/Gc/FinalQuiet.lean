import OCaml.Vm.Gc.Generated.FinalYoungRoots
import OCaml.Vm.Gc.ChainPlan
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.SaveBank
import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Primitives.MemoryFrame
import Vsa.Sim.GRegsFrame
import Vsa.Sim.ChainFactsTac

/-! # `caml_final_oldify_young_roots` with no young finalisers

When `finalisable_first.old ≥ finalisable_first.young` and likewise for
`finalisable_last` (no finaliser registered since the last minor collection),
the call saves four registers, tests both bounds, restores and returns
(blocks `0x800242a0` taken, `0x80024308` taken, `0x80024340`). -/
namespace OCaml.Vm.Gc.FinalQuiet
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def entryBlock : BBlock := caml_final_oldify_young_rootsX42a0TSeg.getD 0 {body := [], term := none}
def lastBlock : BBlock := caml_final_oldify_young_rootsX4308TSeg.getD 0 {body := [], term := none}
def retBlock : BBlock := caml_final_oldify_young_rootsX4340Seg.getD 0 {body := [], term := none}
def blocks := [entryBlock, lastBlock, retBlock]
def pc : BitVec 64 := 0x800242a0#64

/-- `finalisable_first`; `finalisable_last` follows it at `+32`. -/
def table : BitVec 64 := 0x8006c058#64

def regs (sp s0 s1 s2 ra : BitVec 64) : GRegs := [(2, sp), (8, s0), (9, s1), (18, s2), (1, ra)]

theorem chain_ok : ChainOK pc [2, 8, 9, 18, 1] blocks := by decide

theorem code_facts {mem : Std.ExtHashMap Nat (BitVec 8)} (hc : Code.Caml_final_oldify_young_rootsLoaded mem) :
    ChainCode mem blocks := by
  intro b hb
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [entryBlock, lastBlock, retBlock, caml_final_oldify_young_rootsX42a0TSeg,
    caml_final_oldify_young_rootsX4308TSeg, caml_final_oldify_young_rootsX4340Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts hc with "Vsa.Sim.Code.caml_final_oldify_young_roots_at_"

/-- The native frame. -/
def frame (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551584#64

def entryLog (sp s0 s1 s2 ra : BitVec 64) : List WEntry :=
  [((frame sp + 16#64).toNat, 8, s0), ((frame sp + 24#64).toNat, 8, ra),
   ((frame sp + 8#64).toNat, 8, s1), ((frame sp + 0#64).toNat, 8, s2)]

def afterEntry (fsp s1 ra : BitVec 64) (l1 l2 : List (BitVec 8)) : GRegs :=
  [(15, bytesVal .ld l2), (18, bytesVal .ld l1), (8, table), (2, fsp), (9, s1), (1, ra)]

theorem entry_log (sp s0 s1 s2 ra : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM entryBlock.body (regs sp s0 s1 s2 ra) lds = entryLog sp s0 s1 s2 ra := rfl

theorem entry_regs (sp s0 s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM entryBlock.body (regs sp s0 s1 s2 ra) (l1 :: l2 :: rest) = afterEntry (frame sp) s1 ra l1 l2 := by
  simp [entryBlock, caml_final_oldify_young_rootsX42a0TSeg, regs, afterEntry, frame, table,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

def afterLast (fsp s1 ra : BitVec 64) (l3 l4 : List (BitVec 8)) : GRegs :=
  [(15, bytesVal .ld l4), (18, bytesVal .ld l3), (8, table), (2, fsp), (9, s1), (1, ra)]

theorem last_regs (fsp s1 ra : BitVec 64) (l1 l2 l3 l4 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM lastBlock.body (afterEntry fsp s1 ra l1 l2) (l3 :: l4 :: rest) = afterLast fsp s1 ra l3 l4 := by
  simp [lastBlock, caml_final_oldify_young_rootsX4308TSeg, afterEntry, afterLast,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem last_log (fsp s1 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    wlogM lastBlock.body (afterEntry fsp s1 ra l1 l2) lds = [] := rfl

def restored (fsp : BitVec 64) (l4 r1 r2 r3 r4 : List (BitVec 8)) : GRegs :=
  [(2, fsp + 32#64), (18, bytesVal .ld r4), (9, bytesVal .ld r3), (8, bytesVal .ld r2),
   (1, bytesVal .ld r1), (15, bytesVal .ld l4)]

theorem ret_regs (fsp s1 ra : BitVec 64) (l3 l4 r1 r2 r3 r4 : List (BitVec 8)) :
    runGM retBlock.body (afterLast fsp s1 ra l3 l4) [r1, r2, r3, r4] = restored fsp l4 r1 r2 r3 r4 := by
  simp [retBlock, caml_final_oldify_young_rootsX4340Seg, afterLast, restored,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem ret_log (fsp s1 ra : BitVec 64) (l3 l4 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    wlogM retBlock.body (afterLast fsp s1 ra l3 l4) lds = [] := rfl

theorem entry_control (sp s0 s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (quiet : (bytesVal .ld l2).toNat ≤ (bytesVal .ld l1).toNat) :
    TermFactsO (runGM entryBlock.body (regs sp s0 s1 s2 ra) (l1 :: l2 :: rest)) entryBlock.term := by
  rw [entry_regs]
  simpa [entryBlock, caml_final_oldify_young_rootsX42a0TSeg, TermFactsO, TermFactsT, afterEntry, srcVal, lookupG,
    guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt] using quiet

theorem last_control (fsp s1 ra : BitVec 64) (l1 l2 l3 l4 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (quiet : (bytesVal .ld l4).toNat ≤ (bytesVal .ld l3).toNat) :
    TermFactsO (runGM lastBlock.body (afterEntry fsp s1 ra l1 l2) (l3 :: l4 :: rest)) lastBlock.term := by
  rw [last_regs]
  simpa [lastBlock, caml_final_oldify_young_rootsX4308TSeg, TermFactsO, TermFactsT, afterLast, srcVal, lookupG,
    guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt] using quiet

theorem ret_control (fsp s1 ra : BitVec 64) (l3 l4 r1 r2 r3 r4 : List (BitVec 8))
    (aligned : (bytesVal .ld r1).toNat % 4 = 0) :
    TermFactsO (runGM retBlock.body (afterLast fsp s1 ra l3 l4) [r1, r2, r3, r4]) retBlock.term := by
  rw [ret_regs]
  exact return_facts _ rfl rfl rfl rfl aligned

theorem last_access (fsp s1 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (mm : Std.ExtHashMap Nat (BitVec 8))
    (rest : List (List (BitVec 8)))
    (r40 : ReadWindow 0x8006c080#64 8) (r48 : ReadWindow 0x8006c088#64 8) :
    AccessPlan mm (afterEntry fsp s1 ra l1 l2)
      (read8 mm 0x8006c080 :: read8 mm 0x8006c088 :: rest) lastBlock.body := by
  simp only [lastBlock, caml_final_oldify_young_rootsX4308TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · refine r40.ld rfl ?_ (read8_pins _ _)
    simp [afterEntry, table, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · refine r48.ld rfl ?_ (read8_pins _ _)
    simp [afterEntry, table, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]

theorem ret_access (fsp s1 ra : BitVec 64) (l3 l4 : List (BitVec 8)) (mm : Std.ExtHashMap Nat (BitVec 8))
    (windows : ∀ off ∈ [24, 16, 8, 0], ReadWindow (fsp + BitVec.ofNat 64 off) 8) :
    AccessPlan mm (afterLast fsp s1 ra l3 l4)
      [read8 mm (fsp + 24#64).toNat, read8 mm (fsp + 16#64).toNat,
       read8 mm (fsp + 8#64).toNat, read8 mm (fsp + 0#64).toNat] retBlock.body := by
  simp only [retBlock, caml_final_oldify_young_rootsX4340Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · refine (windows 24 (by decide)).ld rfl ?_ (read8_pins _ _)
    simp [afterLast, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
  · refine (windows 16 (by decide)).ld rfl ?_ (read8_pins _ _)
    simp [afterLast, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]
  · refine (windows 8 (by decide)).ld rfl ?_ (read8_pins _ _)
    simp [afterLast, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]
  · refine (windows 0 (by decide)).ld rfl ?_ (read8_pins _ _)
    simp [afterLast, eaddrM, mkLine, decodeM, srcVal, lookupG, stepGM, wvalM, eraseG,
      Functions.sign_extend, Sail.BitVec.signExtend]

/-- The registers after the saves and the `auipc`/`addi` of `s0`. -/
def prefixRegs (sp s1 s2 ra : BitVec 64) : GRegs := [(8, table), (2, frame sp), (9, s1), (18, s2), (1, ra)]

theorem prefix_regs (sp s0 s1 s2 ra : BitVec 64) (lds : List (List (BitVec 8))) :
    runGM (entryBlock.body.take 7) (regs sp s0 s1 s2 ra) lds = prefixRegs sp s1 s2 ra := by
  simp [entryBlock, caml_final_oldify_young_rootsX42a0TSeg, regs, prefixRegs, frame, table,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem prefix8_regs (sp s0 s1 s2 ra : BitVec 64) (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    runGM (entryBlock.body.take 8) (regs sp s0 s1 s2 ra) (l1 :: l2 :: rest) = (18, bytesVal .ld l1) :: [(8, table),
      (2, frame sp), (9, s1), (1, ra)] := by
  simp [entryBlock, caml_final_oldify_young_rootsX42a0TSeg, regs, frame, table,
    runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem entry_lds (l1 l2 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    ldsRunM entryBlock.body (l1 :: l2 :: rest) = rest := rfl

theorem last_lds (l3 l4 : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    ldsRunM lastBlock.body (l3 :: l4 :: rest) = rest := rfl

theorem entry_access (sp s0 s1 s2 ra : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (rest : List (List (BitVec 8)))
    (windows : ∀ off ∈ [16, 24, 8, 0], WriteWindow (frame sp + BitVec.ofNat 64 off) 8)
    (r8 : ReadWindow 0x8006c060#64 8) (r16 : ReadWindow 0x8006c068#64 8)
    (out8 : OutLRange (entryLog sp s0 s1 s2 ra) 0x8006c060 8)
    (out16 : OutLRange (entryLog sp s0 s1 s2 ra) 0x8006c068 8) :
    AccessPlan m (regs sp s0 s1 s2 ra) (read8 m 0x8006c060 :: read8 m 0x8006c068 :: rest) entryBlock.body := by
  simp only [entryBlock, caml_final_oldify_young_rootsX42a0TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact (windows 16 (by decide)).sd rfl rfl
  · exact (windows 24 (by decide)).sd rfl rfl
  · exact (windows 8 (by decide)).sd rfl rfl
  · exact (windows 0 (by decide)).sd rfl rfl
  · refine r8.ld rfl ?_ ?_
    · change eaddrM _ (runGM (entryBlock.body.take 7) (regs sp s0 s1 s2 ra) _) = _
      rw [prefix_regs]
      simp [prefixRegs, table, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
    · change LPins8 (memAfter m (entryBlock.body.take 7) (regs sp s0 s1 s2 ra) _) _ _
      rw [memAfter_eq, show wlogM (entryBlock.body.take 7) (regs sp s0 s1 s2 ra)
        (read8 m 0x8006c060 :: read8 m 0x8006c068 :: rest) = entryLog sp s0 s1 s2 ra from rfl]
      exact lpins8_writeLog (read8_pins m 0x8006c060) out8
  · refine r16.ld rfl ?_ ?_
    · change eaddrM _ (runGM (entryBlock.body.take 8) (regs sp s0 s1 s2 ra) (_ :: _ :: rest)) = _
      rw [prefix8_regs]
      simp [table, eaddrM, mkLine, decodeM, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]
    · change LPins8 (memAfter m (entryBlock.body.take 8) (regs sp s0 s1 s2 ra) _) _ _
      rw [memAfter_eq, show wlogM (entryBlock.body.take 8) (regs sp s0 s1 s2 ra)
        (read8 m 0x8006c060 :: read8 m 0x8006c068 :: rest) = entryLog sp s0 s1 s2 ra from rfl]
      exact lpins8_writeLog (read8_pins m 0x8006c068) out16

/-! ## The whole quiet call -/

def slots : List (Nat × Nat) := [(8, 16), (1, 24), (9, 8), (18, 0)]

/-- The caller's registers as a function, for the save bank. -/
def savedR (s0 s1 s2 ra : BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 8 then s0 else if n = 1 then ra else if n = 9 then s1 else s2

theorem entryLog_bank (sp s0 s1 s2 ra : BitVec 64) :
    entryLog sp s0 s1 s2 ra = SaveBank.log (frame sp) (savedR s0 s1 s2 ra) slots := rfl

def shape : SaveBank.Shape slots := ⟨(1, 24), by decide, by decide, by decide, by decide⟩

/-- Memory after the saves. -/
def savedMem (m : Std.ExtHashMap Nat (BitVec 8)) (sp s0 s1 s2 ra : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog m (entryLog sp s0 s1 s2 ra)

def loads (m : Std.ExtHashMap Nat (BitVec 8)) (sp s0 s1 s2 ra : BitVec 64) : List (List (BitVec 8)) :=
  [read8 m 0x8006c060, read8 m 0x8006c068,
   read8 (savedMem m sp s0 s1 s2 ra) 0x8006c080, read8 (savedMem m sp s0 s1 s2 ra) 0x8006c088,
   read8 (savedMem m sp s0 s1 s2 ra) (frame sp + 24#64).toNat, read8 (savedMem m sp s0 s1 s2 ra) (frame sp + 16#64).toNat,
   read8 (savedMem m sp s0 s1 s2 ra) (frame sp + 8#64).toNat, read8 (savedMem m sp s0 s1 s2 ra) (frame sp + 0#64).toNat]

/-- The quiet call's input. -/
structure Input (sp s0 s1 s2 ra : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_final_oldify_young_rootsLoaded c.σ.mem
  registers : GHolds c.σ (regs sp s0 s1 s2 ra)
  saves : ∀ off ∈ [16, 24, 8, 0], WriteWindow (frame sp + BitVec.ofNat 64 off) 8
  reads : ReadWindow 0x8006c060#64 8 ∧ ReadWindow 0x8006c068#64 8 ∧ ReadWindow 0x8006c080#64 8 ∧
    ReadWindow 0x8006c088#64 8
  outside : ∀ a ∈ [0x8006c060, 0x8006c068, 0x8006c080, 0x8006c088], OutLRange (entryLog sp s0 s1 s2 ra) a 8
  /-- no young finaliser: `old ≥ young` for both tables -/
  quietFirst : (bytesT c.σ.mem 0x8006c068 8).toNat ≤ (bytesT c.σ.mem 0x8006c060 8).toNat
  quietLast : (bytesT c.σ.mem 0x8006c088 8).toNat ≤ (bytesT c.σ.mem 0x8006c080 8).toNat
  aligned : ra.toNat % 4 = 0

structure Post (sp s0 s1 s2 ra : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : PCAt ra after
  registers : GHolds after.σ [(2, sp), (8, s0), (9, s1), (18, s2)]
  memory : after.σ.mem = writeLog before.σ.mem (entryLog sp s0 s1 s2 ra)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ wrChain blocks, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem saved_word {sp s0 s1 s2 ra : BitVec 64} (m : Std.ExtHashMap Nat (BitVec 8))
    (saves : ∀ off ∈ [16, 24, 8, 0], WriteWindow (frame sp + BitVec.ofNat 64 off) 8)
    (cell : Nat × Nat) (member : cell ∈ slots) :
    bytesT (savedMem m sp s0 s1 s2 ra) (frame sp + BitVec.ofNat 64 cell.2).toNat 8 = savedR s0 s1 s2 ra cell.1 := by
  have windows : ∀ c ∈ slots, WriteWindow (frame sp + BitVec.ofNat 64 c.2) 8 := by
    intro c hc
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals exact saves _ (by decide)
  rw [savedMem, entryLog_bank]
  exact shape.read m (frame sp) (savedR s0 s1 s2 ra) windows cell member

theorem frame_restore (sp : BitVec 64) : frame sp + 32#64 = sp := by
  rw [frame, BitVec.add_assoc]
  have : (18446744073709551584#64 + 32#64 : BitVec 64) = 0#64 := by decide
  rw [this, BitVec.add_zero]

/-- **`caml_final_oldify_young_roots` with no young finaliser**, entry to return. -/
theorem call {sp s0 s1 s2 ra c} (input : Input sp s0 s1 s2 ra c) :
    FnSummary pc (fun d => d = c) (Post sp s0 s1 s2 ra c) := by
  obtain ⟨r8, r16, r40, r48⟩ := input.reads
  have out := input.outside
  have w24 : bytesT (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 24#64).toNat 8 = ra :=
    saved_word c.σ.mem input.saves (1, 24) (by decide)
  have w16 : bytesT (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 16#64).toNat 8 = s0 :=
    saved_word c.σ.mem input.saves (8, 16) (by decide)
  have w8 : bytesT (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 8#64).toNat 8 = s1 :=
    saved_word c.σ.mem input.saves (9, 8) (by decide)
  have w0 : bytesT (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 0#64).toNat 8 = s2 :=
    saved_word c.σ.mem input.saves (18, 0) (by decide)
  have last40 : bytesT (writeLog c.σ.mem (entryLog sp s0 s1 s2 ra)) 0x8006c080 8 = bytesT c.σ.mem 0x8006c080 8 :=
    bytesT_writeLog_out _ (out _ (by decide))
  have last48 : bytesT (writeLog c.σ.mem (entryLog sp s0 s1 s2 ra)) 0x8006c088 8 = bytesT c.σ.mem 0x8006c088 8 :=
    bytesT_writeLog_out _ (out _ (by decide))
  have access : ChainAccess c.σ.mem (regs sp s0 s1 s2 ra) (loads c.σ.mem sp s0 s1 s2 ra) blocks := by
    apply ChainAccess.cons ⟨entry_access sp s0 s1 s2 ra c.σ.mem _ input.saves r8 r16 (out _ (by decide))
      (out _ (by decide)), entry_control sp s0 s1 s2 ra _ _ _ (by simpa only [read8_value] using input.quietFirst)⟩
    rw [entry_regs, entry_log, entry_lds]
    simp only [savedMem]
    apply ChainAccess.cons ⟨last_access _ s1 ra _ _ (writeLog c.σ.mem (entryLog sp s0 s1 s2 ra)) _ r40 r48,
      last_control _ s1 ra _ _ _ _ _ (by rw [read8_value, read8_value, last40, last48]; exact input.quietLast)⟩
    rw [last_regs, last_log, last_lds]
    rw [show ∀ m : Std.ExtHashMap Nat (BitVec 8), writeLog m [] = m from fun _ => rfl]
    exact ChainAccess.cons ⟨ret_access _ s1 ra _ _ (writeLog c.σ.mem (entryLog sp s0 s1 s2 ra))
      (fun off h => (input.saves off (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        omega)).read),
      ret_control _ s1 ra _ _ _ _ _ _ (by rw [read8_value, ← savedMem, w24]; exact input.aligned)⟩ ChainAccess.nil
  have facts := chainPlan_facts (code_facts input.code) access
  have summary := block_summary blocks pc (regs sp s0 s1 s2 ra) (loads c.σ.mem sp s0 s1 s2 ra) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2, 8, 9, 18, 1]; decide, facts, chain_ok,
      input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have regsEq : (evalBlocks blocks (SegEvalState.init (regs sp s0 s1 s2 ra) (loads c.σ.mem sp s0 s1 s2 ra))).regs =
      restored (frame sp) (read8 (savedMem c.σ.mem sp s0 s1 s2 ra) 0x8006c088)
        (read8 (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 24#64).toNat)
        (read8 (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 16#64).toNat)
        (read8 (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 8#64).toNat)
        (read8 (savedMem c.σ.mem sp s0 s1 s2 ra) (frame sp + 0#64).toNat) := by
    simp only [blocks, evalBlocks, evalBlock, SegEvalState.init, loads, entry_regs, entry_lds, last_regs, last_lds,
      ret_regs]
  have logEq : (evalBlocks blocks (SegEvalState.init (regs sp s0 s1 s2 ra) (loads c.σ.mem sp s0 s1 s2 ra))).log =
      entryLog sp s0 s1 s2 ra := by
    simp only [blocks, evalBlocks, evalBlock, SegEvalState.init, loads, entry_regs, entry_lds, last_regs, last_lds,
      entry_log, last_log, ret_log, List.append_nil, List.nil_append]
  have pcEq : evalBlocksPC pc (SegEvalState.init (regs sp s0 s1 s2 ra) (loads c.σ.mem sp s0 s1 s2 ra)) blocks = ra := by
    simp only [blocks, evalBlocksPC, SegEvalState.init, chainEndPC, loads, entry_regs, entry_lds,
      last_regs, last_lds]
    change Sail.BitVec.update (srcVal 1 (runGM retBlock.body (afterLast (frame sp) s1 ra _ _) [_, _, _, _]) + 0#64)
      0 0#1 = _
    rw [ret_regs]
    change Sail.BitVec.update (bytesVal .ld _ + 0#64) 0 0#1 = _
    rw [read8_value, w24]
    exact ret_tgt _ input.aligned
  have holds := post.regs
  rw [regsEq] at holds
  have stack := frame_restore sp
  refine ⟨post.good, post.minstret, post.tick, ?_, ?_, ?_, post.output, post.frame⟩
  · rw [PCAt, post.pc, pcEq]
  · apply gholds_select holds
    intro n v member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h <;> cases h
    · show lookupG 2 (restored _ _ _ _ _ _) = _
      rw [show ∀ fsp l4 r1 r2 r3 r4, lookupG 2 (restored fsp l4 r1 r2 r3 r4) = some (fsp + 32#64)
        from fun _ _ _ _ _ _ => rfl, stack]
    · show lookupG 8 (restored _ _ _ _ _ _) = _
      rw [show ∀ fsp l4 r1 r2 r3 r4, lookupG 8 (restored fsp l4 r1 r2 r3 r4) = some (bytesVal .ld r2)
        from fun _ _ _ _ _ _ => rfl, read8_value, w16]
    · show lookupG 9 (restored _ _ _ _ _ _) = _
      rw [show ∀ fsp l4 r1 r2 r3 r4, lookupG 9 (restored fsp l4 r1 r2 r3 r4) = some (bytesVal .ld r3)
        from fun _ _ _ _ _ _ => rfl, read8_value, w8]
    · show lookupG 18 (restored _ _ _ _ _ _) = _
      rw [show ∀ fsp l4 r1 r2 r3 r4, lookupG 18 (restored fsp l4 r1 r2 r3 r4) = some (bytesVal .ld r4)
        from fun _ _ _ _ _ _ => rfl, read8_value, w0]
  · rw [post.memory, logEq]

end OCaml.Vm.Gc.FinalQuiet
