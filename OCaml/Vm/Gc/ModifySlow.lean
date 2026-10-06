import OCaml.Vm.Gc.Generated.Modify
import OCaml.Vm.Gc.ChainPlan
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Layout
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.ElfDecode.Part000
import Vsa.Sim.ElfDecode.Part001
import Vsa.Sim.ElfDecode.Part006
import Vsa.Sim.ElfDecode.Part007
import Vsa.Sim.ElfDecode.Part008
import Vsa.Sim.ElfDecode.Part010
import Vsa.Sim.ElfDecode.Part017
import Vsa.Sim.ElfDecode.Part019
import Vsa.Sim.ElfDecode.Part029
import Vsa.Sim.ElfDecode.Part030
import Vsa.Sim.ElfDecode.Part033
import Vsa.Sim.ElfDecode.Part035
import Vsa.Sim.ElfDecode.Part037
import Vsa.Sim.ElfDecode.Part041
import Vsa.Sim.ElfDecode.Part043
import Vsa.Sim.ElfDecode.Part044
import Vsa.Sim.ElfDecode.Part046
import Vsa.Sim.ElfDecode.Part048
import Vsa.Sim.ElfDecode.Part059
import Vsa.Sim.ElfDecode.Part060
import Vsa.Sim.ElfDecode.Part064
import Vsa.Sim.ElfDecode.Part066
import Vsa.Sim.ElfDecode.Part067
import Vsa.Sim.ElfDecode.Part070
import Vsa.Sim.ElfDecode.Part072
import Vsa.Sim.ElfDecode.Part073
import Vsa.Sim.ElfDecode.Part080
import Vsa.Sim.ElfDecode.Part082
import Vsa.Sim.ElfDecode.Part088
import Vsa.Sim.ElfDecode.Part099
import Vsa.Sim.ElfDecode.Part126
import Vsa.Sim.ElfDecode.Part132
import Vsa.Sim.ElfDecode.Part214
import Vsa.Sim.ElfDecode.Part215
import Vsa.Sim.ElfDecode.Part217
import Vsa.Sim.ElfDecode.Part220

/-!
# `caml_modify`: the slow insertion route up to the realloc call

The route a young value stored into a major slot takes when the remembered
set has no room (in F1: unallocated at the cut): `a9a8`(slot major) →
`a9cc`(old immediate) → `aa0c`,`aa14`,`aa20`(value young) → `aa28`(table
full) → `aa7c`, parked at the `jal caml_realloc_ref_table`.
-/

-- Kernel checking of the generated instruction literals (decodeM on the
-- pinned words), as in `Generated/Modify.lean`.
set_option maxRecDepth 100000

namespace OCaml.Vm.Gc.ModifySlow
open Vsa.Sim Vsa.Machine OCaml.Vm.Primitives LeanRV64DExecutable

def slotBlock : BBlock := caml_modifyXa9a8TSeg.getD 0 { body := [], term := none }
def oldBlock : BBlock := caml_modifyXa9ccTSeg.getD 0 { body := [], term := none }
def immBlock : BBlock := caml_modifyXaa0cFSeg.getD 0 { body := [], term := none }
def endBlock : BBlock := caml_modifyXaa14FSeg.getD 0 { body := [], term := none }
def startBlock : BBlock := caml_modifyXaa20FSeg.getD 0 { body := [], term := none }
def tableBlock : BBlock := caml_modifyXaa28TSeg.getD 0 { body := [], term := none }
def callBlock : BBlock := caml_modifyXaa7cSeg.getD 0 { body := [], term := none }
def blocks := [slotBlock, oldBlock, immBlock, endBlock, startBlock, tableBlock, callBlock]
def pc : BitVec 64 := 0x8000a9a8#64

/-- Entry registers: slot `a0`, value `a1`, return address, stack pointer. -/
def regs (fp v ra sp : BitVec 64) : GRegs := [(10, fp), (11, v), (1, ra), (2, sp)]

theorem chain_ok : ChainOK pc [10, 11, 1, 2] blocks := by decide

theorem code_facts {mem : Std.ExtHashMap Nat (BitVec 8)}
    (code : Code.Caml_modifyLoaded mem) : ChainCode mem blocks := by
  intro b member
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [slotBlock, oldBlock, immBlock, endBlock, startBlock, tableBlock, callBlock,
    caml_modifyXa9a8TSeg, caml_modifyXa9ccTSeg, caml_modifyXaa0cFSeg, caml_modifyXaa14FSeg,
    caml_modifyXaa20FSeg, caml_modifyXaa28TSeg, caml_modifyXaa7cSeg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts code with "Vsa.Sim.Code.caml_modify_at_"

/-- The `Caml_state` symbol address (`auipc a3 ; addi a3`). -/
def stateSym : BitVec 64 := BitVec.ofNat 64 Layout.sym_Caml_state

def sloted (fp v ra sp dom ye : BitVec 64) : GRegs :=
  [(14, ye), (15, dom), (13, stateSym), (10, fp), (11, v), (1, ra), (2, sp)]

theorem slot_regs (fp v ra sp : BitVec 64) (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    runGM slotBlock.body (regs fp v ra sp) (b1::b2::lds) =
      sloted fp v ra sp (bytesVal .ld b1) (bytesVal .ld b2) := by
  simp [slotBlock, caml_modifyXa9a8TSeg, regs, sloted, stateSym, runGM, stepGM, wvalM, srcVal, lookupG,
    eraseG, mkLine, decodeM, stepLdsM, imm20Of, LeanRV64DExecutable.Functions.sign_extend,
    Sail.BitVec.signExtend, Layout.sym_Caml_state]

theorem slot_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp : BitVec 64)
    (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (stateRead : ReadWindow stateSym 8) (statePins : LPins8 mem stateSym.toNat b1)
    (endRead : ReadWindow (bytesVal .ld b1 + 40#64) 8)
    (endPins : LPins8 mem (bytesVal .ld b1 + 40#64).toNat b2) :
    AccessPlan mem (regs fp v ra sp) (b1::b2::lds) slotBlock.body := by
  simp only [slotBlock, caml_modifyXa9a8TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply stateRead.ld rfl ?_ statePins
    simp [eaddrM, mkLine, decodeM, regs, stateSym, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM,
      imm20Of, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, Layout.sym_Caml_state]
  · apply endRead.ld rfl ?_ endPins
    simp [eaddrM, mkLine, decodeM, regs, stateSym, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM,
      imm20Of, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, Layout.sym_Caml_state]

/-- The slot is not below `young_end`: a major (or static) slot. -/
theorem slot_control (fp v ra sp : BitVec 64) (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (major : (bytesVal .ld b2).toNat ≤ fp.toNat) :
    TermFactsO (runGM slotBlock.body (regs fp v ra sp) (b1::b2::lds)) slotBlock.term := by
  rw [slot_regs]
  simp [slotBlock, caml_modifyXa9a8TSeg, TermFactsO, TermFactsT, sloted, srcVal, lookupG, guardB,
    Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
  omega

/-- The 32-byte native frame below the entry stack pointer (as `AllocEntry.frameSp`). -/
def frame (sp : BitVec 64) : BitVec 64 := sp + -32#64

def olded (fp v ra sp old : BitVec 64) : GRegs :=
  [(12, old &&& 1#64), (14, v), (10, old), (15, fp), (2, frame sp), (13, stateSym), (11, v), (1, ra)]

theorem old_regs (fp v ra sp dom ye : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    runGM oldBlock.body (sloted fp v ra sp dom ye) (b::lds) = olded fp v ra sp (bytesVal .ld b) := by
  simp [oldBlock, caml_modifyXa9ccTSeg, sloted, olded, frame, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

/-- A non-store instruction leaves the block's symbolic memory unchanged. -/
theorem stepMemM_of_addi {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs}
    (h : a.kind = .addi) : stepMemM m a L = m := by
  simp [stepMemM, h]

/-- A doubleword store to a disjoint address keeps a load's byte pins. -/
theorem lpins8_stepMemM_sd {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} {x : Nat}
    {bs : List (BitVec 8)} (h : a.kind = .sd) (pins : LPins8 m x bs)
    (apart : OutLRange [wentryM a L] x 8) : LPins8 (stepMemM m a L) x bs := by
  have := lpins8_writeLog pins apart
  simpa [stepMemM, h, writeLog] using this

/-- The block's stores, in the evaluator's exact address shape. -/
theorem old_log (fp v ra sp dom ye : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM oldBlock.body (sloted fp v ra sp dom ye) lds =
      [((frame sp + BitVec.ofNat 64 24).toNat, 8, ra),
       ((fp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0).toNat, 8, v)] := rfl

theorem old_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp dom ye : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (raWrite : WriteWindow (frame sp + BitVec.ofNat 64 24) 8)
    (slotRead : ReadWindow (fp + BitVec.ofNat 64 0) 8)
    (slotPins : LPins8 mem (fp + BitVec.ofNat 64 0).toNat b)
    (apart : OutLRange [((frame sp + BitVec.ofNat 64 24).toNat, 8, ra)] (fp + BitVec.ofNat 64 0).toNat 8)
    (slotWrite : WriteWindow (fp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0) 8) :
    AccessPlan mem (sloted fp v ra sp dom ye) (b::lds) oldBlock.body := by
  simp only [oldBlock, caml_modifyXa9ccTSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact raWrite.sd rfl rfl
  · apply slotRead.ld rfl rfl
    rw [stepMemM_of_addi rfl]
    exact lpins8_stepMemM_sd rfl (by rw [stepMemM_of_addi rfl]; exact slotPins) apart
  · exact slotWrite.sd rfl rfl

/-- The old field value is an immediate (`Is_long`). -/
theorem old_control (fp v ra sp dom ye : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (immediate : bytesVal .ld b &&& 1#64 ≠ 0#64) :
    TermFactsO (runGM oldBlock.body (sloted fp v ra sp dom ye) (b::lds)) oldBlock.term := by
  rw [old_regs]
  simpa [oldBlock, caml_modifyXa9ccTSeg, TermFactsO, TermFactsT, olded, srcVal, lookupG, guardB] using immediate

/-! ### Value classification: immediate? below `young_end`? above `young_start`? -/

def immed (fp v ra sp old : BitVec 64) : GRegs :=
  [(12, v &&& 1#64), (14, v), (10, old), (15, fp), (2, frame sp), (13, stateSym), (11, v), (1, ra)]

theorem imm_regs (fp v ra sp old : BitVec 64) (lds : List (List (BitVec 8))) :
    runGM immBlock.body (olded fp v ra sp old) lds = immed fp v ra sp old := by
  simp [immBlock, caml_modifyXaa0cFSeg, olded, immed, frame, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem imm_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp old : BitVec 64)
    (lds : List (List (BitVec 8))) : AccessPlan mem (olded fp v ra sp old) lds immBlock.body := by
  simp [immBlock, caml_modifyXaa0cFSeg, AccessPlan, MemFacts, mkLine, decodeM]

/-- The new value is a block (`Is_block`). -/
theorem imm_control (fp v ra sp old : BitVec 64) (lds : List (List (BitVec 8)))
    (block : v &&& 1#64 = 0#64) :
    TermFactsO (runGM immBlock.body (olded fp v ra sp old) lds) immBlock.term := by
  rw [imm_regs]
  simpa [immBlock, caml_modifyXaa0cFSeg, TermFactsO, TermFactsT, immed, srcVal, lookupG, guardB] using block

def ended (fp v ra sp old dom ye : BitVec 64) : GRegs :=
  [(12, ye), (13, dom), (14, v), (10, old), (15, fp), (2, frame sp), (11, v), (1, ra)]

theorem end_regs (fp v ra sp old : BitVec 64) (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    runGM endBlock.body (immed fp v ra sp old) (b1::b2::lds) =
      ended fp v ra sp old (bytesVal .ld b1) (bytesVal .ld b2) := by
  simp [endBlock, caml_modifyXaa14FSeg, immed, ended, frame, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem end_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp old : BitVec 64)
    (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (stateRead : ReadWindow (stateSym + BitVec.ofNat 64 0) 8)
    (statePins : LPins8 mem (stateSym + BitVec.ofNat 64 0).toNat b1)
    (endRead : ReadWindow (bytesVal .ld b1 + BitVec.ofNat 64 40) 8)
    (endPins : LPins8 mem (bytesVal .ld b1 + BitVec.ofNat 64 40).toNat b2) :
    AccessPlan mem (immed fp v ra sp old) (b1::b2::lds) endBlock.body := by
  simp only [endBlock, caml_modifyXaa14FSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact stateRead.ld rfl rfl statePins
  · exact endRead.ld rfl rfl endPins

/-- The value lies below `young_end`. -/
theorem end_control (fp v ra sp old : BitVec 64) (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (below : v.toNat < (bytesVal .ld b2).toNat) :
    TermFactsO (runGM endBlock.body (immed fp v ra sp old) (b1::b2::lds)) endBlock.term := by
  rw [end_regs]
  simp [endBlock, caml_modifyXaa14FSeg, TermFactsO, TermFactsT, ended, srcVal, lookupG, guardB,
    Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
  omega

def started (fp v ra sp old dom ys : BitVec 64) : GRegs :=
  [(12, ys), (13, dom), (14, v), (10, old), (15, fp), (2, frame sp), (11, v), (1, ra)]

theorem start_regs (fp v ra sp old dom ye : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    runGM startBlock.body (ended fp v ra sp old dom ye) (b::lds) =
      started fp v ra sp old dom (bytesVal .ld b) := by
  simp [startBlock, caml_modifyXaa20FSeg, ended, started, frame, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem start_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp old dom ye : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (startRead : ReadWindow (dom + BitVec.ofNat 64 32) 8)
    (startPins : LPins8 mem (dom + BitVec.ofNat 64 32).toNat b) :
    AccessPlan mem (ended fp v ra sp old dom ye) (b::lds) startBlock.body := by
  simp only [startBlock, caml_modifyXaa20FSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  exact startRead.ld rfl rfl startPins

/-- The value lies above `young_start`: a young block. -/
theorem start_control (fp v ra sp old dom ye : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (above : (bytesVal .ld b).toNat < v.toNat) :
    TermFactsO (runGM startBlock.body (ended fp v ra sp old dom ye) (b::lds)) startBlock.term := by
  rw [start_regs]
  simp [startBlock, caml_modifyXaa20FSeg, TermFactsO, TermFactsT, started, srcVal, lookupG, guardB,
    Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
  omega

/-! ### The remembered set: full (or unallocated) -/

def tabled (fp v ra sp old ys tbl ptr lim : BitVec 64) : GRegs :=
  [(13, lim), (14, ptr), (10, tbl), (12, ys), (15, fp), (2, frame sp), (11, v), (1, ra)]

theorem table_regs (fp v ra sp old dom ys : BitVec 64) (b1 b2 b3 : List (BitVec 8))
    (lds : List (List (BitVec 8))) :
    runGM tableBlock.body (started fp v ra sp old dom ys) (b1::b2::b3::lds) =
      tabled fp v ra sp old ys (bytesVal .ld b1) (bytesVal .ld b2) (bytesVal .ld b3) := by
  simp [tableBlock, caml_modifyXaa28TSeg, started, tabled, frame, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem table_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp old dom ys : BitVec 64)
    (b1 b2 b3 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (tableRead : ReadWindow (dom + BitVec.ofNat 64 104) 8)
    (tablePins : LPins8 mem (dom + BitVec.ofNat 64 104).toNat b1)
    (ptrRead : ReadWindow (bytesVal .ld b1 + BitVec.ofNat 64 24) 8)
    (ptrPins : LPins8 mem (bytesVal .ld b1 + BitVec.ofNat 64 24).toNat b2)
    (limitRead : ReadWindow (bytesVal .ld b1 + BitVec.ofNat 64 32) 8)
    (limitPins : LPins8 mem (bytesVal .ld b1 + BitVec.ofNat 64 32).toNat b3) :
    AccessPlan mem (started fp v ra sp old dom ys) (b1::b2::b3::lds) tableBlock.body := by
  simp only [tableBlock, caml_modifyXaa28TSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact tableRead.ld rfl rfl tablePins
  · exact ptrRead.ld rfl rfl ptrPins
  · exact limitRead.ld rfl rfl limitPins

/-- No room: `ptr ≥ limit` (true for the unallocated table, `0 ≥ 0`). -/
theorem table_control (fp v ra sp old dom ys : BitVec 64) (b1 b2 b3 : List (BitVec 8))
    (lds : List (List (BitVec 8))) (full : (bytesVal .ld b3).toNat ≤ (bytesVal .ld b2).toNat) :
    TermFactsO (runGM tableBlock.body (started fp v ra sp old dom ys) (b1::b2::b3::lds)) tableBlock.term := by
  rw [table_regs]
  simp [tableBlock, caml_modifyXaa28TSeg, TermFactsO, TermFactsT, tabled, srcVal, lookupG, guardB,
    Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
  omega

/-! ### Saving the slot and table pointer before the realloc call -/

theorem call_log (fp v ra sp old ys tbl ptr lim : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM callBlock.body (tabled fp v ra sp old ys tbl ptr lim) lds =
      [((frame sp + BitVec.ofNat 64 8).toNat, 8, fp), ((frame sp + BitVec.ofNat 64 0).toNat, 8, tbl)] := rfl

theorem call_regs (fp v ra sp old ys tbl ptr lim : BitVec 64) (lds : List (List (BitVec 8))) :
    runGM callBlock.body (tabled fp v ra sp old ys tbl ptr lim) lds = tabled fp v ra sp old ys tbl ptr lim := by
  simp [callBlock, caml_modifyXaa7cSeg, tabled, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem call_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp old ys tbl ptr lim : BitVec 64)
    (lds : List (List (BitVec 8)))
    (slotSave : WriteWindow (frame sp + BitVec.ofNat 64 8) 8)
    (tableSave : WriteWindow (frame sp + BitVec.ofNat 64 0) 8) :
    AccessPlan mem (tabled fp v ra sp old ys tbl ptr lim) lds callBlock.body := by
  simp only [callBlock, caml_modifyXaa7cSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact slotSave.sd rfl rfl
  · exact tableSave.sd rfl rfl

/-! ### The chain certificate -/

theorem slot_log (fp v ra sp : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM slotBlock.body (regs fp v ra sp) lds = [] := rfl
theorem slot_loads (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM slotBlock.body (b1::b2::lds) = lds := rfl
theorem old_loads (b : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM oldBlock.body (b::lds) = lds := rfl
theorem imm_log (fp v ra sp old : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM immBlock.body (olded fp v ra sp old) lds = [] := rfl
theorem imm_loads (lds : List (List (BitVec 8))) : ldsRunM immBlock.body lds = lds := rfl
theorem end_log (fp v ra sp old : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM endBlock.body (immed fp v ra sp old) lds = [] := rfl
theorem end_loads (b1 b2 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM endBlock.body (b1::b2::lds) = lds := rfl
theorem start_log (fp v ra sp old dom ye : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM startBlock.body (ended fp v ra sp old dom ye) lds = [] := rfl
theorem start_loads (b : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM startBlock.body (b::lds) = lds := rfl
theorem table_log (fp v ra sp old dom ys : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM tableBlock.body (started fp v ra sp old dom ys) lds = [] := rfl
theorem table_loads (b1 b2 b3 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM tableBlock.body (b1::b2::b3::lds) = lds := rfl

/-- The memory after the slot block's two stores (saved `ra`, new field value). -/
def stored (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog mem [((frame sp + BitVec.ofNat 64 24).toNat, 8, ra),
    ((fp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0).toNat, 8, v)]

/-- Every scalar observation the route makes, named. Loads after the two
stores read `stored`; branch conditions select this route. -/
structure Route (mem : Std.ExtHashMap Nat (BitVec 8)) (fp v ra sp : BitVec 64)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)) : Prop where
  stateRead : ReadWindow stateSym 8
  statePins : LPins8 mem stateSym.toNat b1
  endRead : ReadWindow (bytesVal .ld b1 + 40#64) 8
  endPins : LPins8 mem (bytesVal .ld b1 + 40#64).toNat b2
  major : (bytesVal .ld b2).toNat ≤ fp.toNat
  raWrite : WriteWindow (frame sp + BitVec.ofNat 64 24) 8
  slotRead : ReadWindow (fp + BitVec.ofNat 64 0) 8
  slotPins : LPins8 mem (fp + BitVec.ofNat 64 0).toNat b3
  apart : OutLRange [((frame sp + BitVec.ofNat 64 24).toNat, 8, ra)] (fp + BitVec.ofNat 64 0).toNat 8
  slotWrite : WriteWindow (fp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0) 8
  oldImmediate : bytesVal .ld b3 &&& 1#64 ≠ 0#64
  valueBlock : v &&& 1#64 = 0#64
  stateRead' : ReadWindow (stateSym + BitVec.ofNat 64 0) 8
  statePins' : LPins8 (stored mem fp v ra sp) (stateSym + BitVec.ofNat 64 0).toNat b4
  endRead' : ReadWindow (bytesVal .ld b4 + BitVec.ofNat 64 40) 8
  endPins' : LPins8 (stored mem fp v ra sp) (bytesVal .ld b4 + BitVec.ofNat 64 40).toNat b5
  below : v.toNat < (bytesVal .ld b5).toNat
  startRead : ReadWindow (bytesVal .ld b4 + BitVec.ofNat 64 32) 8
  startPins : LPins8 (stored mem fp v ra sp) (bytesVal .ld b4 + BitVec.ofNat 64 32).toNat b6
  above : (bytesVal .ld b6).toNat < v.toNat
  tableRead : ReadWindow (bytesVal .ld b4 + BitVec.ofNat 64 104) 8
  tablePins : LPins8 (stored mem fp v ra sp) (bytesVal .ld b4 + BitVec.ofNat 64 104).toNat b7
  ptrRead : ReadWindow (bytesVal .ld b7 + BitVec.ofNat 64 24) 8
  ptrPins : LPins8 (stored mem fp v ra sp) (bytesVal .ld b7 + BitVec.ofNat 64 24).toNat b8
  limitRead : ReadWindow (bytesVal .ld b7 + BitVec.ofNat 64 32) 8
  limitPins : LPins8 (stored mem fp v ra sp) (bytesVal .ld b7 + BitVec.ofNat 64 32).toNat b9
  full : (bytesVal .ld b9).toNat ≤ (bytesVal .ld b8).toNat
  slotSave : WriteWindow (frame sp + BitVec.ofNat 64 8) 8
  tableSave : WriteWindow (frame sp + BitVec.ofNat 64 0) 8

theorem writeLog_nil' (m : Std.ExtHashMap Nat (BitVec 8)) : writeLog m [] = m := rfl

theorem access {mem : Std.ExtHashMap Nat (BitVec 8)} {fp v ra sp : BitVec 64}
    {b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)} (r : Route mem fp v ra sp b1 b2 b3 b4 b5 b6 b7 b8 b9) :
    ChainAccess mem (regs fp v ra sp) [b1, b2, b3, b4, b5, b6, b7, b8, b9] blocks := by
  apply ChainAccess.cons ⟨slot_access mem fp v ra sp b1 b2 _ r.stateRead r.statePins r.endRead r.endPins,
    slot_control fp v ra sp b1 b2 _ r.major⟩
  rw [slot_log, slot_regs, slot_loads, writeLog_nil']
  apply ChainAccess.cons ⟨old_access _ fp v ra sp _ _ b3 _ r.raWrite r.slotRead r.slotPins r.apart r.slotWrite,
    old_control fp v ra sp _ _ b3 _ r.oldImmediate⟩
  rw [old_log, old_regs, old_loads]
  change ChainAccess (stored mem fp v ra sp) _ _ _
  apply ChainAccess.cons ⟨imm_access _ fp v ra sp _ _, imm_control fp v ra sp _ _ r.valueBlock⟩
  rw [imm_log, imm_regs, imm_loads, writeLog_nil']
  apply ChainAccess.cons ⟨end_access _ fp v ra sp _ b4 b5 _ r.stateRead' r.statePins' r.endRead' r.endPins',
    end_control fp v ra sp _ b4 b5 _ r.below⟩
  rw [end_log, end_regs, end_loads, writeLog_nil']
  apply ChainAccess.cons ⟨start_access _ fp v ra sp _ _ _ b6 _ r.startRead r.startPins,
    start_control fp v ra sp _ _ _ b6 _ r.above⟩
  rw [start_log, start_regs, start_loads, writeLog_nil']
  apply ChainAccess.cons ⟨table_access _ fp v ra sp _ _ _ b7 b8 b9 _ r.tableRead r.tablePins r.ptrRead
      r.ptrPins r.limitRead r.limitPins, table_control fp v ra sp _ _ _ b7 b8 b9 _ r.full⟩
  rw [table_log, table_regs, table_loads, writeLog_nil']
  exact ChainAccess.cons ⟨call_access _ fp v ra sp _ _ _ _ _ _ r.slotSave r.tableSave,
    by simp [callBlock, caml_modifyXaa7cSeg, TermFactsO]⟩ ChainAccess.nil

/-! ### The route up to the realloc call -/

def loads (b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)) : List (List (BitVec 8)) :=
  [b1, b2, b3, b4, b5, b6, b7, b8, b9]

/-- Machine state at `caml_modify`'s entry on this route. -/
structure Input (fp v ra sp : BitVec 64) (b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)) (c : Config) :
    Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Code.Caml_modifyLoaded c.σ.mem
  registers : GHolds c.σ (regs fp v ra sp)
  route : Route c.σ.mem fp v ra sp b1 b2 b3 b4 b5 b6 b7 b8 b9

/-- **The actual route from `caml_modify`'s entry to its `jal caml_realloc_ref_table`.** -/
theorem prefix_run {fp v ra sp : BitVec 64} {b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)} {c : Config}
    (input : Input fp v ra sp b1 b2 b3 b4 b5 b6 b7 b8 b9 c) :
    FnSummary pc (fun d => d = c)
      (BlockPost blocks pc (regs fp v ra sp) (loads b1 b2 b3 b4 b5 b6 b7 b8 b9) c) :=
  block_summary blocks pc _ _ c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [10, 11, 1, 2]; decide,
      chainPlan_facts (code_facts input.code) (access input.route), chain_ok, input.tick⟩

/-- The route's exact store log: saved `ra`, the new field value, then the
saved slot and table pointer. -/
theorem log (fp v ra sp : BitVec 64) (b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)) :
    (evalBlocks blocks (SegEvalState.init (regs fp v ra sp) (loads b1 b2 b3 b4 b5 b6 b7 b8 b9))).log =
      [((frame sp + BitVec.ofNat 64 24).toNat, 8, ra),
       ((fp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0).toNat, 8, v),
       ((frame sp + BitVec.ofNat 64 8).toNat, 8, fp),
       ((frame sp + BitVec.ofNat 64 0).toNat, 8, bytesVal .ld b7)] := by
  simp only [blocks, loads, evalBlocks, evalBlock, SegEvalState.init, slot_regs, slot_loads, slot_log,
    old_regs, old_loads, old_log, imm_regs, imm_loads, imm_log, end_regs, end_loads, end_log,
    start_regs, start_loads, start_log, table_regs, table_loads, table_log, call_log,
    List.nil_append, List.cons_append]

/-- The registers parked at the call. -/
theorem registers (fp v ra sp : BitVec 64) (b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (BitVec 8)) :
    (evalBlocks blocks (SegEvalState.init (regs fp v ra sp) (loads b1 b2 b3 b4 b5 b6 b7 b8 b9))).regs =
      tabled fp v ra sp (bytesVal .ld b3) (bytesVal .ld b6) (bytesVal .ld b7) (bytesVal .ld b8)
        (bytesVal .ld b9) := by
  simp only [blocks, loads, evalBlocks, evalBlock, SegEvalState.init, slot_regs, slot_loads,
    old_regs, old_loads, imm_regs, imm_loads, end_regs, end_loads, start_regs, start_loads,
    table_regs, table_loads, call_regs]

end OCaml.Vm.Gc.ModifySlow
