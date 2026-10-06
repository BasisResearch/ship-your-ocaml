import OCaml.Vm.Gc.Generated.Modify
import OCaml.Vm.Gc.ChainPlan
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

end OCaml.Vm.Gc.ModifySlow
