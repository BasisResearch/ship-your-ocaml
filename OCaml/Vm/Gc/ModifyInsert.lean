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
# `caml_modify`: remembered-set insertion after the realloc call, and return

From `jal caml_realloc_ref_table`'s return point `aa88`: reload the table
pointer and the slot from the native frame and the table's `ptr`; `aa38`
bumps `ptr` and stores the slot at the old `ptr`; `aa44` restores `ra`
and `sp` and returns. Logs and addresses are stated in the evaluator's exact
shape (`rfl`).
-/

set_option maxRecDepth 100000

namespace OCaml.Vm.Gc.ModifyInsert
open Vsa.Sim Vsa.Machine OCaml.Vm.Primitives LeanRV64DExecutable

def reloadBlock : BBlock := caml_modifyXaa88Seg.getD 0 { body := [], term := none }
def insertBlock : BBlock := caml_modifyXaa38Seg.getD 0 { body := [], term := none }
def returnBlock : BBlock := caml_modifyXaa44Seg.getD 0 { body := [], term := none }
def blocks := [reloadBlock, insertBlock, returnBlock]
def pc : BitVec 64 := 0x8000aa88#64

def regs (fsp : BitVec 64) : GRegs := [(2, fsp)]

theorem chain_ok : ChainOK pc [2] blocks := by decide

theorem code_facts {mem : Std.ExtHashMap Nat (BitVec 8)}
    (code : Code.Caml_modifyLoaded mem) : ChainCode mem blocks := by
  intro b member
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [reloadBlock, insertBlock, returnBlock, caml_modifyXaa88Seg, caml_modifyXaa38Seg,
    caml_modifyXaa44Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts code with "Vsa.Sim.Code.caml_modify_at_"

def reloaded (fsp tbl fp ptr : BitVec 64) : GRegs := [(14, ptr), (15, fp), (10, tbl), (2, fsp)]

theorem reload_regs (fsp : BitVec 64) (b1 b2 b3 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    runGM reloadBlock.body (regs fsp) (b1::b2::b3::lds) =
      reloaded fsp (bytesVal .ld b1) (bytesVal .ld b2) (bytesVal .ld b3) := by
  simp [reloadBlock, caml_modifyXaa88Seg, regs, reloaded, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem reload_log (fsp : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM reloadBlock.body (regs fsp) lds = [] := rfl
theorem reload_loads (b1 b2 b3 : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    ldsRunM reloadBlock.body (b1::b2::b3::lds) = lds := rfl

theorem reload_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fsp : BitVec 64)
    (b1 b2 b3 : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (tableRead : ReadWindow (fsp + BitVec.ofNat 64 0) 8) (tablePins : LPins8 mem (fsp + BitVec.ofNat 64 0).toNat b1)
    (slotRead : ReadWindow (fsp + BitVec.ofNat 64 8) 8) (slotPins : LPins8 mem (fsp + BitVec.ofNat 64 8).toNat b2)
    (ptrRead : ReadWindow (bytesVal .ld b1 + BitVec.ofNat 64 24) 8)
    (ptrPins : LPins8 mem (bytesVal .ld b1 + BitVec.ofNat 64 24).toNat b3) :
    AccessPlan mem (regs fsp) (b1::b2::b3::lds) reloadBlock.body := by
  simp only [reloadBlock, caml_modifyXaa88Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact tableRead.ld rfl rfl tablePins
  · exact slotRead.ld rfl rfl slotPins
  · exact ptrRead.ld rfl rfl ptrPins

def inserted (fsp tbl fp ptr : BitVec 64) : GRegs :=
  [(13, ptr + 8#64), (14, ptr), (15, fp), (10, tbl), (2, fsp)]

theorem insert_regs (fsp tbl fp ptr : BitVec 64) (lds : List (List (BitVec 8))) :
    runGM insertBlock.body (reloaded fsp tbl fp ptr) lds = inserted fsp tbl fp ptr := by
  simp [insertBlock, caml_modifyXaa38Seg, reloaded, inserted, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

/-- `ref_table->ptr := ptr + 8`, then `*ptr := slot`. -/
theorem insert_log (fsp tbl fp ptr : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM insertBlock.body (reloaded fsp tbl fp ptr) lds =
      [((tbl + BitVec.ofNat 64 24).toNat, 8, ptr + BitVec.ofNat 64 8),
       ((ptr + BitVec.ofNat 64 0).toNat, 8, fp)] := rfl
theorem insert_loads (lds : List (List (BitVec 8))) : ldsRunM insertBlock.body lds = lds := rfl

theorem insert_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fsp tbl fp ptr : BitVec 64)
    (lds : List (List (BitVec 8)))
    (ptrWrite : WriteWindow (tbl + BitVec.ofNat 64 24) 8) (entryWrite : WriteWindow (ptr + BitVec.ofNat 64 0) 8) :
    AccessPlan mem (reloaded fsp tbl fp ptr) lds insertBlock.body := by
  simp only [insertBlock, caml_modifyXaa38Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · exact ptrWrite.sd rfl rfl
  · exact entryWrite.sd rfl rfl

def returned (fsp tbl fp ptr ra : BitVec 64) : GRegs :=
  [(2, fsp + 32#64), (1, ra), (13, ptr + 8#64), (14, ptr), (15, fp), (10, tbl)]

theorem return_regs (fsp tbl fp ptr : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8))) :
    runGM returnBlock.body (inserted fsp tbl fp ptr) (b::lds) =
      returned fsp tbl fp ptr (bytesVal .ld b) := by
  simp [returnBlock, caml_modifyXaa44Seg, inserted, returned, runGM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]

theorem return_log (fsp tbl fp ptr : BitVec 64) (lds : List (List (BitVec 8))) :
    wlogM returnBlock.body (inserted fsp tbl fp ptr) lds = [] := rfl

theorem return_access (mem : Std.ExtHashMap Nat (BitVec 8)) (fsp tbl fp ptr : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (raRead : ReadWindow (fsp + BitVec.ofNat 64 24) 8) (raPins : LPins8 mem (fsp + BitVec.ofNat 64 24).toNat b) :
    AccessPlan mem (inserted fsp tbl fp ptr) (b::lds) returnBlock.body := by
  simp only [returnBlock, caml_modifyXaa44Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  exact raRead.ld rfl rfl raPins

theorem return_control (fsp tbl fp ptr : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (aligned : (bytesVal .ld b).toNat % 4 = 0) :
    TermFactsO (runGM returnBlock.body (inserted fsp tbl fp ptr) (b::lds)) returnBlock.term := by
  rw [return_regs]
  change (Sail.BitVec.update (srcVal 1 (returned fsp tbl fp ptr (bytesVal .ld b)) +
    Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
  rw [show srcVal 1 (returned fsp tbl fp ptr (bytesVal .ld b)) = bytesVal .ld b from rfl,
    ret_tgt _ aligned]
  exact aligned

/-! ### The chain -/

def loads (b1 b2 b3 b4 : List (BitVec 8)) : List (List (BitVec 8)) := [b1, b2, b3, b4]

/-- The memory after the two insertion stores. -/
def stored (mem : Std.ExtHashMap Nat (BitVec 8)) (tbl fp ptr : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog mem [((tbl + BitVec.ofNat 64 24).toNat, 8, ptr + BitVec.ofNat 64 8),
    ((ptr + BitVec.ofNat 64 0).toNat, 8, fp)]

/-- The route's scalar observations: the frame slots and table `ptr` it
reloads, the two insertion stores, and the saved return address. -/
structure Route (mem : Std.ExtHashMap Nat (BitVec 8)) (fsp : BitVec 64) (b1 b2 b3 b4 : List (BitVec 8)) :
    Prop where
  tableRead : ReadWindow (fsp + BitVec.ofNat 64 0) 8
  tablePins : LPins8 mem (fsp + BitVec.ofNat 64 0).toNat b1
  slotRead : ReadWindow (fsp + BitVec.ofNat 64 8) 8
  slotPins : LPins8 mem (fsp + BitVec.ofNat 64 8).toNat b2
  ptrRead : ReadWindow (bytesVal .ld b1 + BitVec.ofNat 64 24) 8
  ptrPins : LPins8 mem (bytesVal .ld b1 + BitVec.ofNat 64 24).toNat b3
  ptrWrite : WriteWindow (bytesVal .ld b1 + BitVec.ofNat 64 24) 8
  entryWrite : WriteWindow (bytesVal .ld b3 + BitVec.ofNat 64 0) 8
  raRead : ReadWindow (fsp + BitVec.ofNat 64 24) 8
  raPins : LPins8 (stored mem (bytesVal .ld b1) (bytesVal .ld b2) (bytesVal .ld b3))
    (fsp + BitVec.ofNat 64 24).toNat b4
  aligned : (bytesVal .ld b4).toNat % 4 = 0

theorem writeLog_nil' (m : Std.ExtHashMap Nat (BitVec 8)) : writeLog m [] = m := rfl

theorem access {mem : Std.ExtHashMap Nat (BitVec 8)} {fsp : BitVec 64} {b1 b2 b3 b4 : List (BitVec 8)}
    (r : Route mem fsp b1 b2 b3 b4) : ChainAccess mem (regs fsp) (loads b1 b2 b3 b4) blocks := by
  apply ChainAccess.cons ⟨reload_access mem fsp b1 b2 b3 _ r.tableRead r.tablePins r.slotRead r.slotPins
    r.ptrRead r.ptrPins, by simp [reloadBlock, caml_modifyXaa88Seg, TermFactsO, TermFactsT]⟩
  rw [reload_log, reload_regs, reload_loads, writeLog_nil']
  apply ChainAccess.cons ⟨insert_access mem fsp _ _ _ _ r.ptrWrite r.entryWrite, trivial⟩
  rw [insert_log, insert_regs, insert_loads]
  change ChainAccess (stored mem _ _ _) _ _ _
  exact ChainAccess.cons ⟨return_access _ fsp _ _ _ b4 [] r.raRead r.raPins,
    return_control fsp _ _ _ b4 [] r.aligned⟩ ChainAccess.nil

structure Input (fsp : BitVec 64) (b1 b2 b3 b4 : List (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Code.Caml_modifyLoaded c.σ.mem
  registers : GHolds c.σ (regs fsp)
  route : Route c.σ.mem fsp b1 b2 b3 b4

/-- **The actual insertion and return** after `caml_realloc_ref_table`. -/
theorem run {fsp : BitVec 64} {b1 b2 b3 b4 : List (BitVec 8)} {c : Config} (input : Input fsp b1 b2 b3 b4 c) :
    FnSummary pc (fun d => d = c) (BlockPost blocks pc (regs fsp) (loads b1 b2 b3 b4) c) :=
  block_summary blocks pc _ _ c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2]; decide,
      chainPlan_facts (code_facts input.code) (access input.route), chain_ok, input.tick⟩

theorem log (fsp : BitVec 64) (b1 b2 b3 b4 : List (BitVec 8)) :
    (evalBlocks blocks (SegEvalState.init (regs fsp) (loads b1 b2 b3 b4))).log =
      [((bytesVal .ld b1 + BitVec.ofNat 64 24).toNat, 8, bytesVal .ld b3 + BitVec.ofNat 64 8),
       ((bytesVal .ld b3 + BitVec.ofNat 64 0).toNat, 8, bytesVal .ld b2)] := by
  simp only [blocks, loads, evalBlocks, evalBlock, SegEvalState.init, reload_regs, reload_loads, reload_log,
    insert_regs, insert_loads, insert_log, return_log, List.nil_append, List.cons_append, List.append_nil]

theorem registers (fsp : BitVec 64) (b1 b2 b3 b4 : List (BitVec 8)) :
    (evalBlocks blocks (SegEvalState.init (regs fsp) (loads b1 b2 b3 b4))).regs =
      returned fsp (bytesVal .ld b1) (bytesVal .ld b2) (bytesVal .ld b3) (bytesVal .ld b4) := by
  simp only [blocks, loads, evalBlocks, evalBlock, SegEvalState.init, reload_regs, reload_loads,
    insert_regs, insert_loads, return_regs]

end OCaml.Vm.Gc.ModifyInsert
