import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.Generated.FieldCopy
import Vsa.Sim.ChainMemory
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def copyLog (slot delta : BitVec 64) (c : Config) : List WEntry :=
  [((delta + slot).toNat, 8, word c slot.toNat)]

def loads (slot delta target : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem slot.toNat,
   read8 (writeLog c.σ.mem (copyLog slot delta c)) (target - 8#64).toNat]

/-- Loop choice computed from the actual header read after the destination store. -/
def again (slot delta target index : BitVec 64) (c : Config) : Bool :=
  guardB .BLTU (index + 1#64)
    ((bytesVal .ld ((loads slot delta target c).tail.headD [])) >>> (10 : Nat))

structure Windows (slot delta target : BitVec 64) : Prop where
  source : ReadWindow slot 8
  destination : WriteWindow (delta + slot) 8
  header : ReadWindow (target - 8#64) 8

macro "field_copy_address" : tactic => `(tactic|
  simp [eaddrM, mkLine, decodeM, regs, afterHeadRegs, stepGM, stepLdsM,
    wvalM, srcVal, lookupG, eraseG, loads, Functions.sign_extend, Sail.BitVec.signExtend])

/-- The head's data certificate depends only on its first scalar load. -/
theorem head_access_bytes (slot delta target index : BitVec 64) (c : Config)
    (lds : List (List (BitVec 8))) (window : ReadWindow slot 8)
    (pins : LPins8 c.σ.mem slot.toNat (lds.headD [])) :
    AccessPlan c.σ.mem (regs slot delta target index) lds headBlock.body := by
  simp only [AccessPlan, headBlock, caml_oldify_mopupX9d4cTSeg, List.getD_cons_zero]
  chain_facts True.intro
  apply window.ld rfl ?_ pins
  field_copy_address

theorem head_access (slot delta target index : BitVec 64) (c : Config)
    (window : ReadWindow slot 8) :
    AccessPlan c.σ.mem (regs slot delta target index) (loads slot delta target c) headBlock.body :=
  head_access_bytes slot delta target index c _ window (read8_pins _ _)

theorem head_control (slot delta target index : BitVec 64) (c : Config)
    (immediate : guardB .BNE (word c slot.toNat &&& 1#64) 0 = true) :
    TermFactsO (runGM headBlock.body (regs slot delta target index) (loads slot delta target c))
      headBlock.term := by
  rw [head_regs]
  simpa [headBlock, caml_oldify_mopupX9d4cTSeg, TermFactsO, TermFactsT,
    afterHeadRegs, srcVal, lookupG, loads, read8_value, word] using immediate

theorem store_access (slot delta target index : BitVec 64) (c : Config)
    (window : WriteWindow (delta + slot) 8) :
    AccessPlan c.σ.mem (afterHeadRegs slot delta target index (word c slot.toNat))
      (loads slot delta target c).tail storeBlock.body := by
  simp only [AccessPlan, storeBlock, caml_oldify_mopupX9d70Seg, List.getD_cons_zero]
  chain_facts True.intro
  apply window.sd rfl
  field_copy_address

theorem tail_access (slot delta target index : BitVec 64) (c : Config)
    (window : ReadWindow (target - 8#64) 8) (back : Bool) :
    AccessPlan (writeLog c.σ.mem (copyLog slot delta c))
      (afterHeadRegs slot delta target index (word c slot.toNat))
      (loads slot delta target c).tail (tailBlock back).body := by
  cases back <;> simp only [AccessPlan, tailBlock, Bool.false_eq_true, ite_false, ite_true,
    caml_oldify_mopupX9d74TSeg, caml_oldify_mopupX9d74FSeg, List.getD_cons_zero]
  all_goals chain_facts True.intro
  all_goals apply window.ld rfl ?_ (read8_pins _ (target - 8#64).toNat)
  all_goals field_copy_address
  all_goals simp [BitVec.sub_eq_add_neg]

theorem tail_control (slot delta target index : BitVec 64) (c : Config) :
    TermFactsO (runGM (tailBlock (again slot delta target index c)).body
      (afterHeadRegs slot delta target index (word c slot.toNat)) (loads slot delta target c).tail)
      (tailBlock (again slot delta target index c)).term := by
  generalize choice : again slot delta target index c = back
  cases back <;> simpa [again, tailBlock, caml_oldify_mopupX9d74TSeg, caml_oldify_mopupX9d74FSeg,
    TermFactsO, TermFactsT, runGM, stepGM, stepLdsM, mkLine, decodeM, afterHeadRegs,
    srcVal, lookupG, eraseG, wvalM, shamtOf, Functions.sign_extend, Sail.BitVec.signExtend,
    Sail.BitVec.extractLsb, Sail.shift_bits_right] using choice

theorem copy_access (slot delta target index : BitVec 64) (c : Config)
    (windows : Windows slot delta target)
    (immediate : guardB .BNE (word c slot.toNat &&& 1#64) 0 = true) :
    ChainAccess c.σ.mem (regs slot delta target index) (loads slot delta target c)
      (blocks (again slot delta target index c)) := by
  apply ChainAccess.cons ⟨head_access slot delta target index c windows.source,
    head_control slot delta target index c immediate⟩
  rw [head_log, head_regs]
  have value : bytesVal .ld ((loads slot delta target c).headD []) = word c slot.toNat :=
    read8_value _ _
  rw [value]
  change ChainAccess c.σ.mem (afterHeadRegs slot delta target index (word c slot.toNat))
    (loads slot delta target c).tail [storeBlock, tailBlock (again slot delta target index c)]
  apply ChainAccess.cons ⟨store_access slot delta target index c windows.destination, True.intro⟩
  rw [store_log]
  change ChainAccess (writeLog c.σ.mem (copyLog slot delta c))
    (afterHeadRegs slot delta target index (word c slot.toNat))
    (loads slot delta target c).tail [tailBlock (again slot delta target index c)]
  exact ChainAccess.cons ⟨tail_access slot delta target index c windows.header _,
    tail_control slot delta target index c⟩ ChainAccess.nil

/-- Concrete memory/platform input for one immediate-valued field iteration. -/
structure Input (slot delta target index : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  registers : GHolds c.σ (regs slot delta target index)
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  windows : Windows slot delta target
  immediate : guardB .BNE (word c slot.toNat &&& 1#64) 0 = true

/-- Exact native-frame result plus copied value and scan-counter progression. -/
structure CopyPost (slot delta target index : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (blocks (again slot delta target index before)) pc (regs slot delta target index)
    (loads slot delta target before) before after
  destination : word after (delta + slot).toNat = word before slot.toNat
  index : gprGet after.σ 9 = some (index + 1#64)
  source : gprGet after.σ 8 = some (slot + 8#64)

/-- Run one real immediate-field iteration; all scalar access and branch
conditions are discharged from the concrete input. -/
theorem copy_machine {slot delta target index c} (input : Input slot delta target index c) :
    FnSummary pc (fun d => d = c) (CopyPost slot delta target index c) := by
  have summary := block_summary (blocks (again slot delta target index c)) pc (regs slot delta target index)
    (loads slot delta target c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [8,18,19,9]; decide,
      chainPlan_facts (code_facts _ input.code) (copy_access slot delta target index c input.windows input.immediate),
      chain_ok _, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have reflected : Post (again slot delta target index c) slot delta target index
      (loads slot delta target c) c.σ.mem after :=
    segmentPost_of_block post
  refine ⟨post, ?_, reflected.advance.1, reflected.advance.2⟩
  change bytesT after.σ.mem (delta + slot).toNat 8 = _
  rw [post.memory]
  change bytesT (writeLog c.σ.mem (outcome _ slot delta target index _).log) _ 8 = _
  rw [writes, word_writeLog]
  exact read8_value _ _

/-- The scalar store policy preserves the mopup code image for the next visit. -/
theorem CopyPost.code {slot delta target index before after}
    (input : Input slot delta target index before)
    (post : CopyPost slot delta target index before after) :
    Code.Caml_oldify_mopupLoaded after.σ.mem := by
  exact mopupCode_after input.code
    (chainPlan_facts (code_facts _ input.code)
      (copy_access slot delta target index before input.windows input.immediate)) post.machine

/-- Readback of the size header uses the shared total-word frame theorem. -/
theorem header_unchanged (slot delta target : BitVec 64) (c : Config)
    (outside : OutLRange (copyLog slot delta c) (target - 8#64).toNat 8) :
    bytesVal .ld ((loads slot delta target c).tail.headD []) = word c (target - 8#64).toNat := by
  change bytesVal .ld (read8 (writeLog c.σ.mem (copyLog slot delta c)) (target - 8#64).toNat) = _
  rw [read8_value, bytesT_writeLog_out _ outside]
  rfl

theorem CopyPost.reflected {slot delta target index before after}
    (post : CopyPost slot delta target index before after) :
    Post (again slot delta target index before) slot delta target index
      (loads slot delta target before) before.σ.mem after :=
  segmentPost_of_block post.machine

theorem CopyPost.scan_regs {slot delta target index before after}
    (post : CopyPost slot delta target index before after) :
    GHolds after.σ (regs (slot + 8#64) delta target (index + 1#64)) :=
  post.reflected.scan_regs

theorem CopyPost.pc {slot delta target index before after}
    (post : CopyPost slot delta target index before after) :
    PCAt (if again slot delta target index before then pc else exitPc) after := by
  rw [PCAt, post.machine.pc, end_pc]

theorem CopyPost.memory {slot delta target index before after}
    (post : CopyPost slot delta target index before after) :
    after.σ.mem = writeLog before.σ.mem (copyLog slot delta before) := by
  rw [post.machine.memory]
  change writeLog before.σ.mem (outcome _ slot delta target index _).log = _
  rw [writes]
  change writeLog before.σ.mem [((delta + slot).toNat, 8,
    bytesVal .ld (read8 before.σ.mem slot.toNat))] = _
  rw [read8_value]
  rfl

end OCaml.Vm.Gc.FieldCopy
