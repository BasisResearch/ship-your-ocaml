import OCaml.Vm.Gc.FieldClassify

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Shared copy-store and advance data facts, independent of the classifier. -/
theorem store_tail_access (slot delta target index : BitVec 64) (c : Config)
    (destination : WriteWindow (delta + slot) 8) (header : ReadWindow (target - 8#64) 8) :
    ChainAccess c.σ.mem (continuationRegs slot delta target index (word c slot.toNat))
      (loads slot delta target c).tail (storeBlocks (again slot delta target index c)) := by
  refine ChainAccess.cons ⟨?_, True.intro⟩ ?_
  · exact store_access slot delta target index c destination
  · have log : wlogM storeBlock.body
        (continuationRegs slot delta target index (word c slot.toNat)) (loads slot delta target c).tail =
        copyLog slot delta c := store_log slot delta target index (word c slot.toNat) (loads slot delta target c).tail
    rw [log]
    change ChainAccess (writeLog c.σ.mem (copyLog slot delta c))
      (continuationRegs slot delta target index (word c slot.toNat))
      (loads slot delta target c).tail [tailBlock (again slot delta target index c)]
    have data := tail_access slot delta target index c header (again slot delta target index c)
    have control := tail_control slot delta target index c
    generalize choice : again slot delta target index c = back at data control ⊢
    cases back <;> refine ChainAccess.cons ⟨?_, ?_⟩ ChainAccess.nil
    all_goals first | exact data | exact control

/-- Copy continuation input. The preceding classifier chooses this PC;
this summary needs only the actual destination and size-header windows. -/
structure StoreInput (slot delta target index : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (continuationRegs slot delta target index (word c slot.toNat))
  destination : WriteWindow (delta + slot) 8
  header : ReadWindow (target - 8#64) 8

structure StorePost (slot delta target index : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (storeBlocks (again slot delta target index before)) storePc
    (continuationRegs slot delta target index (word before slot.toNat))
    (loads slot delta target before).tail before after
  destination : word after (delta + slot).toNat = word before slot.toNat
  memory : after.σ.mem = writeLog before.σ.mem (copyLog slot delta before)
  pc : PCAt (if again slot delta target index before then pc else exitPc) after
  registers : GHolds after.σ (regs (slot + 8#64) delta target (index + 1#64))
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem store_machine {slot delta target index c} (input : StoreInput slot delta target index c) :
    FnSummary storePc (fun d => d = c) (StorePost slot delta target index c) := by
  have facts := chainPlan_facts (store_code _ input.code)
    (store_tail_access slot delta target index c input.destination input.header)
  have summary := block_summary (storeBlocks (again slot delta target index c)) storePc
    (continuationRegs slot delta target index (word c slot.toNat)) (loads slot delta target c).tail c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [11,10,8,18,19,9]; decide,
      facts, store_ok _, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post, ?_, ?_, ?_, store_registers (segmentPost_of_block post),
    mopupCode_after input.code facts post⟩
  · change bytesT after.σ.mem _ 8 = _
    rw [post.memory, store_effect, word_writeLog]
  · rw [post.memory, store_effect]
    rfl
  · rw [PCAt, post.pc, store_exit]

/-- The range classifier preserved every register and memory observation the
copy continuation needs. -/
theorem ClassifiedPost.store_input {slot delta target index domain before after}
    (post : ClassifiedPost slot delta target index domain before after)
    (destination : WriteWindow (delta + slot) 8) (header : ReadWindow (target - 8#64) 8) :
    StoreInput slot delta target index after := by
  refine ⟨post.good, post.minstret, post.tick, post.code, ?_, destination, header⟩
  simpa only [word, post.memory] using post.registers

end OCaml.Vm.Gc.FieldCopy
