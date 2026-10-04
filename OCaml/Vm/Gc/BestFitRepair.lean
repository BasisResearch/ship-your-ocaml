import OCaml.Vm.Gc.BestFitSmall

namespace OCaml.Vm.Gc.BestFitSmall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The merge cursor points to the node being removed. Its repair store
must preserve the successor and the free-word counter used later. -/
structure RepairInput (ra size : BitVec 64) (c : Config) : Prop extends BaseInput ra size c where
  merge : cursor size c = first size c
  mergeWrite : WriteWindow (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge) 8
  nextOutside : OutLRange (repairLog size) (first size c).toNat 8
  counterRepairOutside : OutLRange (repairLog size) Layout.sym_caml_fl_cur_wsz 8

theorem repair_test_control (ra size head : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (same : bytesVal .ld b = head) :
    TermFactsO (runGM repairTest.body (listed ra size head) (b::lds)) repairTest.term := by
  rw [repair_test_regs]
  simpa [repairTest,bf_allocateX7440TSeg,TermFactsO,TermFactsT,listed,merged,srcVal,lookupG,
    guardB] using same

theorem repair_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size head cursor : BitVec 64)
    (lds : List (List (BitVec 8)))
    (window : WriteWindow (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge) 8) :
    AccessPlan mem (merged ra size head cursor) lds repairBlock.body := by
  simp only [repairBlock,bf_allocateX7548Seg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  apply window.sd rfl ?_
  simp [eaddrM,mkLine,decodeM,listed,merged,srcVal,lookupG,
    Functions.sign_extend,Sail.BitVec.signExtend,Layout.off_bf_small_merge]

theorem repaired_access {ra size c} (input : RepairInput ra size c) :
    ChainAccess c.σ.mem (regs ra size) (loads size c) repairBlocks := by
  apply ChainAccess.append_eval (state := SegEvalState.init (regs ra size) (loads size c))
    (left := entryBlocks) (right := [repairTest,repairBlock] ++ popReturnBlocks)
  · change ChainAccess c.σ.mem (regs ra size) (loads size c) entryBlocks
    apply entry_access _ _ _ _ _ input.headWrite.read (read8_pins _ _) input.small
    simpa only [read8_value,first,word] using input.head
  · simp only [loads,entry_eval,read8_value]
    change ChainAccess c.σ.mem (listed ra size (first size c)) _ _
    apply ChainAccess.cons (b := repairTest) ⟨merge_access _ _ _ _ _ _ input.mergeRead (read8_pins _ _),?_⟩
    · rw [repair_test_log,repair_test_regs,repair_test_loads]
      simp only [read8_value]
      change ChainAccess c.σ.mem (merged ra size (first size c) (cursor size c)) _ _
      apply ChainAccess.cons ⟨repair_access _ _ _ _ _ _ input.mergeWrite,True.intro⟩
      rw [repair_log,repair_regs,repair_loads]
      apply pop_return_access _ _ _ _ _ _ _ input.nextRead input.headWrite
      · exact lpins8_writeLog (read8_pins _ _) input.nextOutside
      · apply lpins8_writeLog (lpins8_writeLog (read8_pins _ _) input.counterRepairOutside)
        simpa only [read8_value,next,word] using input.counterOutside
      · simpa only [read8_value,next,word] using input.tail
      · exact input.aligned
    · apply repair_test_control
      simpa only [read8_value,cursor,first,word] using input.merge

abbrev RepairPost (ra size : BitVec 64) (before after : Config) :=
  Post ra size before after repairBlocks (repairLog size ++ effect size before)

/-- Complete exact-size allocation when removing the merge cursor's node:
execute its repair store, the common pop/accounting suffix and native return. -/
theorem allocate_repair {ra size c} (input : RepairInput ra size c) :
    FnSummary pc (fun d => d = c) (RepairPost ra size c) := by
  have facts := chainPlan_facts (repair_code_facts input.code) (repaired_access input)
  have summary := block_summary repairBlocks pc (regs ra size) (loads size c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,10]; decide,
      facts,repair_chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,repair_endpoint _ _ _ _ _ _ input.aligned]
  · have pins := post.regs
    rw [loads,repair_registers] at pins
    simp only [read8_value] at pins
    exact gholds_lookup _ pins (return_value _ _ _ _ _ _)
  · rw [post.memory,loads,repair_writes]
    simp only [effect,next,total,word,read8_value]

/-- The repaired path uses the same real accounting cell and update. -/
theorem RepairPost.counter {ra size before after} (post : RepairPost ra size before after) :
    total after = total before - 1#64 - size := by
  unfold total word
  rw [post.memory]
  exact word_writeLog_at before.σ.mem _ 2 Layout.sym_caml_fl_cur_wsz _ rfl True.intro

/-- The repaired route removes the same selected list head. -/
theorem RepairPost.head {ra size before after} (post : RepairPost ra size before after)
    (outside : OutLRange [((slot size).toNat,8,next size before)] Layout.sym_caml_fl_cur_wsz 8) :
    first size after = next size before := by
  unfold first word
  rw [post.memory]
  apply word_writeLog_at before.σ.mem _ 1 (slot size).toNat _ rfl
  exact ⟨outside.1.elim Or.inr Or.inl,True.intro⟩

/-- The merge cursor is repaired to the list-head cell itself. -/
theorem RepairPost.cursor {ra size before after} (post : RepairPost ra size before after)
    (headWindow : WriteWindow (slot size) 8)
    (outside : OutLRange (repairLog size) Layout.sym_caml_fl_cur_wsz 8) :
    BestFitSmall.cursor size after = slot size := by
  have address : (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat =
      (slot size).toNat + 8 := by
    have bound := headWindow.upper
    change (slot size + 8#64).toNat = (slot size).toNat + 8
    bv_omega
  unfold BestFitSmall.cursor word
  rw [post.memory]
  apply word_writeLog_at before.σ.mem _ 0 _ _ rfl
  refine ⟨Or.inr ?_,⟨outside.1.elim Or.inr Or.inl,True.intro⟩⟩
  exact Nat.le_of_eq address.symm

/-- Additional initial conditions needed only when the observed cursor
matches the removed head. No branch choice or future run is supplied. -/
structure RepairConditions (size : BitVec 64) (c : Config) : Prop where
  mergeWrite : WriteWindow (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge) 8
  nextOutside : OutLRange (repairLog size) (first size c).toNat 8
  counterOutside : OutLRange (repairLog size) Layout.sym_caml_fl_cur_wsz 8

structure NonemptyInput (ra size : BitVec 64) (c : Config) : Prop extends BaseInput ra size c where
  repair : cursor size c = first size c → RepairConditions size c

def selectedBlocks (size : BitVec 64) (c : Config) : List BBlock :=
  if cursor size c = first size c then repairBlocks else blocks

def selectedEffect (size : BitVec 64) (c : Config) : List WEntry :=
  if cursor size c = first size c then repairLog size ++ effect size c else effect size c

abbrev NonemptyPost (ra size : BitVec 64) (before after : Config) :=
  Post ra size before after (selectedBlocks size before) (selectedEffect size before)

/-- Complete exact-size small-list allocation with a nonempty successor,
choosing whether to repair the cursor from the actual initial memory. -/
theorem allocate_nonempty {ra size c} (input : NonemptyInput ra size c) :
    FnSummary pc (fun d => d = c) (NonemptyPost ra size c) := by
  change FnSummary pc (fun d => d = c)
    (fun after => Post ra size c after (selectedBlocks size c) (selectedEffect size c))
  by_cases repair : cursor size c = first size c
  · have conditions := input.repair repair
    have run := allocate_repair
      (⟨input.toBaseInput,repair,conditions.mergeWrite,conditions.nextOutside,conditions.counterOutside⟩ :
        RepairInput ra size c)
    simp only [selectedBlocks,selectedEffect,repair,ite_true]
    exact run
  · have run := allocate (⟨input.toBaseInput,repair⟩ : Input ra size c)
    simp only [selectedBlocks,selectedEffect,repair,ite_false]
    exact run

end OCaml.Vm.Gc.BestFitSmall
