import OCaml.Vm.Gc.Generated.BestFitLargeReturn
import OCaml.Vm.Gc.BestFitAccess

namespace OCaml.Vm.Gc.BestFitLargeReturn
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def loads (sp : BitVec 64) (c : Config) :=
  [read8 c.σ.mem Layout.sym_caml_fl_cur_wsz,
   read8 c.σ.mem (sp + BitVec.ofNat 64 sizeOffset).toNat,
   read8 c.σ.mem (sp + BitVec.ofNat 64 requestOffset).toNat,
   read8 c.σ.mem (sp + BitVec.ofNat 64 returnOffset).toNat]
def savedSize (sp : BitVec 64) (c : Config) := word c (sp + BitVec.ofNat 64 sizeOffset).toNat
def savedRequest (sp : BitVec 64) (c : Config) := word c (sp + BitVec.ofNat 64 requestOffset).toNat
def returnWord (sp : BitVec 64) (c : Config) := word c (sp + BitVec.ofNat 64 returnOffset).toNat
def counted (sp : BitVec 64) (c : Config) := savedSize sp c + word c Layout.sym_caml_fl_cur_wsz - savedRequest sp c

structure Windows (sp : BitVec 64) : Prop where
  size : ReadWindow (sp + BitVec.ofNat 64 sizeOffset) 8
  request : ReadWindow (sp + BitVec.ofNat 64 requestOffset) 8
  returnWord : ReadWindow (sp + BitVec.ofNat 64 returnOffset) 8

structure Input (sp hp : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (regs sp hp)
  windows : Windows sp
  aligned : (returnWord sp c).toNat % 4 = 0

macro "large_return_address" : tactic => `(tactic|
  simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,
    imm20Of,Functions.sign_extend,Sail.BitVec.signExtend,
    Layout.sym_caml_fl_cur_wsz,sizeOffset,requestOffset,returnOffset])

theorem access {sp hp c} (input : Input sp hp c) :
    ChainAccess c.σ.mem (regs sp hp) (loads sp c) blocks := by
  apply ChainAccess.cons (b := block) ⟨?_,?_⟩ ChainAccess.nil
  · simp only [block,bf_allocateX7560Seg,List.getD_cons_zero,AccessPlan]
    chain_facts True.intro
    · apply BestFitSmall.counter_window.read.ld rfl ?_ (read8_pins _ _)
      large_return_address
    · apply input.windows.size.ld rfl ?_ (read8_pins _ _)
      large_return_address
    · apply input.windows.request.ld rfl ?_ (read8_pins _ _)
      large_return_address
    · apply input.windows.returnWord.ld rfl ?_ (read8_pins _ _)
      large_return_address
    · apply BestFitSmall.counter_window.sd rfl
      large_return_address
  · change (Sail.BitVec.update (srcVal 1 (runGM block.body (regs sp hp) (loads sp c)) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [loads,return_ra,read8_value]
    change (Sail.BitVec.update (returnWord sp c + Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [ret_tgt _ input.aligned]
    exact input.aligned

structure Post (sp hp : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs sp hp) (loads sp before) before after
  pc : PCAt (returnWord sp before) after
  result : gprGet after.σ 10 = some hp
  stack : gprGet after.σ 2 = some (sp + frameSize)
  memory : after.σ.mem = writeLog before.σ.mem [(Layout.sym_caml_fl_cur_wsz,8,counted sp before)]
  counter : word after Layout.sym_caml_fl_cur_wsz = counted sp before
  code : Code.Bf_allocateLoaded after.σ.mem

/-- Large-block allocation restores its native caller and accounts for only
the requested words, after the split helper temporarily removed the old block. -/
theorem finish {sp hp c} (input : Input sp hp c) :
    FnSummary pc (fun d => d = c) (Post sp hp c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs sp hp) (loads sp c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [2,10]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = writeLog c.σ.mem [(Layout.sym_caml_fl_cur_wsz,8,counted sp c)] := by
    rw [post.memory,loads,writes]
    simp only [effect,counted,savedSize,savedRequest,read8_value,word]
  refine ⟨post,?_,?_,?_,memory,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,endpoint _ _ _ _ _ _ (by simpa only [read8_value,returnWord,word] using input.aligned)]
    simp only [read8_value,returnWord,word]
  · have pins := post.regs
    change GHolds after.σ (runGM block.body (regs sp hp) (loads sp c)) at pins
    exact gholds_lookup _ pins (return_result _ _ _ _ _ _)
  · have pins := post.regs
    change GHolds after.σ (runGM block.body (regs sp hp) (loads sp c)) at pins
    exact gholds_lookup _ pins (return_stack _ _ _ _ _ _)
  · rw [word,memory]
    exact word_writeLog_at _ _ 0 _ _ rfl True.intro

end OCaml.Vm.Gc.BestFitLargeReturn
