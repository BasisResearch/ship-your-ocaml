import OCaml.Vm.Gc.Generated.BestFitFinish
import OCaml.Vm.Gc.BestFitAccess

namespace OCaml.Vm.Gc.BestFitFinish
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def loads (c : Config) := [read8 c.σ.mem Layout.sym_caml_fl_cur_wsz]
def effect (size : BitVec 64) (c : Config) : List WEntry :=
  [(Layout.sym_caml_fl_cur_wsz,8,word c Layout.sym_caml_fl_cur_wsz - 1#64 - size)]

theorem access (c : Config) (ra size head : BitVec 64) (aligned : ra.toNat % 4 = 0) :
    ChainAccess c.σ.mem (regs ra size head) (loads c) blocks := by
  apply ChainAccess.cons (b := block) ⟨?_,?_⟩ ChainAccess.nil
  · simp only [block,BestFitSmall.returnBlock,bf_allocateX747cSeg,List.getD_cons_zero,AccessPlan]
    chain_facts True.intro
    · apply BestFitSmall.counter_window.read.ld rfl ?_ (read8_pins _ _)
      simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
        Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_fl_cur_wsz]
    · apply BestFitSmall.counter_window.sd rfl ?_
      simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
        Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_fl_cur_wsz]
  · change (Sail.BitVec.update (srcVal 1 (runGM block.body (regs ra size head) (loads c)) +
      Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [loads,return_ra,ret_tgt ra aligned]
    exact aligned

structure Input (ra size head : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (regs ra size head)
  aligned : ra.toNat % 4 = 0

/-- The allocator's common native return has updated free-word accounting
and converted its selected payload address to the header pointer. -/
structure Post (ra size head : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs ra size head) (loads before) before after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (head - BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem (effect size before)
  code : Code.Bf_allocateLoaded after.σ.mem

theorem finish {ra size head c} (input : Input ra size head c) :
    FnSummary pc (fun d => d = c) (Post ra size head c) := by
  have facts := chainPlan_facts (code_facts input.code) (access c ra size head input.aligned)
  have summary := block_summary blocks pc (regs ra size head) (loads c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,10,15]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,endpoint _ _ _ _ input.aligned]
  · exact gholds_lookup _ post.regs (result _ _ _ _)
  · rw [post.memory,loads,writes]
    simp only [effect,read8_value,word]

end OCaml.Vm.Gc.BestFitFinish
