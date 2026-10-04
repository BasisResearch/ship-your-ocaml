import OCaml.Vm.Gc.Generated.BestFitSplit
import OCaml.Vm.Gc.BestFitAccess

namespace OCaml.Vm.Gc.BestFitSplit
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem head_access (large : Bool) (mem : Std.ExtHashMap Nat (BitVec 8))
    (ra request source : BitVec 64) (bh bt : List (BitVec 8))
    (window : ReadWindow (headerAddr source) 8)
    (hp : LPins8 mem (headerAddr source).toNat bh)
    (tp : LPins8 mem Layout.sym_caml_fl_cur_wsz bt) :
    AccessPlan mem (regs ra request source) [bh,bt] (headBlock large).body := by
  cases large
  all_goals simp only [headBlock,Bool.false_eq_true,eq_self,ite_false,ite_true,
    bf_splitX6150FSeg,bf_splitX6150TSeg,List.getD_cons_zero,AccessPlan]
  all_goals chain_facts True.intro
  all_goals first
  | apply window.ld rfl ?_ hp
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,headerAddr,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.header_bytes,BitVec.sub_eq_add_neg]
  | apply BestFitSmall.counter_window.read.ld rfl ?_ tp
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_fl_cur_wsz]
  | apply BestFitSmall.counter_window.sd rfl ?_
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_fl_cur_wsz]

def route (request header : BitVec 64) : Bool := decide (limit.toNat < (delta request header).toNat)

theorem head_control (ra request source : BitVec 64) (bh bt : List (BitVec 8)) :
    TermFactsO (runGM (headBlock (route request (bytesVal .ld bh))).body
      (regs ra request source) [bh,bt]) (headBlock (route request (bytesVal .ld bh))).term := by
  rw [head_regs]
  generalize he : route request (bytesVal .ld bh) = large
  have choice := he
  simp only [route] at choice
  cases large
  all_goals simp [headBlock,bf_splitX6150FSeg,bf_splitX6150TSeg,TermFactsO,TermFactsT,
    afterHead,srcVal,lookupG,guardB,Functions.zopz0zI_u,Sail.BitVec.toNatInt]
  all_goals simp only [decide_eq_false_iff_not,decide_eq_true_eq] at choice
  all_goals omega

theorem small_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra request source header : BitVec 64) :
    AccessPlan mem (afterHead ra request source header) [] smallBlock.body := by
  simp only [smallBlock,bf_splitX6188Seg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro

theorem return_access (large : Bool) (mem : Std.ExtHashMap Nat (BitVec 8))
    (ra request source header : BitVec 64) (window : WriteWindow (headerAddr source) 8) :
    AccessPlan mem (atReturn large ra request source header) [] returnBlock.body := by
  simp only [returnBlock,bf_splitX6190Seg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  apply window.sd rfl ?_
  cases large <;> change source + (-BitVec.ofNat 64 Layout.header_bytes) = headerAddr source
  all_goals simp only [headerAddr,Layout.header_bytes,BitVec.sub_eq_add_neg]
  all_goals rfl

theorem return_control (large : Bool) (ra request source header : BitVec 64)
    (aligned : ra.toNat % 4 = 0) :
    TermFactsO (runGM returnBlock.body (atReturn large ra request source header) []) returnBlock.term := by
  change (Sail.BitVec.update (srcVal 1 (runGM returnBlock.body (atReturn large ra request source header) []) +
    Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
  rw [return_ra,ret_tgt ra aligned]
  exact aligned

end OCaml.Vm.Gc.BestFitSplit
