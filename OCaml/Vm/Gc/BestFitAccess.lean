import OCaml.Vm.Gc.Generated.BestFitSmall
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.BestFitSmall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem size_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size : BitVec 64)
    (lds : List (List (BitVec 8))) : AccessPlan mem (regs ra size) lds sizeBlock.body := by
  simp only [sizeBlock,bf_allocateX73acFSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro

theorem size_control (ra size : BitVec 64) (lds : List (List (BitVec 8)))
    (small : size.toNat ≤ Layout.bf_small_count) :
    TermFactsO (runGM sizeBlock.body (regs ra size) lds) sizeBlock.term := by
  rw [size_regs]
  simp [sizeBlock,bf_allocateX73acFSeg,TermFactsO,TermFactsT,sized,srcVal,lookupG,
    guardB,Functions.zopz0zI_u,Sail.BitVec.toNatInt,Layout.bf_small_count]
  change size.toNat ≤ 16 at small
  omega

theorem list_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (window : ReadWindow (slot size) 8) (pins : LPins8 mem (slot size).toNat b) :
    AccessPlan mem (sized ra size) (b::lds) listBlock.body := by
  simp only [listBlock,bf_allocateX73b4TSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  apply window.ld rfl ?_ pins
  simp [eaddrM,mkLine,decodeM,sized,slot,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,
    imm20Of,shamtOf,Sail.BitVec.extractLsb,Functions.sign_extend,Sail.BitVec.signExtend,
    Layout.sym_bf_small_fl,Layout.bf_small_size]
  rfl

theorem list_control (ra size : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (nonnull : bytesVal .ld b ≠ 0) :
    TermFactsO (runGM listBlock.body (sized ra size) (b::lds)) listBlock.term := by
  rw [list_regs]
  simpa [listBlock,bf_allocateX73b4TSeg,TermFactsO,TermFactsT,listed,srcVal,lookupG,
    guardB] using nonnull

theorem merge_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size head : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (window : ReadWindow (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge) 8)
    (pins : LPins8 mem (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat b) :
    AccessPlan mem (listed ra size head) (b::lds) mergeBlock.body := by
  simp only [mergeBlock,bf_allocateX7440FSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  apply window.ld rfl ?_ pins
  simp [eaddrM,mkLine,decodeM,listed,srcVal,lookupG,
    Functions.sign_extend,Sail.BitVec.signExtend,Layout.off_bf_small_merge]

theorem merge_control (ra size head : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (different : bytesVal .ld b ≠ head) :
    TermFactsO (runGM mergeBlock.body (listed ra size head) (b::lds)) mergeBlock.term := by
  rw [merge_regs]
  simpa [mergeBlock,bf_allocateX7440FSeg,TermFactsO,TermFactsT,listed,merged,srcVal,lookupG,
    guardB] using different

theorem pop_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size head cursor : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (read : ReadWindow head 8) (write : WriteWindow (slot size) 8)
    (pins : LPins8 mem head.toNat b) :
    AccessPlan mem (merged ra size head cursor) (b::lds) popBlock.body := by
  simp only [popBlock,bf_allocateX7448TSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply read.ld rfl ?_ pins
    simp [eaddrM,mkLine,decodeM,listed,merged,srcVal,lookupG,
      Functions.sign_extend,Sail.BitVec.signExtend]
  · apply write.sd rfl ?_
    simp [eaddrM,mkLine,decodeM,listed,merged,slot,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,
      Functions.sign_extend,Sail.BitVec.signExtend]

theorem pop_control (ra size head cursor : BitVec 64) (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (nonnull : bytesVal .ld b ≠ 0) :
    TermFactsO (runGM popBlock.body (merged ra size head cursor) (b::lds)) popBlock.term := by
  rw [pop_regs]
  simpa [popBlock,bf_allocateX7448TSeg,TermFactsO,TermFactsT,popped,srcVal,lookupG,
    guardB] using nonnull

/-- ELF-derived free-word counter, read and written by the exact-size path. -/
theorem counter_window : WriteWindow (BitVec.ofNat 64 Layout.sym_caml_fl_cur_wsz) 8 := by
  constructor <;> decide

theorem return_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size head cursor next : BitVec 64)
    (b : List (BitVec 8)) (pins : LPins8 mem Layout.sym_caml_fl_cur_wsz b) :
    AccessPlan mem (popped ra size head cursor next) [b] returnBlock.body := by
  simp only [returnBlock,bf_allocateX747cSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply counter_window.read.ld rfl ?_ pins
    simp [eaddrM,mkLine,decodeM,popped,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_fl_cur_wsz]
  · apply counter_window.sd rfl ?_
    simp [eaddrM,mkLine,decodeM,popped,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_fl_cur_wsz]

theorem return_control (ra size head cursor next : BitVec 64) (b : List (BitVec 8))
    (aligned : ra.toNat % 4 = 0) :
    TermFactsO (runGM returnBlock.body (popped ra size head cursor next) [b]) returnBlock.term := by
  change (Sail.BitVec.update (srcVal 1 (finalRegs ra size head cursor next b) +
    Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
  rw [finalRegs,return_ra,ret_tgt ra aligned]
  exact aligned

end OCaml.Vm.Gc.BestFitSmall
