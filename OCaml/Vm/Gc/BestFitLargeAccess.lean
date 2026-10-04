import OCaml.Vm.Gc.Generated.BestFitLarge
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.Readback

namespace OCaml.Vm.Gc.BestFitLarge
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def size (sp : BitVec 64) (c : Config) := word c (sp + BitVec.ofNat 64 sizeOffset).toNat
def bits (sp : BitVec 64) (c : Config) := word c (sp + BitVec.ofNat 64 bitmapOffset).toNat
def least (c : Config) := word c Layout.sym_bf_large_least
def header (c : Config) := word c (least c - BitVec.ofNat 64 Layout.header_bytes).toNat
def loads (sp : BitVec 64) (c : Config) :=
  [read8 c.σ.mem (sp + BitVec.ofNat 64 bitmapOffset).toNat,
   read8 c.σ.mem (sp + BitVec.ofNat 64 sizeOffset).toNat,
   read8 c.σ.mem Layout.sym_bf_large_least,
   read8 c.σ.mem (least c - BitVec.ofNat 64 Layout.header_bytes).toNat]

structure Windows (sp : BitVec 64) : Prop where
  bitmap : WriteWindow (sp + BitVec.ofNat 64 bitmapOffset) 8
  size : WriteWindow (sp + BitVec.ofNat 64 sizeOffset) 8

/-- Initial memory and geometry for the least-large-block split route. -/
structure Conditions (sp : BitVec 64) (c : Config) : Prop where
  stack : Windows sp
  headerWrite : WriteWindow (least c - BitVec.ofNat 64 Layout.header_bytes) 8
  nonnull : least c ≠ 0
  small : (size sp c).toNat ≤ Layout.bf_small_count
  large : (size sp c).toNat + (Layout.bf_small_count + 1) < (BestFitSplit.sizeWord (header c)).toNat

structure Input (sp : BitVec 64) (c : Config) : Prop extends Conditions sp c where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (regs sp)

theorem Conditions.of_memory {sp} {before after : Config} (memory : after.σ.mem = before.σ.mem)
    (conditions : Conditions sp before) : Conditions sp after := by
  refine ⟨conditions.stack,?_,?_,?_,?_⟩
  · simpa only [least,word,memory] using conditions.headerWrite
  · simpa only [least,word,memory] using conditions.nonnull
  · simpa only [size,word,memory] using conditions.small
  · simpa only [size,header,least,word,memory] using conditions.large

macro "large_address" : tactic => `(tactic|
  simp [eaddrM,mkLine,decodeM,regs,restored,leasted,headered,srcVal,lookupG,eraseG,stepGM,
    stepLdsM,wvalM,imm20Of,Functions.sign_extend,Sail.BitVec.signExtend,
    Layout.sym_bf_large_least,Layout.sym_bf_small_fl,Layout.header_bytes,
    bitmapOffset,sizeOffset,BitVec.sub_eq_add_neg])

theorem least_window : ReadWindow (BitVec.ofNat 64 Layout.sym_bf_large_least) 8 := by
  constructor <;> decide

theorem restore_access {sp c} (input : Input sp c) :
    AccessPlan c.σ.mem (regs sp) (loads sp c) restoreBlock.body := by
  simp only [restoreBlock,bf_allocateX73f8FSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply input.stack.bitmap.read.ld rfl ?_ (read8_pins _ _)
    large_address
  · apply input.stack.size.read.ld rfl ?_ (read8_pins _ _)
    large_address

theorem restore_control (sp : BitVec 64) (a b : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    TermFactsO (runGM restoreBlock.body (regs sp) (a::b::rest)) restoreBlock.term := by
  rw [restore_regs]
  simp [restoreBlock,bf_allocateX73f8FSeg,TermFactsO,TermFactsT,restored,srcVal,lookupG,guardB]

theorem least_access (sp bits size : BitVec 64) (c : Config) (lds : List (List (BitVec 8))) :
    AccessPlan c.σ.mem (restored sp bits size) (read8 c.σ.mem Layout.sym_bf_large_least :: lds) leastBlock.body := by
  simp only [leastBlock,bf_allocateX7410FSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  apply least_window.ld rfl ?_ (read8_pins _ _)
  large_address

theorem least_control (sp bits size : BitVec 64) (c : Config) (lds : List (List (BitVec 8)))
    (nonnull : least c ≠ 0) :
    TermFactsO (runGM leastBlock.body (restored sp bits size)
      (read8 c.σ.mem Layout.sym_bf_large_least :: lds)) leastBlock.term := by
  rw [least_regs]
  simpa [leastBlock,bf_allocateX7410FSeg,TermFactsO,TermFactsT,leasted,restored,srcVal,lookupG,
    guardB,read8_value,least,word] using nonnull

theorem header_access {sp c} (input : Input sp c) :
    AccessPlan c.σ.mem (leasted sp (bits sp c) (size sp c) (least c))
      [read8 c.σ.mem (least c - BitVec.ofNat 64 Layout.header_bytes).toNat] headerBlock.body := by
  simp only [headerBlock,bf_allocateX741cTSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  apply input.headerWrite.read.ld rfl ?_ (read8_pins _ _)
  large_address

theorem header_control {sp c} (input : Input sp c) :
    TermFactsO (runGM headerBlock.body (leasted sp (bits sp c) (size sp c) (least c))
      [read8 c.σ.mem (least c - BitVec.ofNat 64 Layout.header_bytes).toNat]) headerBlock.term := by
  rw [header_regs]
  have bound := input.small
  have large := input.large
  have nowrap : (size sp c + BitVec.ofNat 64 (Layout.bf_small_count + 1)).toNat =
      (size sp c).toNat + (Layout.bf_small_count + 1) := by
    simp only [BitVec.toNat_add]
    change ((size sp c).toNat + 17) % 2^64 = (size sp c).toNat + 17
    change (size sp c).toNat ≤ 16 at bound
    omega
  simp [headerBlock,bf_allocateX741cTSeg,TermFactsO,TermFactsT,headered,srcVal,lookupG,
    guardB,Functions.zopz0zI_u,Sail.BitVec.toNatInt,read8_value,header,word,nowrap] at large ⊢
  omega

theorem save_access {sp c} (input : Input sp c) :
    AccessPlan c.σ.mem (headered sp (bits sp c) (size sp c) (least c) (header c)) [] saveBlock.body := by
  simp only [saveBlock,bf_allocateX7550Seg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply input.stack.size.sd rfl
    large_address
  · apply input.stack.bitmap.sd rfl
    large_address

theorem access {sp c} (input : Input sp c) : ChainAccess c.σ.mem (regs sp) (loads sp c) blocks := by
  apply ChainAccess.cons ⟨restore_access input,restore_control _ _ _ _⟩
  rw [loads,restore_regs]
  simp only [read8_value]
  change ChainAccess c.σ.mem (restored sp (bits sp c) (size sp c))
    [read8 c.σ.mem Layout.sym_bf_large_least,
     read8 c.σ.mem (least c - BitVec.ofNat 64 Layout.header_bytes).toNat]
    [leastBlock,headerBlock,saveBlock]
  apply ChainAccess.cons ⟨least_access _ _ _ _ _,least_control _ _ _ _ _ input.nonnull⟩
  rw [least_regs]
  simp only [read8_value]
  change ChainAccess c.σ.mem (leasted sp (bits sp c) (size sp c) (least c))
    [read8 c.σ.mem (least c - BitVec.ofNat 64 Layout.header_bytes).toNat] [headerBlock,saveBlock]
  apply ChainAccess.cons ⟨header_access input,header_control input⟩
  rw [header_regs]
  simp only [read8_value]
  change ChainAccess c.σ.mem (headered sp (bits sp c) (size sp c) (least c) (header c)) [] [saveBlock]
  exact ChainAccess.cons ⟨save_access input,True.intro⟩ ChainAccess.nil

end OCaml.Vm.Gc.BestFitLarge
