import OCaml.Vm.Gc.Generated.BestFitBitmap
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.BestFitBitmap
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The ELF bitmap is an aligned four-byte RAM cell. -/
theorem bitmap_window : WriteWindow (BitVec.ofNat 64 Layout.sym_bf_small_map) 4 := by
  constructor <;> decide

def loads (c : Config) := [read4 c.σ.mem Layout.sym_bf_small_map]

theorem access (c : Config) (size : BitVec 64) :
    ChainAccess c.σ.mem (regs size) (loads c) blocks := by
  apply ChainAccess.cons (b := block) ⟨?_,True.intro⟩ ChainAccess.nil
  simp only [block,bf_allocateX7458Seg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply bitmap_window.read.lw rfl ?_ (read4_pins _ _)
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_bf_small_map]
  · apply bitmap_window.sw rfl ?_
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_bf_small_map]

/-- Fixed-size index validation for the allocator's sixteen small classes.
The statement is independent of the bitmap value and of memory. -/
theorem mask_small (size : BitVec 64) (positive : 0 < size.toNat)
    (small : size.toNat ≤ Layout.bf_small_count) :
    (mask size).setWidth 32 = (1#32 <<< (size.toNat - 1)) := by
  have bounded : ∀ n, n < Layout.bf_small_count + 1 → 1 ≤ n →
      (mask (BitVec.ofNat 64 n)).setWidth 32 = (1#32 <<< (n - 1)) := by decide
  have result := bounded size.toNat (by omega) positive
  simpa using result

/-- The emitted LW/SLLW/AND/SW computes ordinary bitmap bit clearing. -/
theorem cleared_word (c : Config) (size : BitVec 64) (positive : 0 < size.toNat)
    (small : size.toNat ≤ Layout.bf_small_count) :
    (cleared size (bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map))).setWidth 32 =
      word32 c Layout.sym_bf_small_map &&& ~~~(1#32 <<< (size.toNat - 1)) := by
  rw [cleared,BitVec.setWidth_and,BitVec.setWidth_not (by decide),mask_small size positive small,read4_value]
  rw [truncate_signed_word]
  rfl

structure Input (size : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (regs size)
  positive : 0 < size.toNat
  small : size.toNat ≤ Layout.bf_small_count

/-- The bitmap block has cleared the selected small-size bit and is parked
at the common accounting/return suffix, preserving its nonwritten registers. -/
structure Post (size : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs size) (loads before) before after
  pc : PCAt exitPc after
  memory : after.σ.mem = writeLog before.σ.mem
    [(Layout.sym_bf_small_map,4,cleared size (bytesVal .lw (read4 before.σ.mem Layout.sym_bf_small_map)))]
  bitmap : word32 after Layout.sym_bf_small_map =
    word32 before Layout.sym_bf_small_map &&& ~~~(1#32 <<< (size.toNat - 1))
  code : Code.Bf_allocateLoaded after.σ.mem

/-- Execute the actual bitmap update for an emptied small-list slot. -/
theorem clear {size c} (input : Input size c) :
    FnSummary pc (fun d => d = c) (Post size c) := by
  have facts := chainPlan_facts (code_facts input.code) (access c size)
  have summary := block_summary blocks pc (regs size) (loads c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [10]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = writeLog c.σ.mem
      [(Layout.sym_bf_small_map,4,cleared size (bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map)))] := by
    rw [post.memory,loads,writes]
  refine ⟨post,?_,memory,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,endpoint]
  · unfold word32
    rw [memory,word32_writeLog]
    exact cleared_word c size input.positive input.small

end OCaml.Vm.Gc.BestFitBitmap
