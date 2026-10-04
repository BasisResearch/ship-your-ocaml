import OCaml.Vm.Gc.Generated.BestFitFallback
import OCaml.Vm.Gc.FfsZero
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Primitives.Word32Access

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def loads (c : Config) := [read4 c.σ.mem Layout.sym_bf_small_map]
def bitmap (c : Config) := bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map)

theorem bitmap_window : ReadWindow (BitVec.ofNat 64 Layout.sym_bf_small_map) 4 := by
  constructor <;> decide

/-- A zero bitmap observation supplies the actual filtered-zero branch. -/
theorem filtered_zero {R : Nat → BitVec 64} {c : Config} (zero : bytesT c.σ.mem Layout.sym_bf_small_map 4 = 0) :
    filtered (R 10) (bitmap c) = 0 := by
  simp only [filtered,bitmap,read4_value,zero]
  simp [Functions.sign_extend,Sail.BitVec.signExtend]

/-- The native stack supplies the three save windows decoded from the
fallback prologue; the bitmap is a total four-byte observation. -/
structure StackConditions (R : Nat → BitVec 64) : Prop where
  windows : ∀ cell ∈ saves, WriteWindow (frameSp R + BitVec.ofNat 64 cell.2) 8

structure Input (R : Nat → BitVec 64) (c : Config) : Prop extends StackConditions R where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (regs R)

macro "fallback_address" : tactic => `(tactic|
  simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,
    imm20Of,Functions.sign_extend,Sail.BitVec.signExtend,frameSp,frameSize,
    Layout.sym_bf_small_map,saves,BitVec.sub_eq_add_neg])

theorem access {R c} (input : Input R c) : ChainAccess c.σ.mem (regs R) (loads c) blocks := by
  apply ChainAccess.cons (b := block) ⟨?_,True.intro⟩ ChainAccess.nil
  simp only [block,bf_allocateX73ccSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply bitmap_window.lw rfl ?_ (read4_pins _ _)
    fallback_address
  · apply (input.windows (saves[0]!) (by decide)).sd rfl
    fallback_address
  · apply (input.windows (saves[1]!) (by decide)).sd rfl
    fallback_address
  · apply (input.windows (saves[2]!) (by decide)).sd rfl
    fallback_address

structure Prepared (R : Nat → BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs R) (loads before) before after
  pc : PCAt call.pc after
  registers : GHolds after.σ (atCall R (bitmap before))
  memory : after.σ.mem = writeLog before.σ.mem (effect R (bitmap before))
  code : Code.Bf_allocateLoaded after.σ.mem

/-- Execute the fallback bitmap filter and native prologue to the actual
ffs call site. All writes and load observations come from generated code. -/
theorem prepare {R c} (input : Input R c) :
    FnSummary pc (fun d => d = c) (Prepared R c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs R) (loads c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,2,10]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,endpoint]
  · simpa only [loads,registers,bitmap] using post.regs
  · rw [post.memory,loads,writes]
    rfl

/-- The zero bitmap helper has returned to the real fallback continuation.
The size and bitmap remain in the native frame installed by this prefix. -/
structure Searched (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt call.link after
  result : gprGet after.σ 10 = some 0
  stack : gprGet after.σ 2 = some (frameSp R)
  memory : after.σ.mem = writeLog before.σ.mem (effect R (bitmap before))
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,10,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Real fallback prologue, linking call and zero-input ffs execution. -/
theorem search_zero {R c} (input : Input R c) (ffsCode : Code.FfsLoaded c.σ.mem)
    (empty : filtered (R 10) (bitmap c) = 0) :
    FnSummary pc (fun d => d = c) (Searched R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare input).run
  intro middle prepared
  have ffsCode' : Code.FfsLoaded middle.σ.mem :=
    image_after Code.ffs_transport (by decide) ffsCode
      (chainPlan_facts (code_facts input.code) (access input)) prepared.machine
  let pins : GRegs := [(2,frameSp R),(10,filtered (R 10) (bitmap c))]
  have holds : GHolds middle.σ pins :=
    ⟨gholds_lookup _ prepared.registers rfl,gholds_lookup _ prepared.registers rfl,True.intro⟩
  have callSummary := call_summary call_shape call_decode middle (call_pins prepared.code)
    prepared.machine.good prepared.machine.tick prepared.machine.minstret pins holds
    (by change KeysOK [2,10]; decide)
    (by change ∀ n ∈ [2,10], n ≠ 1; decide)
  obtain ⟨callee,callRun,called⟩ := callSummary.run middle ⟨prepared.pc,rfl⟩
  have ffsInput : FfsZero.Input call.link callee :=
    ⟨called.good,called.tick,called.minstret,called.mem ▸ ffsCode',
      ⟨called.ra,empty ▸ gholds_lookup _ called.registers rfl,True.intro⟩,by decide⟩
  have calleePc : PCAt FfsZero.pc callee := by simpa only [PCAt,call_target] using called.pc
  obtain ⟨after,run,returned⟩ := (FfsZero.zero ffsInput).run callee ⟨calleePc,rfl⟩
  have memory : after.σ.mem = middle.σ.mem := returned.memory.trans called.mem
  refine ⟨after,callRun.trans run,⟨returned.machine.good,returned.machine.tick,returned.machine.minstret,
    returned.pc,returned.result,?_,memory.trans prepared.memory,memory ▸ prepared.code,
    returned.machine.output.trans (called.output.trans prepared.machine.output),?_⟩⟩
  · have same := returned.machine.frame Register.x2 (by decide)
      (fun n hn => by
        have h := FfsZero.written n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl <;> decide)
    have stack : gprGet callee.σ 2 = some (frameSp R) := gholds_lookup _ called.registers rfl
    exact same.trans stack
  · intro r noise outside
    apply (returned.machine.frame r noise (fun n hn => outside n (by
      have h := FfsZero.written n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl | rfl <;> simp))).trans
    apply (called.frame r noise (by simp [wrChain]) (outside 1 (by simp))).trans
    apply prepared.machine.frame r noise
    intro n hn
    apply outside n
    have h := written n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with rfl | rfl | rfl | rfl <;> simp

end OCaml.Vm.Gc.BestFitFallback
