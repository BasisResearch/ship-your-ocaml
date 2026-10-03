import OCaml.Vm.Gc.EnqueueAccess
import OCaml.Vm.Gc.OldifyReturn

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Normalize the six actual stores using the concrete source and head reads. -/
theorem EnqueueRunPost.memory_effect {q qs pl root size before after}
    (post : EnqueueRunPost q qs pl root size before after)
    (input : EnqueueInput q qs pl root size before) :
    after.σ.mem = writeLog before.σ.mem
      (Enqueue.effect q.source q.target root (word before q.source.toNat) (head qs)) := by
  rw [post.machine.memory, Enqueue.writes, enqueue_loadedFirst input.separate,
    enqueue_loadedNext input.queue input.headOutside]

theorem EnqueueRunPost.code {q qs pl root size before after}
    (post : EnqueueRunPost q qs pl root size before after)
    (input : EnqueueInput q qs pl root size before) : Code.Caml_oldify_oneLoaded after.σ.mem :=
  oldifyCode_after input.code
    (chainPlan_facts (Enqueue.code_facts input.code)
      (enqueue_access q root size before input.windows input.large)) post.machine

theorem EnqueueRunPost.return_input {q qs pl root size sp before after}
    (post : EnqueueRunPost q qs pl root size before after)
    (input : EnqueueInput q qs pl root size before)
    (stack : gprGet before.σ 2 = some sp)
    (windows : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8)
    (same : OldifyReturn.SavedSame sp before after)
    (aligned : (OldifyReturn.returnWord sp before).toNat % 4 = 0) :
    OldifyReturn.Input sp after := by
  have keep : gprGet after.σ 2 = gprGet before.σ 2 := by
    apply post.machine.frame Register.x2 (by decide)
    intro n hn
    have h := Enqueue.written n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  refine ⟨post.machine.good, post.machine.minstret, post.machine.tick, post.code input,
    ⟨keep.trans stack, True.intro⟩, windows, ?_⟩
  rw [same.returnWord]
  exact aligned

/-- The allocation-return queue path has returned natively, retaining the
pending payload's first field and the new intrusive queue node. Allocation
itself and the original native prologue remain separate obligations. -/
structure EnqueueReturned (q : PendingCopy) (qs : List PendingCopy) (pl : Place)
    (root sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem
    (Enqueue.effect q.source q.target root (word before q.source.toNat) (head qs))
  data : EnqueuePost q qs pl root (word before q.source.toNat) after
  pc : PCAt (OldifyReturn.returnWord sp before) after
  registers : GHolds after.σ (OldifyReturn.restored sp before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ wrChain Enqueue.blocks ++ wrChain OldifyReturn.blocks, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem enqueue_return {q qs pl root size sp c} (input : EnqueueInput q qs pl root size c)
    (stack : gprGet c.σ 2 = some sp)
    (windows : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8)
    (outside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange (Enqueue.effect q.source q.target root (word c q.source.toNat) (head qs))
        (sp + BitVec.ofNat 64 off).toNat 8)
    (aligned : (OldifyReturn.returnWord sp c).toNat % 4 = 0) :
    FnSummary Enqueue.pc (fun d => d = c) (EnqueueReturned q qs pl root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (enqueue_machine input).run
  intro middle enqueued
  have memory := enqueued.memory_effect input
  have same := OldifyReturn.SavedSame.of_writeLog memory outside
  have pc : PCAt OldifyReturn.pc middle := by
    rw [PCAt, enqueued.machine.pc, Enqueue.endpoint]
    rfl
  obtain ⟨after, run, returned⟩ :=
    (OldifyReturn.return_machine (enqueued.return_input input stack windows same aligned)).run
      middle ⟨pc, rfl⟩
  refine ⟨after, run, ⟨returned.machine.good, returned.machine.minstret, returned.machine.tick,
    returned.code, returned.memory.trans memory, enqueued.data.memory_eq returned.memory,
    ?_, ?_, returned.machine.output.trans enqueued.machine.output, ?_⟩⟩
  · simpa only [same.returnWord] using returned.pc
  · simpa only [same.restored] using returned.registers
  · intro r noise untouched
    exact (returned.machine.frame r noise (fun n hn => untouched n (List.mem_append_right _ hn))).trans
      (enqueued.machine.frame r noise (fun n hn => untouched n (List.mem_append_left _ hn)))

end OCaml.Vm.Gc.WorkQueue
