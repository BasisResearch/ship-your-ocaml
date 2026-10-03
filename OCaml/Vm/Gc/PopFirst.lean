import OCaml.Vm.Gc.QueueFirstInput

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Exact oldify writes after the pop has supplied its three loaded values. -/
def firstEffect (R : Nat → BitVec 64) (q : PendingCopy) (c : Config) :=
  ForwardedCall.effect (FirstCall.linked (FirstField.args (firstRegs R q c))) c

/-- Remaining queue links and the loaded child's forwarding word do not
alias the native/first-slot writes or the queue-head store. Heap ownership
and native-stack separation supply these finite footprint facts. -/
structure FirstSeparation (R : Nat → BitVec 64) (q : PendingCopy) (qs : List PendingCopy) (c : Config) : Prop where
  forwarding : OutWRange popFootprint (word c q.target.toNat).toNat 8
  links : LinksOutside qs (firstEffect R q c)
  head : OutLRange (firstEffect R q c) Layout.sym_oldify_todo_list 8

structure PopFirstPost (R : Nat → BitVec 64) (q : PendingCopy) (qs : List PendingCopy)
    (pl : Place) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem
    ([(Layout.sym_oldify_todo_list,8,head qs)] ++ firstEffect R q before)
  first : word after q.target.toNat = word before (word before q.target.toNat).toNat
  pc : PCAt FirstCall.setupPc after
  registers : GHolds after.σ (OldifyEntry.callerRegs (FirstCall.linked (FirstField.args (firstRegs R q before))))
  queue : View qs pl after
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,10,11,12,14,15,18,19], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared continuation after either concrete queue-pop entry. -/
theorem first_after_pop {R domain q qs pl c} (input : PopInput q qs pl c)
    (ready : FirstReady R domain q c) (separate : FirstSeparation R q qs c) :
    Vsa.Logic.Triple (PopPost q qs pl c) (PopFirstPost R q qs pl c) := by
  intro middle popped
  have child := frame_word popped.memory_frame separate.forwarding
  have callInput := popped.first_input input ready
  obtain ⟨after, run, updated⟩ := (FirstField.forwarded callInput).run middle
    ⟨popped.first_pc ready.even,rfl⟩
  have effect : ForwardedCall.effect (FirstCall.linked (FirstField.args (firstRegs R q c))) middle =
      firstEffect R q c := by
    unfold firstEffect ForwardedCall.effect
    change _ ++ [(_,8,word middle (word c q.target.toNat).toNat)] = _
    rw [child]
    rfl
  have memory : after.σ.mem = writeLog middle.σ.mem (firstEffect R q c) := by
    rw [updated.memory, effect]
  refine ⟨after, run, ⟨updated.good, updated.minstret, updated.tick, updated.code, updated.oldifyCode,
    ?_, ?_, updated.pc, updated.registers, popped.queue.frame_log memory separate.links separate.head,
    updated.output.trans popped.effects.output, ?_⟩⟩
  · rw [memory, popped.memory_effect input.queue, writeLog_append]
  · exact updated.first.trans child
  · intro r noise untouched
    apply (updated.native r noise ?_).trans (popped.effects.frame_subset (MopupPop.actual_written _) r noise ?_)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

/-- Initial queue pop followed by the shared first-field continuation. -/
theorem pop_first {R domain q qs pl c} (input : PopInput q qs pl c)
    (ready : FirstReady R domain q c) (separate : FirstSeparation R q qs c) :
    FnSummary MopupPop.pc (fun d => d = c) (PopFirstPost R q qs pl c) :=
  ⟨Vsa.Logic.Triple.seq (pop_machine input).run (first_after_pop input ready separate)⟩

end OCaml.Vm.Gc.WorkQueue
