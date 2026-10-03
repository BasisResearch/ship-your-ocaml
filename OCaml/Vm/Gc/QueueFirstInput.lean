import OCaml.Vm.Gc.QueueObserved
import OCaml.Vm.Gc.PopScan
import OCaml.Vm.Gc.FirstField
import OCaml.Vm.Gc.ForwardedObservations

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Native values unchanged by the queue pop; three loaded values are
supplied separately from the concrete queue and copied first field. -/
def firstNative (R : Nat → BitVec 64) : GRegs :=
  [(2,R 2),(8,R 8),(9,R 9),(1,R 1),(20,R 20),(21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

def firstRegs (R : Nat → BitVec 64) (q : PendingCopy) (c : Config) (n : Nat) : BitVec 64 :=
  if n = 10 then word c q.target.toNat else if n = 18 then q.source
  else if n = 19 then q.target else R n

/-- Static native and heap facts needed when the popped first child is an
already-forwarded young pointer. PopInput separately supplies the queue,
platform and pop windows. No post-pop machine state is assumed. -/
structure FirstReady (R : Nat → BitVec 64) (domain : BitVec 64) (q : PendingCopy) (c : Config) : Prop where
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  native : GHolds c.σ (firstNative R)
  runtime : R 22 = BitVec.ofNat 64 Layout.sym_Caml_state
  windows : ∀ cell ∈ OldifyEntry.saves,
    WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  even : (word c q.target.toNat).toNat % 2 = 0
  conditions : ForwardedCall.Conditions (FirstField.args (firstRegs R q c)) domain c
  observations : ForwardedCall.ObservationsOutside (FirstField.args (firstRegs R q c)) domain popFootprint

theorem PopPost.first_native {R q qs pl before after} (post : PopPost q qs pl before after)
    (holds : GHolds before.σ (firstNative R)) : GHolds after.σ (firstNative R) := by
  apply gholds_of_frame (post.effects.frame_subset (MopupPop.actual_written _)) (firstNative R)
    (by change KeysOK [2,8,9,1,20,21,22,23,24,25]; decide) ?_ ?_ holds
  · change ∀ n ∈ [2,8,9,1,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · change ∀ n ∈ [2,8,9,1,20,21,22,23,24,25], ∀ m ∈ [18,19,10,15], (gprReg m == gprReg n) = false
    decide

theorem PopPost.first_input {R domain q qs pl before after}
    (input : PopInput q qs pl before) (ready : FirstReady R domain q before)
    (post : PopPost q qs pl before after) : FirstField.Input (firstRegs R q before) domain after := by
  have saved := post.first_native ready.native
  have loaded := post.loaded_regs input.queue
  have all : GHolds after.σ ([(18,q.source),(19,q.target),(10,word before q.target.toNat)] ++ firstNative R) := by
    exact ⟨gholds_lookup _ loaded rfl, gholds_lookup _ loaded rfl, gholds_lookup _ loaded rfl, saved⟩
  refine ⟨post.effects.good, post.effects.minstret, post.effects.tick, post.code input,
    post.oldifyCode input.queue ready.code, ?_, ?_, ready.windows, ready.even,
    ready.conditions.frame ready.observations post.memory_frame⟩
  · apply gholds_select all
    intro n v member
    simp only [FirstField.carried, ForwardedField.carried, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl
  · have pin : gprGet after.σ 22 = some (R 22) := gholds_lookup _ saved rfl
    simpa only [ready.runtime] using pin

/-- The popped child parity is the actual load observation, so an even word
reaches the first-field nursery classifier rather than suffix setup. -/
theorem PopPost.first_pc {q qs pl before after} (post : PopPost q qs pl before after)
    (even : (word before q.target.toNat).toNat % 2 = 0) : PCAt FirstYoung.pc after := by
  have immediate : firstImmediate q before = false := by
    unfold firstImmediate
    rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
    simp [guardB, BitVec.getLsbD, even]
  have machine := post.machine
  rw [immediate] at machine
  exact machine.pointer_pc

end OCaml.Vm.Gc.WorkQueue
