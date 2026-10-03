import OCaml.Vm.Gc.MopupResume
import OCaml.Vm.Gc.Advance

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The branch reads the real post-call header, including any effects of the
native save bank and root store. Geometry later identifies a preserved size. -/
def againAfterCall (R : Nat → BitVec 64) (c : Config) : Bool :=
  guardB .BLTU (R 9 + 1#64)
    (bytesT (writeLog c.σ.mem (ForwardedCall.effect (linked R) c)) (R 19 - 8#64).toNat 8 >>> (10 : Nat))

theorem ResumedPost.advance_input {R before after} (post : ResumedPost R before after)
    (header : ReadWindow (R 19 - 8#64) 8) :
    FieldCopy.AdvanceInput (R 8) (R 18) (R 19) (R 9) after := by
  refine ⟨post.body.good, post.body.minstret, post.body.tick, post.code, ?_, header⟩
  apply gholds_select post.body.registers
  intro n v member
  simp only [FieldCopy.regs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h <;> cases h <;> rfl

/-- A returned forwarded pointer has been written and the scan has advanced.
Only the actual scratch/link registers and scan index/pointer may change;
restored callee-saved registers remain available to the enclosing loop. -/
structure AdvancedPost (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem (ForwardedCall.effect (linked R) before)
  destination : word after (R 11).toNat = word before (R 10).toNat
  pc : PCAt (if againAfterCall R before then FieldCopy.pc else FieldCopy.exitPc) after
  registers : GHolds after.σ (FieldCopy.regs (R 8 + 8#64) (R 18) (R 19) (R 9 + 1#64))
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,8,9,12,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete forwarded-field call, native return, resume jump and concrete
header-controlled advance. The preceding field classifier supplies its call
arguments; fresh-object oldification remains a different callee route. -/
theorem forwarded_advance {R domain c} (input : ForwardedCall.Input R domain c)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) (header : ReadWindow (R 19 - 8#64) 8) :
    FnSummary call.pc (fun d => d = c) (AdvancedPost R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (forwarded_resume input code).run
  intro middle returned
  obtain ⟨after, run, advanced⟩ := (FieldCopy.advance_machine (returned.advance_input header)).run
    middle ⟨returned.body.pc, rfl⟩
  refine ⟨after, run, ⟨advanced.machine.good, advanced.machine.minstret, advanced.machine.tick,
    advanced.code, advanced.memory.trans returned.body.memory, ?_, ?_, advanced.registers,
    advanced.machine.output.trans returned.body.output, ?_⟩⟩
  · simpa [word, linked, advanced.memory] using returned.body.root
  · have same : FieldCopy.advanceAgain (R 19) (R 9) middle = againAfterCall R c := by
      unfold FieldCopy.advanceAgain againAfterCall word
      rw [returned.body.memory]
    simpa only [same] using advanced.pc
  · intro r noise untouched
    apply (advanced.machine.frame r noise ?_).trans
      (abi_frame returned.body input.entry.registers r noise ?_)
    · intro n hn
      have member := FieldCopy.advance_written _ n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact untouched _ (by decide)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

end OCaml.Vm.Gc.MopupCall
