import OCaml.Vm.Sim.StopReady
import OCaml.Vm.Sim.StopArm
import OCaml.Vm.Sim.DecodeFetch
import OCaml.RefinementF1

/-!
# The STOP row of the F1 arm table

`stop_row`: from any reachable loop head at `STOP`, the machine halts with
`BcSem`'s console and exit code 0. The arm body is a1-arms'
`stop_halt_step_arm`; its native preconditions come from `Running.native`
(`stop_ready`), its exit from caml_do_exit's run (`stop_exit_continuation`),
and the accumulator is an ordinary result word because F1 never stops with a
raw word (`GoodF1.stopAccu`) and the placement is word aligned
(`StackGeometry.words`). The exit facts at the STOP state remain the named
premise `StopExitReady`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **The STOP row.** -/
theorem stop_row {L : OCaml.Layout} {P : Prog} (good : OCaml.GoodF1 P)
    (exit : ∀ s c D sp, Reach P s → OCaml.LoopAt L P s c → Invocation D c → NativeValid D →
      StopExitReady c D.nativeSp (BitVec.ofNat 64 sp)) :
    OCaml.OpArm P (OCaml.LoopAt L P) .STOP := by
  intro s c i reach h hd op _
  obtain ⟨o, args⟩ := i
  cases op
  cases args with
  | cons a rest => exact trivial
  | nil =>
    apply OCaml.ArmOutcome.of_cases
    · intro s' step
      simp [stepI] at step
    · intro e w step
      obtain ⟨pl, cp, sp, high, ai⟩ := ArmInput.of_loop h (decode_fetch hd).1
      obtain ⟨D, inv, valid⟩ := ai.native
      obtain ⟨value, accuReg, encoded⟩ := ai.accu
      have notRaw : ∀ r, s.accu ≠ .raw r := by
        intro r hr
        have := good.stopAccu s _ reach hd
        simp [OCaml.stopOrdinary, hr] at this
      have words := ai.geometry.words
      have ordinary := valWord_ordinary words.code (fun l a ha => by have := words.heap l a ha; omega)
        (by have := words.atoms; omega) notRaw encoded
      have invocation := (stop_ready (vmSp := BitVec.ofNat 64 sp) inv valid ai.geometry.domainLow
        ai.geometry.domainArena ai.geometry.domainAligned).1
      have cont := stop_exit_continuation inv valid ai.geometry.domainLow ai.geometry.domainArena
        ai.geometry.domainAligned ordinary (exit s c D sp reach h inv valid)
      rw [ai.world.1] at cont
      exact stop_halt_step_arm ai invocation encoded cont step

end OCaml.Vm.Sim
