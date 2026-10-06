import OCaml.Vm.Sim.StopReady
import OCaml.Vm.Sim.StopArm
import OCaml.Vm.Sim.DecodeFetch
import OCaml.RefinementF1
import OCaml.Vm.Gc.F1Runtime

/-!
# The STOP row of the F1 arm table

`stop_row`: from any reachable loop head at `STOP`, the machine halts with
`BcSem`'s console and exit code 0. The arm body is a1-arms'
`stop_halt_step_arm`; its native preconditions come from `Running.native`
(`stop_ready`), its exit from caml_do_exit's run (`stop_exit_continuation`),
and the accumulator is an ordinary result word because F1 never stops with a
raw word (`GoodF1.stopAccu`) and the placement is word aligned
(`StackGeometry.words`). The exit facts at the STOP state remain the named
runtime and register facts at the STOP state: the quiet-exit globals and HTIF idleness.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- STOP's exit facts from the loop invariant: the address facts follow from
the snapshot's placement; the exit globals and HTIF idleness are the runtime
and register facts at the STOP state. -/
theorem stopExitReady_of {c : Config} {D : InvocationData} {vmSp : BitVec 64}
    (valid : NativeValid D) (dLow : Layout.sym_bss_end ≤ (word c Layout.sym_Caml_state).toNat)
    (globals : ExitPath.ExitGlobals c)
    (htifIdle : c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some (0#4)) :
    StopExitReady c D.nativeSp vmSp := by
  have n1 := valid.low
  have n2 := valid.high
  have n3 := valid.aligned
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.interpFrameBytes, Layout.camlMainFrameBytes,
    Layout.sym_stack_top] at n1 n2
  simp only [Layout.sym_bss_end] at dLow
  have hsp : (BitVec.ofNat 64 (D.nativeSp + Layout.interpFrameBytes + Layout.camlMainFrameBytes)).toNat =
      D.nativeSp + 640 := by
    simp only [Layout.interpFrameBytes, Layout.camlMainFrameBytes, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨globals, ?_, ?_, htifIdle⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;>
      simp only [Vsa.Sim.OutLRange, stopLog, ExitPath.verbGc, ExitPath.cleanupOnExit, ExitPath.atexitList,
        ExitPath.stdioExitHandler, BitVec.toNat_ofNat, Layout.sym_caml_verb_gc, Layout.sym_caml_cleanup_on_exit,
        Layout.sym_atexit, Layout.sym_stdio_exit_handler, Layout.sym_caml_callback_depth, Layout.off_extern_sp,
        Layout.off_external_raise, and_true] <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hsp]
    all_goals try simp only [ExitPath.doExitDepth, Layout.sym_tohost, Image.textBase, Image.textSize,
      Image.rodataBase, Image.rodataSize, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, ExitPath.verbGc, ExitPath.cleanupOnExit, ExitPath.atexitList,
      ExitPath.atexitMutex, ExitPath.stdioExitHandler, BitVec.toNat_ofNat, Layout.sym_caml_verb_gc,
      Layout.sym_caml_cleanup_on_exit, Layout.sym_atexit, Layout.sym_atexit_recursive_mutex,
      Layout.sym_stdio_exit_handler]
    all_goals omega

/-- **The STOP row.** -/
theorem stop_row {L : OCaml.Layout} {P : Prog} (good : OCaml.GoodF1 P)
    (globals : ∀ s c, Reach P s → OCaml.LoopAt L P s c → ExitPath.ExitGlobals c)
    (htifIdle : ∀ s c, Reach P s → OCaml.LoopAt L P s c →
      c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some (0#4)) :
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
      have cont := stop_exit_continuation (vmSp := BitVec.ofNat 64 sp) inv valid ai.geometry.domainLow ai.geometry.domainArena
        ai.geometry.domainAligned ordinary
        (stopExitReady_of valid ai.geometry.domainLow (globals s c reach h) (htifIdle s c reach h))
      rw [ai.world.1] at cont
      exact stop_halt_step_arm ai invocation encoded cont step

end OCaml.Vm.Sim

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine

/-- **The STOP row for the pinned F1 layout**, unconditional on F1 programs:
the quiet-exit globals come from the runtime invariant (`Gc.f1_exitGlobals`)
and HTIF idleness from the loop registers. -/
theorem stop_row_f1 {P : Prog} (good : OCaml.GoodF1 P) :
    OCaml.OpArm P (OCaml.LoopAt Gc.f1Layout P) .STOP :=
  stop_row good (fun _ _ _ h => Gc.f1_exitGlobals h.running.platform.runtime)
    (fun _ _ _ h => h.running.loop.htifIdle)

end OCaml.Vm.Sim
