import OCaml.Vm.Sim.CcallRows
import OCaml.Vm.Sim.Ccall1Exit
import OCaml.Vm.Sim.F1Frame
import OCaml.Vm.Sim.G1Capacity
import OCaml.Vm.Primitives.ExitPath.Primitive

/-!
# `ArmSim.halt` at a `C_CALL1` site: `caml_sys_exit`

The only exiting F1 primitive is `caml_sys_exit` (one argument). At a
reachable C_CALL1 loop head of the pinned layout, a1-arms' exit arm runs
dispatch and argument setup; a1-prims' `caml_sys_exit_halts` runs the callee
through caml_do_exit to the HTIF halt. Its exit runtime comes from the
invariant: the pinned runtime's quiet-exit globals, HTIF idle, and the native
invocation's headroom. Only presence of the registers caml_do_exit reads at
the callee entry is named (supplied by `LoopRegisters.gprs`, a1-arms).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ExitPath

/-- **The C_CALL1 exit row** for the pinned layout. -/
theorem ccall1Exit_f1 {P : Prog} (fits : OCaml.Fits Gc.g1Budget P)
    (present : ∀ s c' pl cp sp high domain entry env, Reach P s →
      CcallSetupPost (0x80003060#64) [s.accu] Gc.f1Layout P s pl cp sp high domain entry env c' →
      ∀ n ∈ exitReads, (gprGet c'.σ n).isSome) :
    CcallExit Gc.f1Layout P .C_CALL1 0 := by
  refine ⟨fun s c w name e world reach h code fetch nonnegative hp member _ hr => ?_⟩
  obtain ⟨hname, -⟩ := primF1Impl_exit hr
  subst hname
  have space := stack_fits fits g1_capacity reach (k := 2)
  obtain ⟨pl, cp, sp, high, entry, value, env, ready⟩ :=
    CcallReady.of_loop h code fetch nonnegative hp space
  have hs := ready.stack.1
  have same : high = Gc.f1High := ready.stackHigh.symm.trans (f1_runtimeFrame.stackHigh c ready.runtime)
  subst same
  have stable : WindowStable Gc.f1Layout.runtimeOk (ccall1Windows sp (domainAt c)) :=
    f1_runtimeFrame.windows _ fun x hx => by
      simp only [ccall1Windows, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
      · rw [domainAt, f1_runtimeFrame.domainWord c ready.runtime]
        exact Or.inr ⟨Layout.off_extern_sp, by decide, rfl⟩
  have args : s.accu :: s.stack.take 0 = [s.accu] := by simp
  rw [args] at hr
  obtain ⟨n, hn⟩ : ∃ n, s.accu = .int n := by
    cases ha : s.accu <;> simp [ha, primF1Impl, intArg?] at hr ⊢
  rw [hn] at hr
  apply c_call1_exit_arm stable ready
  refine ⟨member, by rw [hn]; exact hr, fun c' setup => ?_⟩
  obtain ⟨D, inv, valid⟩ := setup.native
  have target : PrimitiveEntries.lookup "caml_sys_exit" = some Layout.sym_caml_sys_exit := by decide
  have entryEq : entry = Layout.sym_caml_sys_exit := by
    have := ready.entryName; rw [target] at this; exact (Option.some.inj this).symm
  subst entryEq
  have n1 := valid.headroom
  have n2 := valid.high
  have n3 := valid.aligned
  simp only [Vsa.Sim.DlHeap.heapEnd, nativeHeadroom, Layout.interpFrameBytes, Layout.camlMainFrameBytes,
    Layout.sym_stack_top] at n1 n2
  have hsp : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := Nat.mod_eq_of_lt (by omega)
  have runtime : ExitRuntime (BitVec.ofNat 64 D.nativeSp) c' := by
    refine ⟨⟨setup.input.good, setup.input.tick, setup.input.loop.htifIdle,
      present s c' pl cp sp _ _ _ env reach setup⟩, inv.stack, ?_, Gc.f1_exitGlobals setup.input.runtime⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hsp]
    all_goals try simp only [exitDepth, Layout.sym_tohost, Image.textBase, Image.textSize,
      Image.rodataBase, Image.rodataSize, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, verbGc, cleanupOnExit, atexitList, atexitMutex, stdioExitHandler,
      BitVec.toNat_ofNat, Layout.sym_caml_verb_gc, Layout.sym_caml_cleanup_on_exit, Layout.sym_atexit,
      Layout.sym_atexit_recursive_mutex, Layout.sym_stdio_exit_handler]
    all_goals omega
  rw [hn] at setup
  exact caml_sys_exit_halts setup.input runtime setup.target hr

/-- Every register `caml_do_exit` reads is present at the C_CALL1 callee
entry: `ra` and `a0` from the call setup, `sp` from the native invocation,
`s0`–`s10` from `CcallSetupPost.calleeSaved`. -/
theorem ccall1_present {P : Prog} : ∀ s c' pl cp sp high domain entry env, Reach P s →
    CcallSetupPost (0x80003060#64) [s.accu] Gc.f1Layout P s pl cp sp high domain entry env c' →
    ∀ n ∈ exitReads, (gprGet c'.σ n).isSome := by
  intro s c' pl cp sp high domain entry env _ setup n hn
  have saved := setup.calleeSaved
  obtain ⟨D, inv, -⟩ := setup.native
  obtain ⟨w, -, hw⟩ := setup.input.arguments 0 s.accu rfl
  simp only [exitReads, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isSome_of_pin setup.input.raReg
  · exact isSome_of_pin inv.stack
  · exact saved 8 (by simp)
  · exact saved 9 (by simp)
  · exact isSome_of_pin hw
  all_goals exact saved _ (by simp)

/-- **The C_CALL1 exit row**, with no premise beyond the budget. -/
theorem ccall1Exit_pinned {P : Prog} (fits : OCaml.Fits Gc.g1Budget P) :
    CcallExit Gc.f1Layout P .C_CALL1 0 :=
  ccall1Exit_f1 fits ccall1_present

end OCaml.Vm.Sim
