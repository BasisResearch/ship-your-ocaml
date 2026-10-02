import OCaml.Vm.Sim.Ccall1Setup
import OCaml.Vm.Sim.Ccall1Primitives
import OCaml.Vm.Sim.Ccall

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic
open OCaml.Vm.Primitives

/-- Unary instance of the shared call-site and returning-callee contracts. -/
abbrev Ccall1Ready := CcallReady .C_CALL1

abbrev Ccall1Callee (L : OCaml.Layout) (P : Prog) (s : St) :=
  CcallCallee (0x80003060#64) [s.accu] L P s

/-- Unary C_CALL with a successful F1 primitive result. Dispatch, native setup,
the named callee summary and native restoration compose through callSeg. -/
theorem c_call1_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table entry : Nat}
    {value env result : BitVec 64} {index : BitVec 32} {name : String}
    {v : Val} {heap : Heap} {world : World}
    (writeStable : WindowStable L.runtimeOk (ccall1Windows sp domain))
    (readStable : MemoryStable L.runtimeOk)
    (h : Ccall1Ready L P s c pl cp sp high domain table entry value env index name)
    (callee : Ccall1Callee L P s pl cp sp high domain entry env name v result heap world) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := s.pc + 2, accu := v, heap := heap, world := world} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨n, call, prefixSteps, setup⟩ := c_call1_setup writeStable h.toArmInput h.operand h.nonnegative
    h.primitive h.entryName h.aligned h.domainWord h.tableWord h.targetRead h.value h.environment h.space dp
  have pre : Triple (fun x => x = d) (fun x => PCAt (BitVec.ofNat 64 entry) x ∧ x = call) := by
    rintro x rfl
    exact ⟨call, prefixSteps.toSteps, setup.target, rfl⟩
  have composed := callSeg pre (callee.summary call setup).run (c_call1_return_triple readStable)
  obtain ⟨after, run, represented⟩ := composed d rfl
  exact ⟨_, after, run.toN_of_stepsField, represented⟩

/-- Match the actual C_CALL1 bytecode rule to the named successful primitive
result; the resulting arm uses the same generated setup/return segments. -/
theorem c_call1_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table entry : Nat}
    {value env result : BitVec 64} {index : BitVec 32} {name : String}
    {v : Val} {heap : Heap} {world : World}
    (writeStable : WindowStable L.runtimeOk (ccall1Windows sp domain))
    (readStable : MemoryStable L.runtimeOk)
    (h : Ccall1Ready L P s c pl cp sp high domain table entry value env index name)
    (callee : Ccall1Callee L P s pl cp sp high domain entry env name v result heap world)
    (step : stepI P s ⟨.C_CALL1, [index.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {s with pc := s.pc + 2, accu := v, heap := heap, world := world} = s' := by
    simpa [stepI, h.primitive, opt, cCall, prim, primF1, callee.fragment, callee.semantics] using step
  rw [← state]
  exact c_call1_arm writeStable readStable h callee

/-- Instantiate the named obligation from a represented read-only summary
family. The finite caller-register frame and saved words are discharged once. -/
theorem c_call1_callee_of_readOnly {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env result : BitVec 64}
    {name : String} {v : Val} {writes : List Nat}
    (fragment : name ∈ primsF1)
    (model : primF1Impl name [s.accu] s.heap s.world = .ok v s.heap s.world)
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (summary : ∀ c, ImmediateInput L.runtimeOk P s pl cp sp high (0x80003060#64) [s.accu] c →
      FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
        (ReadOnlyPost L.runtimeOk P s pl cp sp high name [s.accu] v result writes c (0x80003060#64))) :
    Ccall1Callee L P s pl cp sp high domain entry env name v result s.heap s.world :=
  ccall_callee_of_readOnly fragment model preserved summary

/-- The landed Sys.argv machine summary supplies the returning-callee obligation.
The runtime/world invariant must supply the global argv binding at call sites. -/
theorem c_call1_sys_argv_callee {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {env result : BitVec 64}
    (stable : MemoryStable L.runtimeOk)
    (value : valWord pl s.world.argv = some result)
    (global : ∀ c, Ccall1SetupPost L P s pl cp sp high domain Layout.sym_caml_sys_argv env c →
      word c Layout.sym_main_argv = result) :
    Ccall1Callee L P s pl cp sp high domain Layout.sym_caml_sys_argv env
      "caml_sys_argv" s.world.argv result s.heap s.world := by
  refine ⟨by decide, rfl, ?_⟩
  intro c setup
  have S := caml_sys_argv_primitive stable setup.input (by rw [global c setup]; exact value)
  rw [global c setup] at S
  exact c_call1_readOnly_summary S (by decide) setup.saved


end OCaml.Vm.Sim
