import OCaml.Vm.Sim.Ccall1Setup
import OCaml.Vm.Sim.Ccall1Primitives
import OCaml.Logic.Symbolic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic
open OCaml.Vm.Primitives

/-- Static represented inputs for the unary primitive-call arm. The eventual
loop invariant supplies the geometry, separation and nonnegative operand. -/
structure Ccall1Ready (L : OCaml.Layout) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp high domain table entry : Nat)
    (accuWord envWord : BitVec 64) (index : BitVec 32) (name : String) : Prop
    extends ArmInput L P s .C_CALL1 c pl cp sp high where
  operand : OperandAt P pl (s.pc + 1) index
  nonnegative : 0 ≤ index.toInt
  primitive : P.prims[index.toInt.toNat]? = some name
  entryName : PrimitiveEntries.lookup name = some entry
  aligned : (BitVec.ofNat 64 entry).toNat % 4 = 0
  domainWord : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain
  tableWord : word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) = BitVec.ofNat 64 table
  targetRead : RamReadAt (table + 8 * index.toInt.toNat) 8
  value : valWord pl s.accu = some accuWord
  environment : valWord pl s.env = some envWord
  space : Ccall1WriteOk P s c pl cp sp domain (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2))) envWord

/-- Named obligation for a returning F1 primitive. a1-prims supplies the
represented machine summary; its frame must retain the caller-owned saved
words/registers. This obligation contains only the callee, not arm execution.
Exceptions and exits require different continuations and remain separate. -/
structure Ccall1Callee (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high domain entry : Nat) (env : BitVec 64) (name : String)
    (v : Val) (result : BitVec 64) (heap : Heap) (world : World) : Prop where
  fragment : name ∈ primsF1
  semantics : primF1Impl name [s.accu] s.heap s.world = .ok v heap world
  summary : ∀ c, Ccall1SetupPost L P s pl cp sp high domain entry env c →
    FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
      (Ccall1Return L P {s with pc := s.pc + 2, accu := v, heap := heap, world := world}
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16)) result env)

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
  ⟨fragment, model, fun c setup =>
    c_call1_readOnly_summary (summary c setup.input) preserved setup.saved⟩

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
