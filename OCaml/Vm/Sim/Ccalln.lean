import OCaml.Vm.Sim.CcallnSetup
import OCaml.Logic.Symbolic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic
open OCaml.Vm.Primitives

/-- Static C_CALLN call-site facts. The loop invariant must supply geometry,
separation, native stack and operand facts; no primitive run is assumed. -/
structure CcallnReady (L : OCaml.Layout) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp high domain table nativeSp entry : Nat)
    (accuWord envWord : BitVec 64) (index nargs : BitVec 32) (name : String) : Prop
    extends ArmInput L P s .C_CALLN c pl cp sp high where
  countOperand : OperandAt P pl (s.pc + 1) nargs
  positive : 0 < nargs.toInt
  bound : nargs.toInt.toNat - 1 ≤ s.stack.length
  operand : OperandAt P pl (s.pc + 2) index
  nonnegative : 0 ≤ index.toInt
  primitive : P.prims[index.toInt.toNat]? = some name
  entryName : PrimitiveEntries.lookup name = some entry
  aligned : (BitVec.ofNat 64 entry).toNat % 4 = 0
  domainWord : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain
  tableWord : word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) = BitVec.ofNat 64 table
  targetRead : RamReadAt (table + 8 * index.toInt.toNat) 8
  value : valWord pl s.accu = some accuWord
  environment : valWord pl s.env = some envWord
  nativeReg : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  space : CcallnWriteOk P s c pl cp sp domain nativeSp
    (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) envWord accuWord

/-- Named returning primitive obligation for the stack-array ABI. a1-prims
must supply a summary for that ABI and preserve the saved native/VM frame.
This contract covers only the callee; exceptions and exits are separate. -/
structure CcallnCallee (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high count domain nativeSp entry : Nat) (env : BitVec 64) (name : String)
    (v : Val) (result : BitVec 64) (heap : Heap) (world : World) : Prop where
  fragment : name ∈ primsF1
  semantics : primF1Impl name (s.accu :: s.stack.take (count - 1)) s.heap s.world = .ok v heap world
  summary : ∀ c, CcallnSetupPost L P s pl cp sp high count domain nativeSp entry env c →
    FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
      (CcallnReturn L P {s with pc := s.pc + 3, accu := v, heap := heap, world := world}
        pl cp sp high count (BitVec.ofNat 64 nativeSp)
        (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 24)) result env)

/-- Compose dispatch, the stack-array setup, a named returning primitive
summary and the generated restoration through the shared callSeg rule. -/
theorem c_calln_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table nativeSp entry : Nat}
    {value env result : BitVec 64} {index nargs : BitVec 32} {name : String}
    {v : Val} {heap : Heap} {world : World}
    (writeStable : WindowStable L.runtimeOk (ccallnWindows sp domain nativeSp))
    (readStable : MemoryStable L.runtimeOk)
    (h : CcallnReady L P s c pl cp sp high domain table nativeSp entry value env index nargs name)
    (callee : CcallnCallee L P s pl cp sp high nargs.toInt.toNat domain nativeSp entry env name v result heap world) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := s.pc + 3, accu := v, heap := heap, world := world, stack := s.stack.drop (nargs.toInt.toNat - 1)} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨n, call, prefixSteps, setup⟩ := c_calln_setup writeStable h.toArmInput
    h.countOperand h.positive h.bound h.operand h.nonnegative h.primitive h.entryName h.aligned
    h.domainWord h.tableWord h.targetRead h.value h.environment h.nativeReg h.space dp
  have pre : Triple (fun x => x = d) (fun x => PCAt (BitVec.ofNat 64 entry) x ∧ x = call) := by
    rintro x rfl
    exact ⟨call, prefixSteps.toSteps, setup.target, rfl⟩
  have composed := callSeg pre (callee.summary call setup).run
    (c_calln_return_triple readStable setup.input.positive h.bound)
  obtain ⟨after, run, represented⟩ := composed d rfl
  exact ⟨_, after, run.toN_of_stepsField, represented⟩

/-- Match the checked returning C_CALLN bytecode rule to the machine arm. -/
theorem c_calln_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table nativeSp entry : Nat}
    {value env result : BitVec 64} {index nargs : BitVec 32} {name : String}
    {v : Val} {heap : Heap} {world : World}
    (writeStable : WindowStable L.runtimeOk (ccallnWindows sp domain nativeSp))
    (readStable : MemoryStable L.runtimeOk)
    (h : CcallnReady L P s c pl cp sp high domain table nativeSp entry value env index nargs name)
    (callee : CcallnCallee L P s pl cp sp high nargs.toInt.toNat domain nativeSp entry env name v result heap world)
    (step : stepI P s ⟨.C_CALLN, [nargs.toInt, index.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {s with pc := s.pc + 3, accu := v, heap := heap, world := world, stack := s.stack.drop (nargs.toInt.toNat - 1)} = s' := by
    simpa [stepI, h.primitive, opt, cCall, prim, primF1, callee.fragment, callee.semantics,
      Int.not_le.mpr h.positive, Nat.not_lt.mpr h.bound,
      List.length_take, Nat.min_eq_left h.bound] using step
  rw [← state]
  exact c_calln_arm writeStable readStable h callee

/-- Adapt a represented stack-array primitive summary with a checked ABI
write-set to the caller's return frame. The primitive body stays in a1-prims. -/
theorem c_calln_callee_of_readOnly {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high count domain nativeSp entry : Nat}
    {env result : BitVec 64} {name : String} {v : Val} {writes : List Nat}
    (fragment : name ∈ primsF1)
    (model : primF1Impl name (s.accu :: s.stack.take (count - 1)) s.heap s.world = .ok v s.heap s.world)
    (preserved : ∀ r ∈ callnSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (summary : ∀ c, CcallnInput L.runtimeOk P s pl cp sp high count c →
      FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
        (ReadOnlyPost L.runtimeOk P s pl cp sp high name (s.accu :: s.stack.take (count - 1))
          v result writes c (0x80002e64#64))) :
    CcallnCallee L P s pl cp sp high count domain nativeSp entry env name v result s.heap s.world :=
  ⟨fragment, model, fun c setup =>
    c_calln_readOnly_summary (summary c setup.input) preserved setup.saved⟩

end OCaml.Vm.Sim
