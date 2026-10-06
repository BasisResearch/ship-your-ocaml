import OCaml.Vm.Sim.CcallSetup
import OCaml.Logic.Symbolic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic
open OCaml.Vm.Primitives

/-- Static represented inputs for the fixed-arity primitive-call arm. The eventual
loop invariant supplies the geometry, separation and nonnegative operand. -/
structure CcallReady (opcode : Opcode) (L : OCaml.Layout) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp high domain table entry : Nat)
    (accuWord envWord : BitVec 64) (index : BitVec 32) (name : String) : Prop
    extends ArmInput L P s opcode c pl cp sp high where
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
  /-- the stack, the pushed environment and return address fit the VM stack
  (with `StackGeometry.statics`: `sp - 16` lies above `.bss`) -/
  stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes

/-- Named obligation for a returning F1 primitive. a1-prims supplies the
represented machine summary; its frame must retain the caller-owned saved
words/registers. This obligation contains only the callee, not arm execution.
Exceptions and exits require different continuations and remain separate. -/
structure CcallCallee (ra : BitVec 64) (args : List Val) (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high domain entry : Nat) (env : BitVec 64) (name : String)
    (v : Val) (result : BitVec 64) (heap : Heap) (world : World) : Prop where
  fragment : name ∈ primsF1
  semantics : primF1Impl name args s.heap s.world = .ok v heap world
  summary : ∀ c, CcallSetupPost ra args L P s pl cp sp high domain entry env c →
    FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
      (CcallReturn ra L P {s with pc := s.pc + 2, accu := v, heap := heap, world := world}
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16)) result env)

/-- Instantiate the named obligation from a represented read-only summary
family. The finite caller-register frame and saved words are discharged once. -/
theorem ccall_callee_of_readOnly {ra : BitVec 64} {args : List Val} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env result : BitVec 64}
    {name : String} {v : Val} {writes : List Nat}
    (fragment : name ∈ primsF1)
    (model : primF1Impl name args s.heap s.world = .ok v s.heap s.world)
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (summary : ∀ c, ImmediateInput L.runtimeOk P s pl cp sp high ra args c →
      FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
        (ReadOnlyPost L.runtimeOk P s pl cp sp high name args v result writes c ra)) :
    CcallCallee ra args L P s pl cp sp high domain entry env name v result s.heap s.world :=
  ⟨fragment, model, fun c setup =>
    ccall_readOnly_summary (summary c setup.input) preserved setup.saved setup.geometry
      setup.native⟩

end OCaml.Vm.Sim
