import OCaml.Vm.Sim.Ccall1Return
import OCaml.Vm.Primitives.CamlSysArgv

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic
open OCaml.Vm.Primitives

/-- Compose a named represented primitive summary with the generated return
suffix. Callers supply the prefix; all primitive bodies remain in a1-prims. -/
theorem c_call1_resume {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high : Nat} {domain frameSp result env entry : BitVec 64}
    {Pre : Config → Prop} (stable : MemoryStable L.runtimeOk)
    (S : FnSummary entry Pre (Ccall1Return L P s pl cp sp high domain frameSp result env)) :
    FnSummary entry Pre (Running L P s) :=
  ⟨Triple.seq S.run (c_call1_return_triple stable)⟩

/-- Consume the landed Sys.argv primitive summary and restore the loop state.
The caller still supplies its generated setup and the world/global link. -/
theorem c_call1_sys_argv {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high : Nat} {domain frameSp env : BitVec 64} {c : Config}
    (stable : MemoryStable L.runtimeOk)
    (h : ImmediateInput L.runtimeOk P s pl cp sp high (0x80003060#64) [s.accu] c)
    (saved : Ccall1Saved {s with pc := s.pc + 2} pl sp domain frameSp env c)
    (argv : valWord pl s.world.argv = some (word c Layout.sym_main_argv))
    (geometry : ArmGeometry P s c pl cp high) (native : NativePlaced c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_argv) (fun x => x = c)
      (Running L P {s with pc := s.pc + 2, accu := s.world.argv}) :=
  c_call1_resume stable (c_call1_readOnly_summary
    (caml_sys_argv_primitive stable h argv) (by decide) saved geometry native)

end OCaml.Vm.Sim
