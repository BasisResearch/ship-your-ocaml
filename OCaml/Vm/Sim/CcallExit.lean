import OCaml.Vm.Sim.Ccall
import OCaml.Vm.Sim.Ccalln

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A terminal primitive summary starts at its represented call site and
matches the primitive's actual exit outcome. a1-prims supplies this callee
execution; the C_CALL adapter supplies dispatch and argument setup. -/
structure PrimitiveExitSummary (pre : Config → Prop) (name : String) (args : List Val)
    (heap : Heap) (world : World) (code : Nat) (resultWorld : World) : Prop where
  fragment : name ∈ primsF1
  semantics : primF1Impl name args heap world = .exit code resultWorld
  summary : ∀ c, pre c → Halts c (bytesToString resultWorld.console) code

abbrev CcallExitCallee (ra : BitVec 64) (args : List Val) (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high domain entry : Nat) (env : BitVec 64) (name : String)
    (code : Nat) (resultWorld : World) :=
  PrimitiveExitSummary (CcallSetupPost ra args L P s pl cp sp high domain entry env)
    name args s.heap s.world code resultWorld

abbrev CcallnExitCallee (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high count domain nativeSp entry : Nat) (env : BitVec 64) (name : String)
    (code : Nat) (resultWorld : World) :=
  PrimitiveExitSummary (CcallnSetupPost L P s pl cp sp high count domain nativeSp entry env)
    name (s.accu :: s.stack.take (count - 1)) s.heap s.world code resultWorld

/-- Dispatch preserves a terminal callee continuation through the machine run law. -/
theorem dispatch_halts {c : Config} {op : Opcode} {a : BitVec 64} {output : String} {code : Nat}
    (h : DispatchInput op a c)
    (body : ∀ d, DispatchPost c op a d → Halts d output code) : Halts c output code := by
  obtain ⟨count, after, _, run, post⟩ := dispatch_run h
  exact Halts.of_steps run.toSteps (body after post)

end OCaml.Vm.Sim
