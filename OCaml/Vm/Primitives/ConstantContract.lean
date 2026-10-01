import OCaml.Vm.Primitives.Payload

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Represented VM data and saved caller registers at a unary C-call boundary.
The arm supplies its setup frame; the callee returns in a0 and preserves the
other GPRs. The arm's restoration segment re-establishes `VmReprAt.atHead`. -/
structure ConstantInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  data : VmPayload P s c pl cp sp high
  runtime : runtimeOk c
  loop : LoopRegisters c
  argument : ∃ w, valWord pl s.accu = some w ∧ gpr c 10 = some w

structure ConstantPost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (n : BitVec 63)
    (before : Config) (ra : BitVec 64) (after : Config) : Prop where
  call : LeafPost before ra (tag64 n) after
  data : VmPayload P {s with accu := .int n} after pl cp sp high
  platform : PlatformOk runtimeOk after
  loop : LoopRegisters after
  resultRepr : valWord pl (.int n) = some (tag64 n)
  semantics : primF1Impl name [s.accu] s.heap s.world = .ok (.int n) s.heap s.world

/-- Lift a generated constant function to the represented primitive boundary.
`stable` is the frame law for the caller's chosen runtime invariant, not a
callee run or a primitive-body assumption. -/
theorem constant_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {ra entry : BitVec 64}
    {c : Config} {name : String} {n : BitVec 63}
    (h : ConstantInput runtimeOk P s pl cp sp high ra c)
    (S : FnSummary entry (fun x => x = c) (LeafPost c ra (tag64 n)))
    (model : primF1Impl name [s.accu] s.heap s.world = .ok (.int n) s.heap s.world) :
    FnSummary entry (fun x => x = c)
      (ConstantPost runtimeOk P s pl cp sp high name n c ra) := by
  apply S.weaken (fun _ h => h)
  intro after post
  refine ⟨post, (h.data.accu_int n).frame post.memory post.output,
    ⟨post.good, post.image, stable _ _ post.memory h.runtime⟩, ?_, rfl, model⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (post.frame (gprReg Layout.reg_dispatchTable) (by decide) (by decide)).trans h.loop.dispatchTable
  · exact (post.frame (gprReg Layout.reg_opcodeBound) (by decide) (by decide)).trans h.loop.opcodeBound
  · exact (post.frame (gprReg Layout.reg_pending) (by decide) (by decide)).trans h.loop.pending
  · exact (post.frame (gprReg Layout.reg_domain) (by decide) (by decide)).trans h.loop.domain

end OCaml.Vm.Primitives
