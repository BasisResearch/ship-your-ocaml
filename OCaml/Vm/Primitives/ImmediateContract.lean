import OCaml.Vm.Primitives.Register
import OCaml.Vm.Primitives.Payload

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- C arguments are passed in consecutive registers starting at a0. -/
def ArgumentsRepr (pl : Place) (args : List Val) (c : Config) : Prop :=
  ∀ i v, args[i]? = some v → ∃ word, valWord pl v = some word ∧ gpr c (10 + i) = some word

theorem ArgumentsRepr.get {pl : Place} {args : List Val} {c : Config}
    (h : ArgumentsRepr pl args c) {i : Nat} {v : Val} {w : BitVec 64}
    (hi : args[i]? = some v) (hv : valWord pl v = some w) :
    gpr c (10 + i) = some w := by
  obtain ⟨w', hw', hr⟩ := h i v hi
  have he : w' = w := Option.some.inj (hw'.symm.trans hv)
  simpa only [he] using hr

/-- Data and platform facts common to read-only primitive calls. -/
structure ImmediateInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (args : List Val) (c : Config) : Prop extends LeafInput ra c where
  data : VmPayload P s c pl cp sp high
  runtime : runtimeOk c
  loop : LoopRegisters c
  arguments : ArgumentsRepr pl args c

structure ImmediatePost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (n : BitVec 63) (writes : List Nat) (before : Config) (ra : BitVec 64)
    (after : Config) : Prop where
  call : RegisterPost writes before ra (tag64 n) after
  data : VmPayload P {s with accu := .int n} after pl cp sp high
  platform : PlatformOk runtimeOk after
  loop : LoopRegisters after
  resultRepr : valWord pl (.int n) = some (tag64 n)
  semantics : primF1Impl name args s.heap s.world = .ok (.int n) s.heap s.world

/-- A finite write-set check protects the interpreter's dedicated registers. -/
def PreservesLoopRegisters (writes : List Nat) : Prop :=
  ∀ r ∈ [Layout.reg_dispatchTable, Layout.reg_opcodeBound, Layout.reg_pending, Layout.reg_domain],
    ∀ n ∈ writes, gprReg n ≠ gprReg r

theorem immediate_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {ra entry : BitVec 64}
    {c : Config} {name : String} {args : List Val} {n : BitVec 63} {writes : List Nat}
    (h : ImmediateInput runtimeOk P s pl cp sp high ra args c)
    (S : FnSummary entry (fun x => x = c) (RegisterPost writes c ra (tag64 n)))
    (frame : PreservesLoopRegisters writes)
    (model : primF1Impl name args s.heap s.world = .ok (.int n) s.heap s.world) :
    FnSummary entry (fun x => x = c)
      (ImmediatePost runtimeOk P s pl cp sp high name args n writes c ra) := by
  apply S.weaken (fun _ h => h)
  intro after post
  refine ⟨post, (h.data.accu_int n).frame post.memory post.output,
    ⟨post.good, post.image, stable _ _ post.memory h.runtime⟩, ?_, rfl, model⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (post.frame (gprReg Layout.reg_dispatchTable) (frame Layout.reg_dispatchTable (by simp)) (by decide)).trans h.loop.dispatchTable
  · exact (post.frame (gprReg Layout.reg_opcodeBound) (frame Layout.reg_opcodeBound (by simp)) (by decide)).trans h.loop.opcodeBound
  · exact (post.frame (gprReg Layout.reg_pending) (frame Layout.reg_pending (by simp)) (by decide)).trans h.loop.pending
  · exact (post.frame (gprReg Layout.reg_domain) (frame Layout.reg_domain (by simp)) (by decide)).trans h.loop.domain

end OCaml.Vm.Primitives
