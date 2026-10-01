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

/-- Data, platform and ABI facts common to primitive calls. -/
structure ImmediateInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (args : List Val) (c : Config) : Prop extends LeafInput ra c where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  runtime : runtimeOk c
  loop : LoopRegisters c
  arguments : ArgumentsRepr pl args c

structure PrimitivePost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (v : Val) (w : BitVec 64) (heapAfter : Heap) (worldAfter : World)
    (writes : List Nat) (expectedMem : Std.ExtHashMap Nat (BitVec 8)) (before : Config) (ra : BitVec 64)
    (after : Config) : Prop where
  call : EffectPost writes expectedMem before ra w after
  data : VmPayload P {s with accu := v, heap := heapAfter, world := worldAfter} after pl cp sp high
  primitives : PrimitiveBindings P after
  platform : PlatformOk runtimeOk after
  loop : LoopRegisters after
  resultRepr : valWord pl (v) = some w
  semantics : primF1Impl name args s.heap s.world = .ok v heapAfter worldAfter

/-- A read-only primitive leaves the abstract heap/world and concrete memory unchanged. -/
abbrev ReadOnlyPost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (v : Val) (w : BitVec 64) (writes : List Nat) (before : Config) (ra : BitVec 64) :=
  PrimitivePost runtimeOk P s pl cp sp high name args v w s.heap s.world writes before.σ.mem before ra

/-- The immediate-result specialization preserves the original primitive API. -/
abbrev ImmediatePost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (n : BitVec 63) (writes : List Nat) (before : Config) (ra : BitVec 64) :=
  ReadOnlyPost runtimeOk P s pl cp sp high name args (.int n) (tag64 n) writes before ra

theorem readOnly_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {ra entry : BitVec 64}
    {c : Config} {name : String} {args : List Val} {v : Val} {w : BitVec 64} {writes : List Nat}
    (h : ImmediateInput runtimeOk P s pl cp sp high ra args c)
    (S : FnSummary entry (fun x => x = c) (RegisterPost writes c ra w))
    (frame : PreservesLoopRegisters writes)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (repr : valWord pl v = some w)
    (model : primF1Impl name args s.heap s.world = .ok (v) s.heap s.world) :
    FnSummary entry (fun x => x = c)
      (ReadOnlyPost runtimeOk P s pl cp sp high name args v w writes c ra) := by
  apply S.weaken (fun _ h => h)
  intro after post
  refine ⟨post, (h.data.accu_of_root v root).frame post.memory post.output, h.primitives.frame post.memory,
    ⟨post.good, post.image, stable _ _ post.memory h.runtime⟩, ?_, repr, model⟩
  exact post.loop frame h.loop


theorem immediate_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat} {ra entry : BitVec 64}
    {c : Config} {name : String} {args : List Val} {n : BitVec 63} {writes : List Nat}
    (h : ImmediateInput runtimeOk P s pl cp sp high ra args c)
    (S : FnSummary entry (fun x => x = c) (RegisterPost writes c ra (tag64 n)))
    (frame : PreservesLoopRegisters writes)
    (model : primF1Impl name args s.heap s.world = .ok (.int n) s.heap s.world) :
    FnSummary entry (fun x => x = c)
      (ImmediatePost runtimeOk P s pl cp sp high name args n writes c ra) := by
  exact readOnly_contract stable h S frame (fun _ hl => by cases hl) rfl model

end OCaml.Vm.Primitives
