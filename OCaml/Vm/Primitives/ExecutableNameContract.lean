import OCaml.Vm.Primitives.ExecutableNameMachine
import OCaml.Vm.Primitives.StringCopyObservations
import OCaml.Vm.Primitives.ObservationContract

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim StringCopy

/-- The caller supplies nursery room, source bytes, a fresh placement, and
separation from the live VM payload. These are G1 allocation obligations. -/
structure ExecutableNameInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra nativeSp : BitVec 64)
    (arg : Val) (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat) (a : Nat) (g : Nat → BitVec 8)
    (domain young limit : BitVec 64) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high ra [arg] c where
  copy : CopyInput live Dt DA ra nativeSp a s.world.exeName.length g domain young limit c
  source : word c Layout.sym_caml_exe_name = BitVec.ofNat 64 a
  sourceBytes : ∀ i x, s.world.exeName[i]? = some x → g (a + i) = BitVec.ofNat 8 x.toNat
  placed : pl.φ (s.heap.alloc (.bytes s.world.exeName)).2 =
    some (resultWord young s.world.exeName.length).toNat
  separate : AllocationOutside P s pl (resultWord young s.world.exeName.length).toNat (.bytes s.world.exeName)
  payloadOutside : PayloadOutside (copyFootprint ra nativeSp a s.world.exeName.length domain young) P s c pl cp sp
  bindingsOutside : BindingsOutside (copyFootprint ra nativeSp a s.world.exeName.length domain young) P c

/-- The represented return retains the machine copy effects needed to
restore the interpreter caller's saved native frame. -/
structure ExecutableNamePost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra nativeSp : BitVec 64)
    (arg : Val) (live : Nat → Prop) (a : Nat) (g : Nat → BitVec 8)
    (domain young : BitVec 64) (before after : Config) : Prop
    extends LibraryPrimitivePost runtimeOk P s pl cp sp high "caml_sys_executable_name" [arg]
      (.ptr (s.heap.alloc (.bytes s.world.exeName)).2 0) (resultWord young s.world.exeName.length)
      (s.heap.alloc (.bytes s.world.exeName)).1 s.world ra after,
      CopyPost live ra nativeSp a s.world.exeName.length g domain young before after

theorem executable_name_contract {runtimeOk P s pl cp sp high ra nativeSp arg live Dt DA a g domain young limit c}
    (h : ExecutableNameInput runtimeOk P s pl cp sp high ra nativeSp arg live Dt DA a g domain young limit c)
    (runtime : ObservationRuntime runtimeOk c (copyMemory c ra nativeSp a s.world.exeName.length g domain young)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_executable_name) (fun d => d = c)
      (ExecutableNamePost runtimeOk P s pl cp sp high ra nativeSp arg live a g domain young c) := by
  apply (executable_name_machine c h.copy h.source).weaken (fun _ eq => eq)
  intro after post
  have layout : ObjAt after pl cp (resultWord young s.world.exeName.length).toNat (.bytes s.world.exeName) :=
    post.shell.object (fun i x hi => (post.bytes i (List.getElem?_eq_some_iff.mp hi).1).trans (h.sourceBytes i x hi))
  refine { post with
    data := ?_
    primitives := bindings_frame_outsideLog h.primitives h.bindingsOutside post.footprint
    platform := ⟨post.good, post.image, runtime after post.memory_complete h.runtime⟩
    loop := loop_of_abi_frame post.registers (by decide) h.loop
    resultRepr := ?_
    semantics := ?_ }
  · exact (h.data.frame_outsideLog h.payloadOutside post.footprint post.output).allocate
      (by intro t fs impossible; cases impossible) h.placed layout h.separate
  · simp [valWord, h.placed]
  · rfl

end OCaml.Vm.Primitives
