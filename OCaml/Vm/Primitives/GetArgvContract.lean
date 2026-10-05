import OCaml.Vm.Primitives.ArgvTupleFinished
import OCaml.Vm.Primitives.ExecutableNameContract

namespace OCaml.Vm.Primitives.ArgvTuple
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- Every write of the complete `caml_sys_get_argv` run. -/
def getArgvLog (R : Nat → BitVec 64) (domain roots young blockYoung argv : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) : List WEntry :=
  allocatedLog R domain roots young blockYoung a len g ++
    tupleLog (frameSp (R 2)) (tupleWord blockYoung) (StringCopy.resultWord young len) argv domain roots

/-- The pair `caml_sys_get_argv` returns. -/
def argvPair (s : St) : Obj :=
  .block 0 [.ptr (s.heap.alloc (.bytes s.world.exeName)).2 0, s.world.argv]

/-- The state after the executable name is allocated, before the pair. -/
def afterName (s : St) : St :=
  {s with heap := (s.heap.alloc (.bytes s.world.exeName)).1,
          accu := .ptr (s.heap.alloc (.bytes s.world.exeName)).2 0}

/-- G1 obligations of the represented call: the machine-stage layout, the
source bytes and argv global, two fresh placements reserved in nursery
order, and separation of all writes from the live VM payload. -/
structure GetArgvInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (arg : Val)
    (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat) (R : Nat → BitVec 64)
    (bd be br : List (BitVec 8)) (a : Nat) (g : Nat → BitVec 8)
    (young limit blockYoung argv : BitVec 64) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high (R 1) [arg] c where
  machine : FinishStageInput live Dt DA R bd be br a s.world.exeName.length g young limit blockYoung argv c
  sourceBytes : ∀ i x, s.world.exeName[i]? = some x → g (a + i) = BitVec.ofNat 8 x.toNat
  argvRepr : valWord pl s.world.argv = some argv
  namePlaced : pl.φ (s.heap.alloc (.bytes s.world.exeName)).2 =
    some (StringCopy.resultWord young s.world.exeName.length).toNat
  nameSeparate : AllocationOutside P s pl (StringCopy.resultWord young s.world.exeName.length).toNat
    (.bytes s.world.exeName)
  pairPlaced : pl.φ ((afterName s).heap.alloc (argvPair s)).2 = some (tupleWord blockYoung).toNat
  pairSeparate : AllocationOutside P (afterName s) pl (tupleWord blockYoung).toNat (argvPair s)
  payloadOutside : PayloadOutside (getArgvLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung argv
    a s.world.exeName.length g) P s c pl cp sp
  bindingsOutside : BindingsOutside (getArgvLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung argv
    a s.world.exeName.length g) P c

structure GetArgvPost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (arg : Val) (live : Nat → Prop)
    (R : Nat → BitVec 64) (bd br : List (BitVec 8)) (a : Nat) (g : Nat → BitVec 8)
    (young blockYoung argv : BitVec 64) (before after : Config) : Prop
    extends LibraryPrimitivePost runtimeOk P s pl cp sp high "caml_sys_get_argv" [arg]
      (.ptr ((afterName s).heap.alloc (argvPair s)).2 0) (tupleWord blockYoung)
      ((afterName s).heap.alloc (argvPair s)).1 s.world (R 1) after,
      FinishStagePost live R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung argv a
        s.world.exeName.length g before after

theorem tuple_header {blockYoung : BitVec 64} (window : WriteWindow (tupleWord blockYoung) 8) :
    (tupleWord blockYoung).toNat - 8 = (SmallAllocation.nurseryHeader blockYoung 2#64).toNat := by
  have low := window.lower
  simp only [tupleWord, BitVec.toNat_add, BitVec.toNat_ofNat] at low ⊢
  omega

theorem get_argv_contract {runtimeOk P s pl cp sp high arg live Dt DA R bd be br a g young limit blockYoung argv c}
    (h : GetArgvInput runtimeOk P s pl cp sp high arg live Dt DA R bd be br a g young limit blockYoung argv c)
    (runtime : ObservationRuntime runtimeOk c (fun x => ((writeLog c.σ.mem (getArgvLog R (bytesVal .ld bd)
      (bytesVal .ld br) young blockYoung argv a s.world.exeName.length g))[x]?).getD 0)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_argv) (fun d => d = c)
      (GetArgvPost runtimeOk P s pl cp sp high arg live R bd br a g young blockYoung argv c) := by
  apply (argv_finish_stage h.machine).weaken (fun _ eq => eq)
  intro after post
  have outside := outsideLog_of_observedLog post.memory
  have d0 := h.data.frame_observedLog h.payloadOutside post.memory post.output
  have name := post.stringObject pl cp s.world.exeName rfl h.sourceBytes
  have d1 := d0.allocate (by intro t fs impossible; cases impossible) h.namePlaced name h.nameSeparate
  have pair : ObjAt after pl cp (tupleWord blockYoung).toNat (argvPair s) := by
    refine ⟨?_, ?_⟩
    · rw [tuple_header h.machine.layout.firstField]
      exact post.header
    · intro i v hv
      match i, hv with
      | 0, hv =>
        cases hv
        simp only [valWord, h.namePlaced, Option.map_some, Nat.mul_zero, Nat.add_zero,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact congrArg some post.fields.1.symm
      | 1, hv =>
        cases hv
        rw [h.argvRepr]
        exact congrArg some post.fields.2.symm
  have fields : AllocationRoots P (afterName s) (argvPair s) := by
    intro t fs same v member l located
    cases same
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact Live.root (by simp [roots, afterName]) located
    · exact Live.root (by simp [roots, afterName]) located
  have d2 := d1.allocate fields h.pairPlaced pair h.pairSeparate
  exact { post with
    pc := post.pc
    result := post.result
    data := d2
    primitives := bindings_frame_outsideLog h.primitives h.bindingsOutside outside
    platform := ⟨post.good, post.image,
      runtime after (fun x => (byte_total after x).trans (post.memory x)) h.runtime⟩
    loop := loop_of_abi_frame post.registers (by decide) h.loop
    resultRepr := by simp [valWord, h.pairPlaced]
    semantics := rfl }

end OCaml.Vm.Primitives.ArgvTuple
