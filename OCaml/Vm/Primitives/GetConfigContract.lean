import OCaml.Vm.Primitives.ConfigTupleFinished
import OCaml.Vm.Primitives.GetArgvContract

namespace OCaml.Vm.Primitives.ConfigTuple
open OCaml.Bytecode Vsa.Machine Vsa.Sim
open ArgvTuple (frameSp)

/-- `OCAML_OS_TYPE` of this build, as `primF1Impl` allocates it. -/
def osType : List UInt8 := "Unix".toList.map (·.toNat.toUInt8)

/-- Every write of the complete `caml_sys_get_config` run. -/
def getConfigLog (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (g : Nat → BitVec 8) : List WEntry :=
  allocatedLog R domain roots young blockYoung osType.length g ++
    tripleLog (frameSp (R 2)) (tripleWord blockYoung) (StringCopy.resultWord young osType.length) domain roots

/-- The triple `caml_sys_get_config` returns. -/
def configTriple (s : St) : Obj :=
  .block 0 [.ptr (s.heap.alloc (.bytes osType)).2 0, Val.ofInt 64, Val.ofBool false]

/-- The state after the OS type string is allocated, before the triple. -/
def afterOsType (s : St) : St :=
  {s with heap := (s.heap.alloc (.bytes osType)).1, accu := .ptr (s.heap.alloc (.bytes osType)).2 0}

/-- G1 obligations of the represented call: the machine-stage layout, the
literal's bytes, two fresh placements in nursery order, and separation of all
writes from the live VM payload. -/
structure GetConfigInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (arg : Val)
    (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat) (R : Nat → BitVec 64)
    (bd br : List (BitVec 8)) (g : Nat → BitVec 8)
    (young limit blockYoung : BitVec 64) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high (R 1) [arg] c where
  machine : FinishStageInput live Dt DA R bd br osType.length g young limit blockYoung c
  sourceBytes : ∀ i x, osType[i]? = some x → g (osTypeAddress.toNat + i) = BitVec.ofNat 8 x.toNat
  namePlaced : pl.φ (s.heap.alloc (.bytes osType)).2 = some (StringCopy.resultWord young osType.length).toNat
  nameSeparate : AllocationOutside P s pl (StringCopy.resultWord young osType.length).toNat (.bytes osType)
  triplePlaced : pl.φ ((afterOsType s).heap.alloc (configTriple s)).2 = some (tripleWord blockYoung).toNat
  tripleSeparate : AllocationOutside P (afterOsType s) pl (tripleWord blockYoung).toNat (configTriple s)
  payloadOutside : PayloadOutside (getConfigLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung g)
    P s c pl cp sp
  bindingsOutside : BindingsOutside (getConfigLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung g) P c

structure GetConfigPost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (arg : Val) (live : Nat → Prop)
    (R : Nat → BitVec 64) (bd br : List (BitVec 8)) (g : Nat → BitVec 8)
    (young blockYoung : BitVec 64) (before after : Config) : Prop
    extends LibraryPrimitivePost runtimeOk P s pl cp sp high "caml_sys_get_config" [arg]
      (.ptr ((afterOsType s).heap.alloc (configTriple s)).2 0) (tripleWord blockYoung)
      ((afterOsType s).heap.alloc (configTriple s)).1 s.world (R 1) after,
      FinishStagePost live R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung osType.length g before after

theorem triple_header {blockYoung : BitVec 64} (window : WriteWindow (tripleWord blockYoung) 8) :
    (tripleWord blockYoung).toNat - 8 = (SmallAllocation.nurseryHeader blockYoung 3#64).toNat := by
  have low := window.lower
  simp only [tripleWord, BitVec.toNat_add, BitVec.toNat_ofNat] at low ⊢
  omega

theorem get_config_contract {runtimeOk P s pl cp sp high arg live Dt DA R bd br g young limit blockYoung c}
    (h : GetConfigInput runtimeOk P s pl cp sp high arg live Dt DA R bd br g young limit blockYoung c)
    (runtime : ObservationRuntime runtimeOk c (fun x => ((writeLog c.σ.mem (getConfigLog R (bytesVal .ld bd)
      (bytesVal .ld br) young blockYoung g))[x]?).getD 0)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_config) (fun d => d = c)
      (GetConfigPost runtimeOk P s pl cp sp high arg live R bd br g young blockYoung c) := by
  apply (config_finish_stage h.machine).weaken (fun _ eq => eq)
  intro after post
  have outside := outsideLog_of_observedLog post.memory
  have d0 := h.data.frame_observedLog h.payloadOutside post.memory post.output
  have name := post.stringObject pl cp osType rfl h.sourceBytes
  have d1 := d0.allocate (by intro t fs impossible; cases impossible) h.namePlaced name h.nameSeparate
  have triple : ObjAt after pl cp (tripleWord blockYoung).toNat (configTriple s) := by
    refine ⟨?_, ?_⟩
    · rw [triple_header h.machine.layout.firstField]
      exact post.header
    · intro i v hv
      match i, hv with
      | 0, hv =>
        cases hv
        simp only [valWord, h.namePlaced, Option.map_some, Nat.mul_zero, Nat.add_zero,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact congrArg some post.field0.symm
      | 1, hv =>
        cases hv
        rw [post.field1]
        rfl
      | 2, hv =>
        cases hv
        rw [post.field2]
        rfl
  have fields : AllocationRoots P (afterOsType s) (configTriple s) := by
    intro t fs same v member l located
    cases same
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Live.root (by simp [roots, afterOsType]) located
    · cases located
    · cases located
  have d2 := d1.allocate fields h.triplePlaced triple h.tripleSeparate
  exact { post with
    pc := post.pc
    result := post.result
    data := d2
    primitives := bindings_frame_outsideLog h.primitives h.bindingsOutside outside
    platform := ⟨post.good, post.image,
      runtime after (fun x => (byte_total after x).trans (post.memory x)) h.runtime⟩
    loop := loop_of_abi_frame post.registers (by decide) h.loop
    resultRepr := by simp [valWord, h.triplePlaced]
    semantics := rfl }

end OCaml.Vm.Primitives.ConfigTuple
