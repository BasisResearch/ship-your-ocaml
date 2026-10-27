import OCaml.Vm.Sim.CountedCcallSetup
import OCaml.Vm.Sim.CountedInvariant
import OCaml.Vm.Sim.AllocPlacesOk
import OCaml.Vm.Sim.G1Capacity

/-! Complete counted channel boundaries through the actual unary C_CALL run. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic

/-- C_CALL setup selects its channel placement from the counted loop stack.
The shared ordinary producer extends only the heap placement. -/
theorem CcallReady.of_counted_loop {Customs : Config → Nat → Prop} {L : OCaml.Layout}
    {P : Prog} {s : St} {c : Config} {op : Opcode} {index : BitVec 32} {name : String}
    (h : CountedLoopAt Customs L P s c) (code : DispatchCode P s op)
    (fetch : P.code[s.pc + 1]? = some index) (nonnegative : 0 ≤ index.toInt)
    (primitive : P.prims[index.toInt.toNat]? = some name)
    (space : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (places : ∀ young : BitVec 64, young.toNat % 8 = 0 → AllocPlacesOk name s young) :
    ∃ pl cp sp high entry value env, CcallReady op L P s c pl cp sp high
      (domainAt c) (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat
      entry value env index name ∧ ChannelCustomsRepr Customs c cp s.world := by
  obtain ⟨pl0, cp, sp, high, input, counts⟩ := ArmInput.of_counted_loop h code
  obtain ⟨pl, entry, value, env, ready⟩ := CcallReady.of_input input fetch nonnegative primitive space places
  exact ⟨pl, cp, sp, high, entry, value, env, ready, counts⟩

/-- Dispatch, the generated counted setup, the actual counted call, and the
generated return suffix on one execution. All count observations come from
the callee's actual post at the same returned channel placement. -/
theorem counted_c_call1_arm {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table entry : Nat}
    {value env result : BitVec 64} {index : BitVec 32} {name : String}
    {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (h : CcallReady .C_CALL1 Gc.f1Layout P s c pl cp sp high domain table entry value env index name)
    (counts : ChannelCustomsRepr Customs c cp s.world)
    (callee : CountedCcallCallee Customs (0x80003060#64) [s.accu] Gc.f1Layout P s
      pl cp sp high domain entry env name v result heap world) :
    ∃ after, OCaml.Plus c after ∧ CountedRunning Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨n, call, prefixSteps, setup, youngKept⟩ := counted_c_call1_setup custom h counts dp
  have pre : Triple (fun x => x = d) (fun x => PCAt (BitVec.ofNat 64 entry) x ∧ x = call) := by
    rintro x rfl
    exact ⟨call, prefixSteps.toSteps, setup.target, rfl⟩
  have suffix : Triple
      (CountedCcallReturn Customs (0x80003060#64) Gc.f1Layout P
        {s with pc := s.pc + 2, accu := v, heap := heap, world := world}
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16)) result env)
      (CountedRunning Customs Gc.f1Layout P
        {s with pc := s.pc + 2, accu := v, heap := heap, world := world}) := by
    intro f returned
    obtain ⟨cp', at_⟩ := returned.placed
    obtain ⟨after, ⟨n, run⟩, running, memory⟩ := c_call1_return_framed f1_memoryStable at_.toCcallReturnAt
    have counts := (ChannelCountFrame.sameMemory (cp := cp') custom.accounting memory).repr at_.counts
    refine ⟨after, run.toSteps, { toRunning := running.toRunning, countedStack := ?_ }⟩
    exact ⟨pl, cp', sp + 8 * 0, high, { toVmReprAt := running.represented, counts := counts }, running.geometry⟩
  have composed := callSeg pre
    (callee.summary call setup (by rw [youngKept]; exact h.allocPlaced)).run suffix
  obtain ⟨after, run, represented⟩ := composed d rfl
  exact ⟨_, after, run.toN_of_stepsField, represented⟩

/-- A successful unary call from the counted loop head, through the shared
placement producer and the actual setup/callee/suffix. `Fits` is applied to
the reachable semantic successor used by the callee's readiness proof. -/
theorem counted_c_call1_success {P : Prog} {s : St} {c : Config}
    {index : BitVec 32} {name : String} {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (fits : OCaml.Fits Gc.g1Budget P) (reach : Reach P s)
    (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (decoded : decodeAt P.code s.pc = some ⟨.C_CALL1, [index.toInt]⟩)
    (nonnegative : 0 ≤ index.toInt) (primitive : P.prims[index.toInt.toNat]? = some name)
    (member : name ∈ primsF1)
    (sem : primF1Impl name [s.accu] s.heap s.world = .ok v heap world)
    (returns : CountedPrimReturnsAtR Gc.f1Layout P Customs .C_CALL1 (0x80003060#64) 0 name) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world} after := by
  have effect : stepI P s ⟨.C_CALL1, [index.toInt]⟩ =
      .next {s with pc := s.pc + 2, accu := v, heap := heap, world := world} := by
    simp only [stepI, show ¬ index.toInt < 0 by omega, if_false, primitive, opt,
      cCall, prim, primF1, member, if_true, sem, List.length_cons, List.length_nil,
      Nat.add_sub_cancel, List.drop_zero]
  have successor := reach_next reach decoded effect
  obtain ⟨code, fetches⟩ := decode_fetch decoded
  obtain ⟨w, fetch, same⟩ := fetches 0 index.toInt rfl
  have eq : w = index := BitVec.eq_of_toInt_eq same
  subst w
  obtain ⟨pl, cp, sp, high, entry, value, env, ready, counts⟩ :=
    CcallReady.of_counted_loop h code fetch nonnegative primitive
      (stack_fits fits g1_capacity reach (k := 2)) (allocPlaces_ok name s)
  obtain ⟨result, callee⟩ := returns s c pl cp sp high _ entry value env index v heap world
    reach ready sem (fits _ successor).heap ⟨_, successor, rfl, rfl⟩
  obtain ⟨after, run, running⟩ := counted_c_call1_arm custom ready counts callee
  exact ⟨after, run, h.of_plus run running⟩

end OCaml.Vm.Sim
