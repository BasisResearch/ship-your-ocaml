import OCaml.Vm.Sim.CountedCcallSetup

/-! Complete counted channel boundaries through the actual unary C_CALL run. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic

/-- The ordinary loop relation and counted stack at the same selected placement. -/
structure CountedRunning (Customs : Config → Nat → Prop) (L : OCaml.Layout)
    (P : Prog) (s : St) (c : Config) : Prop extends OCaml.Running L P s c where
  countedStack : ∃ pl cp sp high, CountedVmReprAt Customs P s c pl cp sp high ∧
    OCaml.LoopGeometry L P s c pl cp high

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

end OCaml.Vm.Sim
