import OCaml.Vm.Sim.CountedCcallSetup

/-! Counted execution of the actual unary call arm. This retains the physical
count from the callee's execution through the suffix. It deliberately does not
claim to reconstruct `ChannelCustomsRepr`: that also needs the callee's natural
reference-count observations at its returned channel placement. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Logic

/-- Dispatch, the generated counted setup, the actual counted call, and the
generated return suffix on one execution. The physical successor count comes
from the callee's post, never from its readiness or a pre-call refcount store. -/
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
    ∃ after, OCaml.Plus c after ∧ CountedResult Customs
      (OCaml.Running Gc.f1Layout P {s with pc := s.pc + 2, accu := v, heap := heap, world := world})
      world.customs after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨n, call, prefixSteps, setup, youngKept⟩ := counted_c_call1_setup custom h counts dp
  have pre : Triple (fun x => x = d) (fun x => PCAt (BitVec.ofNat 64 entry) x ∧ x = call) := by
    rintro x rfl
    exact ⟨call, prefixSteps.toSteps, setup.target, rfl⟩
  have suffix : Triple
      (CountedResult Customs
        (CcallReturn (0x80003060#64) Gc.f1Layout P
          {s with pc := s.pc + 2, accu := v, heap := heap, world := world}
          pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16)) result env) world.customs)
      (CountedResult Customs
        (OCaml.Running Gc.f1Layout P {s with pc := s.pc + 2, accu := v, heap := heap, world := world})
        world.customs) := by
    intro f returned
    obtain ⟨cp', at_⟩ := returned.post
    obtain ⟨after, ⟨n, run⟩, running, memory⟩ := c_call1_return_framed f1_memoryStable at_
    refine ⟨after, run.toSteps, running, ?_⟩
    simpa only [Nat.add_zero] using (custom.accounting.sameMemory memory).count returned.physical
  have composed := callSeg pre
    (callee.summary call setup (by rw [youngKept]; exact h.allocPlaced)).run suffix
  obtain ⟨after, run, represented⟩ := composed d rfl
  exact ⟨_, after, run.toN_of_stepsField, represented⟩

end OCaml.Vm.Sim
