import OCaml.Vm.Sim.CountedInvariant
import OCaml.Vm.Sim.ChannelCountFrame
import OCaml.RefinementF1

/-! Reuse generic rows under a local runtime invariant. Channel calls change
the frozen world and use their counted machine summaries instead. Ordinary
rows still need actual frame instances for the effects they perform. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Counts depend on the channel model, independently of console, argv,
named values and the object-id counter. -/
theorem _root_.OCaml.Vm.ChannelCustomsRepr.of_chans_eq
    {Customs : Config → Nat → Prop} {c : Config} {cp : ChanPlace} {w w' : World}
    (counts : ChannelCustomsRepr Customs c cp w) (channels : w'.chans = w.chans) :
    ChannelCustomsRepr Customs c cp w' := by
  refine ⟨⟨fun id ch at_ => counts.references.refs id ch (by rwa [channels] at at_)⟩, ?_, ?_⟩
  · simpa only [channels] using counts.opened
  · simpa only [World.customs, channels] using counts.physical

/-- Retarget only runtime facts and the definitionally equal budget. The
ordinary representation and its selected channel placement are retained. -/
theorem _root_.OCaml.Running.retarget {L L' : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    (running : OCaml.Running L P s c) (runtime : L'.runtimeOk c)
    (budget : L'.budget = L.budget) : OCaml.Running L' P s c := by
  obtain ⟨pl, cp, sp, high, repr, geometry⟩ := running.stack
  exact { running with
    platform := ⟨running.platform.control, running.platform.image, runtime⟩
    stack := ⟨pl, cp, sp, high, repr,
      ⟨geometry.toArmGeometry, by rw [budget]; exact geometry.room⟩⟩ }

/-- A local layout used for one non-channel row. It freezes the boundary
channel world, while generic VM proofs retain their usual statements. -/
def countedLayout (L : OCaml.Layout) (Customs : Config → Nat → Prop) (cp : ChanPlace)
    (world : World) : OCaml.Layout :=
  ⟨fun c => L.runtimeOk c ∧ ChannelCustomsRepr Customs c cp world, L.budget⟩

/-- Register-only effects frame all count observations, using the same
physical accounting law as the counted C_CALL suffix. -/
theorem counted_memoryStable {L : OCaml.Layout} {Customs : Config → Nat → Prop}
    {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {cp : ChanPlace} {w : World}
    (stable : MemoryStable L.runtimeOk) (accounting : Gc.CustomAccounting Ready state Customs) :
    MemoryStable (countedLayout L Customs cp w).runtimeOk := by
  intro c d memory before
  exact ⟨stable c d memory before.1, (ChannelCountFrame.sameMemory accounting memory).repr before.2⟩

/-- Reuse a generic row at the local counted runtime. Its actual runtime
frame supplies the count observations; linked-list coherence recovers them
at the ordinary producer's selected stack placement. No preservation
supplier is added to the headline. -/
theorem counted_memory_row {L : OCaml.Layout} {P : Prog} {op : Opcode}
    {Customs : Config → Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (stable : MemoryStable L.runtimeOk) (accounting : Gc.CustomAccounting Ready state Customs)
    (row : ∀ L' : OCaml.Layout, MemoryStable L'.runtimeOk → OCaml.OpArm P (OCaml.LoopAt L' P) op)
    (channels : ∀ (s : St) (i : Instr) (s' : St),
      i.op = op → stepI P s i = .next s' → s'.world.chans = s.world.chans) :
    OCaml.OpArm P (CountedLoopAt Customs L P) op := by
  intro s c i reach h decoded opcode fragment
  obtain ⟨pl, cp, sp, high, repr, geometry⟩ := h.running.countedStack
  let L' := countedLayout L Customs cp s.world
  have running : OCaml.Running L' P s c :=
    h.running.toRunning.retarget ⟨h.running.platform.runtime, repr.counts⟩ rfl
  have outcome := row L' (counted_memoryStable stable accounting)
    s c i reach ⟨running, h.clock⟩ decoded opcode fragment
  cases effect : stepI P s i with
  | next s' =>
    obtain ⟨after, run, post⟩ := (show ∃ after, OCaml.Plus c after ∧ OCaml.LoopAt L' P s' after by
      simpa only [OCaml.ArmOutcome, effect] using outcome)
    have counts := post.running.platform.runtime.2.of_chans_eq (channels s i s' opcode effect)
    exact ⟨after, run, h.of_plus run
      (countedRunning_of_counts (post.running.retarget post.running.platform.runtime.1 rfl) counts)⟩
  | halt e w => simpa only [OCaml.ArmOutcome, effect] using outcome
  | unsupported | wrong => trivial

end OCaml.Vm.Sim
