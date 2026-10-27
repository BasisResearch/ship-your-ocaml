import OCaml.Vm.Repr.ChannelCounts
import OCaml.Vm.Sim.ArmInput

/-! The counted relation for the existing arbitrary-relation `F1Arms`
assembly. Its placement is selected once for both the ordinary stack and
complete physical channel accounting. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- The linked list fixes every valid channel placement when every channel
is placed. This lets shared ordinary producers choose their stack witness
without discarding accounting carried at another represented placement. -/
theorem placedChannels_injective {cp cp' : ChanPlace} (n : Nat)
    (total : ∀ id, id < n → ∃ a, cp id = some a)
    (total' : ∀ id, id < n → ∃ a, cp' id = some a)
    (same : Gc.placedChannels cp n = Gc.placedChannels cp' n) :
    ∀ id, id < n → cp id = cp' id := by
  induction n with
  | zero => intro id bound; omega
  | succ n ih =>
    obtain ⟨a, at_⟩ := total n (by omega)
    obtain ⟨b, at_'⟩ := total' n (by omega)
    rw [Gc.placedChannels_push (fun _ _ => rfl) at_,
      Gc.placedChannels_push (fun _ _ => rfl) at_'] at same
    obtain ⟨head, tail⟩ := List.cons.inj same
    intro id bound
    by_cases last : id = n
    · subst id
      rw [at_, at_', head]
    · exact ih (fun id bound => total id (by omega))
        (fun id bound => total' id (by omega)) tail id (by omega)

/-- Boundary coherence follows from the actual linked-list geometry and
represented natural refcounts, without deriving a physical count from
`runtimeOk` or from the reference sum. The physical witness is retained. -/
theorem _root_.OCaml.Vm.ChannelCustomsRepr.at_geometry {Customs : Config → Nat → Prop}
    {P : Prog} {s : St} {c : Config} {pl : Place} {cp cp' : ChanPlace} {high : Nat}
    (counts : ChannelCustomsRepr Customs c cp s.world)
    (world : WorldRepr c cp' s.world)
    (geometry : Gc.NurseryGeometry P s c pl cp' high) :
    ChannelCustomsRepr Customs c cp' s.world := by
  have same := placedChannels_injective s.world.chans.length
    (fun id bound => by
      obtain ⟨a, placed, _⟩ := counts.references.refs id _ (List.getElem?_eq_getElem bound)
      exact ⟨a, placed⟩)
    (fun id bound => by
      obtain ⟨a, placed, _⟩ := world.chans id _ (List.getElem?_eq_getElem bound)
      exact ⟨a, placed⟩)
    (counts.opened.unique geometry.channelsListed)
  refine ⟨⟨?_⟩, geometry.channelsListed, counts.physical⟩
  intro id ch at_
  obtain ⟨a, placed, refs⟩ := counts.references.refs id ch at_
  exact ⟨a, (same id (List.getElem?_eq_some_iff.mp at_).1).symm.trans placed, refs⟩

/-- The ordinary loop relation and counted stack at the same placement. -/
structure CountedRunning (Customs : Config → Nat → Prop) (L : OCaml.Layout)
    (P : Prog) (s : St) (c : Config) : Prop extends OCaml.Running L P s c where
  countedStack : ∃ pl cp sp high, CountedVmReprAt Customs P s c pl cp sp high ∧
    OCaml.LoopGeometry L P s c pl cp high

/-- Reuse an ordinary row's own stack witness once its physical/refcount
observations have been framed. The opened list determines the placement. -/
theorem countedRunning_of_counts {Customs : Config → Nat → Prop} {L : OCaml.Layout}
    {P : Prog} {s : St} {c : Config} {cp : ChanPlace}
    (running : OCaml.Running L P s c) (counts : ChannelCustomsRepr Customs c cp s.world) :
    CountedRunning Customs L P s c := by
  obtain ⟨pl, cp', sp, high, repr, geometry⟩ := running.stack
  exact { toRunning := running, countedStack :=
    ⟨pl, cp', sp, high, { repr with counts := counts.at_geometry repr.world geometry.nursery }, geometry⟩ }

/-- The counted F1 loop head, including dispatch's clock. -/
structure CountedLoopAt (Customs : Config → Nat → Prop) (L : OCaml.Layout)
    (P : Prog) (s : St) (c : Config) : Prop where
  running : CountedRunning Customs L P s c
  clock : c.tick < 2

theorem CountedLoopAt.toLoopAt {Customs : Config → Nat → Prop} {L : OCaml.Layout}
    {P : Prog} {s : St} {c : Config} (h : CountedLoopAt Customs L P s c) :
    OCaml.LoopAt L P s c := ⟨h.running.toRunning, h.clock⟩

theorem CountedLoopAt.of_plus {Customs : Config → Nat → Prop} {L : OCaml.Layout}
    {P : Prog} {s s' : St} {c d : Config} (h : CountedLoopAt Customs L P s c)
    (run : OCaml.Plus c d) (running : CountedRunning Customs L P s' d) :
    CountedLoopAt Customs L P s' d :=
  ⟨running, let ⟨_, steps⟩ := run; steps.tick_lt h.clock⟩

/-- Dispatch uses the counted stack's own channel placement. Choosing the
ordinary stack witness again would lose the association with the counts. -/
theorem ArmInput.of_counted_loop {Customs : Config → Nat → Prop} {L : OCaml.Layout}
    {P : Prog} {s : St} {op : Opcode} {c : Config}
    (h : CountedLoopAt Customs L P s c) (code : DispatchCode P s op) :
    ∃ pl cp sp high, ArmInput L P s op c pl cp sp high ∧
      ChannelCustomsRepr Customs c cp s.world := by
  obtain ⟨pl, cp, sp, high, repr, geometry⟩ := h.running.countedStack
  refine ⟨pl, cp, sp, high, ?_, repr.counts⟩
  exact ArmInput.of_repr repr.toVmReprAt h.running.platform h.running.loop h.clock
    (geometry.code_read (by simpa using (Array.getElem?_eq_some_iff.mp code.fetch).1))
    code.fetch geometry h.running.native

end OCaml.Vm.Sim
