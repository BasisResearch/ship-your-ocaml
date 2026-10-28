import OCaml.Vm.Sim.CountedRuntime
import OCaml.Vm.Sim.ChannelReadiness
import OCaml.Vm.Sim.CcallNames

/-! Explicit entry counts let ordinary native contracts run at the local
counted layout. Return counts are recovered at the actual returned placement. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Retarget readiness without changing any fetch, placement or write guard. -/
theorem CcallReady.retarget {L L' : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {op : Opcode} {pl : Place} {cp : ChanPlace} {sp high domain table entry : Nat}
    {value env : BitVec 64} {index : BitVec 32} {name : String}
    (h : CcallReady op L P s c pl cp sp high domain table entry value env index name)
    (runtime : L'.runtimeOk c) (budget : L'.budget = L.budget) :
    CcallReady op L' P s c pl cp sp high domain table entry value env index name :=
  { h with runtime := runtime, geometry := h.geometry.retarget budget }

/-- Layout transport changes only runtime facts and the equal budget. -/
theorem CcallSetupPost.retarget {L L' : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {ra : BitVec 64} {args : List Val} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env : BitVec 64}
    (h : CcallSetupPost ra args L P s pl cp sp high domain entry env c)
    (runtime : L'.runtimeOk c) (budget : L'.budget = L.budget) :
    CcallSetupPost ra args L' P s pl cp sp high domain entry env c :=
  { h with input := { h.input with runtime := runtime }, geometry := h.geometry.retarget budget }

/-- The actual counted setup supplies the local runtime to the native contract. -/
theorem CountedCcallSetupPost.local {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {Customs : Config → Nat → Prop} {ra : BitVec 64} {args : List Val}
    {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64}
    (h : CountedCcallSetupPost Customs ra args L P s pl cp sp high domain entry env c) :
    CcallSetupPost ra args (countedLayout L Customs cp s.world) P s pl cp sp high domain entry env c :=
  { h.toCcallSetupPost with
    input := { h.input with runtime := ⟨h.input.runtime, h.counts⟩ }
    geometry := h.geometry.retarget rfl }

/-- Forget the local layout only after recovering counts at the returned cp.
The real semantic channel equality changes the frozen world; linked-list
uniqueness and total placement supply coherence at that same return. -/
theorem CcallReturnAt.of_countedLayout {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {Customs : Config → Nat → Prop} {ra : BitVec 64} {pl : Place} {cp cp0 : ChanPlace}
    {world : World} {sp high : Nat} {domain frameSp result env : BitVec 64}
    (h : CcallReturnAt ra (countedLayout L Customs cp0 world) P s pl cp sp high
      domain frameSp result env c) (channels : s.world.chans = world.chans) :
    CountedCcallReturnAt Customs ra L P s pl cp sp high domain frameSp result env c := by
  have counts := h.platform.runtime.2.of_chans_eq channels
  exact { h with
    platform := { h.platform with runtime := h.platform.runtime.1 }
    geometry := h.geometry.retarget rfl
    counts := counts.at_geometry h.data.world h.geometry.nursery }

/-- Shared native-summary adapter. The original entry count witness is an
explicit argument of CountedPrimReturnsAtR, independent of the later callee. -/
theorem counted_prim_returns_of_local {L : OCaml.Layout} {P : Prog}
    {Customs : Config → Nat → Prop} {op : Opcode} {ra : BitVec 64} {k : Nat} {name : String}
    (localReturns : ∀ cp world, PrimReturnsAt (countedLayout L Customs cp world) P op ra k name)
    (channels : ∀ args h w v h' w', primF1Impl name args h w = .ok v h' w' → w'.chans = w.chans) :
    CountedPrimReturnsAtR L P Customs op ra k name := by
  intro s c pl cp sp high table entry value env index v heap world reach ready counts sem words _succ
  obtain ⟨result, callee⟩ := localReturns cp s.world s c pl cp sp high table entry value env index
    v heap world reach (ready.retarget ⟨ready.runtime, counts⟩ rfl) sem words
  refine ⟨result, callee.fragment, callee.semantics, ?_⟩
  intro call setup placed
  exact (callee.summary call setup.local placed).weaken (fun _ h => h) fun after returned => by
    obtain ⟨cp', post⟩ := returned
    exact ⟨cp', post.of_countedLayout (channels _ _ _ _ _ _ sem)⟩

/-- The saved-ra window uses the existing native runtime frame and the
selected heap's channel/count frame on that exact window. -/
theorem counted_native_stable {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs)
    (stable : ∀ lo, Vsa.Sim.DlHeap.heapEnd ≤ lo →
      WindowStable Gc.f1Layout.runtimeOk [⟨lo, lo + 8⟩]) :
    ∀ lo, Vsa.Sim.DlHeap.heapEnd ≤ lo →
      WindowStable (countedLayout Gc.f1Layout Customs cp world).runtimeOk [⟨lo, lo + 8⟩] := by
  intro lo above c d frame before
  exact ⟨stable lo above c d frame before.1,
    (f1_stack_channelCountFrame custom before.1 before.2 (fun w hw => by
      simp only [List.mem_singleton] at hw
      subst w
      exact Or.inr above) frame).repr before.2⟩

end OCaml.Vm.Sim
