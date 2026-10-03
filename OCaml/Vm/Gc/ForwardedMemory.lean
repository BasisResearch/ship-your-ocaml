import OCaml.Vm.Gc.ForwardedLoopState
import OCaml.Vm.Gc.RelocatedPayload

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives

/-- Field arguments depend only on memory, so read-only setup preserves them. -/
theorem args_memory_eq {R} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    args R after = args R before := by
  funext n
  simp only [args, word, memory]

/-- All scalar observations used by the fixed suffix data are outside an
external write footprint, such as queue removal plus first-field handling. -/
structure LoopOutside (R : Nat → BitVec 64) (domain : BitVec 64)
    (a b count start : Nat) (initial : Config) (ws : List W) : Prop where
  header : OutWRange ws (b - 8) 8
  source : ∀ i, start ≤ i → i < count → OutWRange ws (scanPtr a i).toNat 8
  conditions : ∀ i, start ≤ i → i < count →
    ForwardedCall.ObservationsOutside (args (cursor R a start i) initial) domain ws
  forwarding : ∀ i, start ≤ i → i < count →
    OutWRange ws (word initial (scanPtr a i).toNat).toNat 8

/-- Transport fixed suffix data across a separated write footprint. This
connects earlier collector stages to the loop without assuming a future
machine state or re-supplying each iteration's input. -/
theorem LoopData.frame {R domain a b count start before expected ws} {after : Config}
    (data : LoopData R domain a b count start before expected)
    (outside : LoopOutside R domain a b count start before ws)
    (frame : FrameOn ws before.σ.mem after.σ.mem) :
    LoopData R domain a b count start after expected := by
  have source : ∀ i, start ≤ i → i < count →
      word after (scanPtr a i).toNat = word before (scanPtr a i).toNat :=
    fun i lower upper => frame_word frame (outside.source i lower upper)
  have sameArgs : ∀ i, start ≤ i → i < count →
      args (cursor R a start i) after = args (cursor R a start i) before := by
    intro i lower upper
    funext n
    simp only [args, show cursor R a start i 8 = scanPtr a i from rfl, source i lower upper]
  refine { data with
    header := ?_, even := ?_, conditions := ?_, observations := ?_,
    forwardingOutside := ?_, forwarding := ?_ }
  · rw [frame_word frame outside.header]
    exact data.header
  · intro i lower upper
    rw [source i lower upper]
    exact data.even i lower upper
  · intro i lower upper
    rw [sameArgs i lower upper]
    exact (data.conditions i lower upper).frame (outside.conditions i lower upper) frame
  · intro i lower upper
    rw [sameArgs i lower upper]
    exact data.observations i lower upper
  · intro i lower upper
    rw [source i lower upper]
    exact data.forwardingOutside i lower upper
  · intro i lower upper
    rw [source i lower upper, frame_word frame (outside.forwarding i lower upper)]
    exact data.forwarding i lower upper

/-- Read-only setup transports the fixed field observations and geometry
used to derive every suffix iteration's concrete callee input. -/
theorem LoopData.memory_eq {R domain a b count start before expected} {after : Config}
    (data : LoopData R domain a b count start before expected)
    (memory : after.σ.mem = before.σ.mem) :
    LoopData R domain a b count start after expected := by
  apply data.frame (ws := [])
  · exact ⟨True.intro, fun _ _ _ => True.intro,
      fun _ _ _ => ⟨True.intro, True.intro, True.intro, True.intro⟩,
      fun _ _ _ => True.intro⟩
  · intro a _
    rw [memory]

end OCaml.Vm.Gc.ForwardedField

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Reloc

theorem RelocatingGrey.memory_eq {a b fields pl μ before} {after : Config}
    (grey : RelocatingGrey a b fields pl μ before)
    (memory : after.σ.mem = before.σ.mem) : RelocatingGrey a b fields pl μ after := by
  constructor
  · intro v member
    simpa only [Eqv.val, word, memory] using grey.first v member
  · intro i v member lower
    simpa only [Eqv.val, word, memory] using grey.suffix i v member lower

end OCaml.Vm.Gc.FieldCopy
