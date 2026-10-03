import OCaml.Vm.Gc.MixedLoopState

namespace OCaml.Vm.Gc.MixedField
open Vsa.Machine Vsa.Sim Primitives

/-- External writes, such as queue removal and first-field processing, are
separate from the initial observations used by the mixed suffix. Forwarding
observations are required only for young values that use that route. -/
structure LoopOutside (maps : Nat → Nat → BitVec 64) (domain : BitVec 64)
    (a b count start : Nat) (initial : Config) (ws : List W) : Prop where
  root : OutWRange ws Layout.sym_Caml_state 8
  lower : OutWRange ws (domain + BitVec.ofNat 64 Layout.off_young_start).toNat 8
  upper : OutWRange ws (domain + BitVec.ofNat 64 Layout.off_young_end).toNat 8
  header : OutWRange ws (b - 8) 8
  source : ∀ i, start ≤ i → i < count → OutWRange ws (scanPtr a i).toNat 8
  conditions : ∀ i, start ≤ i → i < count →
    needsOldify domain (word initial (scanPtr a i).toNat) initial →
    ForwardedCall.ObservationsOutside (ForwardedField.args (maps i) initial) domain ws
  forwarding : ∀ i, start ≤ i → i < count →
    needsOldify domain (word initial (scanPtr a i).toNat) initial →
    OutWRange ws (word initial (scanPtr a i).toNat).toNat 8

/-- Preserve the fixed mixed-loop data across an earlier separated write
footprint. This transports route decisions as well as scalar values, so the
same initial register schedule remains valid after those writes. -/
theorem LoopData.frame {maps domain a b count start before expected ws} {after : Config}
    (data : LoopData maps domain a b count start before expected)
    (outside : LoopOutside maps domain a b count start before ws)
    (frame : FrameOn ws before.σ.mem after.σ.mem) :
    LoopData maps domain a b count start after expected := by
  have source : ∀ i, start ≤ i → i < count →
      word after (scanPtr a i).toNat = word before (scanPtr a i).toNat :=
    fun i lower upper => frame_word frame (outside.source i lower upper)
  have lower : Young.lowerWord domain after = Young.lowerWord domain before := frame_word frame outside.lower
  have upper : Young.upperWord domain after = Young.upperWord domain before := frame_word frame outside.upper
  have route : ∀ i, start ≤ i → i < count →
      needsOldify domain (word after (scanPtr a i).toNat) after =
        needsOldify domain (word before (scanPtr a i).toNat) before := by
    intro i lo hi
    simp only [needsOldify, source i lo hi, lower, upper]
  have sameArgs : ∀ i, start ≤ i → i < count →
      ForwardedField.args (maps i) after = ForwardedField.args (maps i) before := by
    intro i lo hi
    funext n
    simp only [ForwardedField.args, data.slot i lo hi, source i lo hi]
  refine { data with
    root := (frame_word frame outside.root).trans data.root
    header := ?_, conditions := ?_, observations := ?_, forwardingOutside := ?_, value := ?_, advance := ?_ }
  · rw [frame_word frame outside.header]
    exact data.header
  · intro i lo hi young
    have original := (route i lo hi) ▸ young
    rw [sameArgs i lo hi]
    exact (data.conditions i lo hi original).frame (outside.conditions i lo hi original) frame
  · intro i lo hi young
    rw [sameArgs i lo hi]
    exact data.observations i lo hi ((route i lo hi) ▸ young)
  · intro i lo hi young
    rw [source i lo hi]
    exact data.forwardingOutside i lo hi ((route i lo hi) ▸ young)
  · intro i lo hi
    simp only [route i lo hi]
    rw [source i lo hi]
    by_cases young : needsOldify domain (word before (scanPtr a i).toNat) before
    · rw [ite_eq_left young, frame_word frame (outside.forwarding i lo hi young)]
      simpa only [ite_eq_left young] using data.value i lo hi
    · simpa only [ite_eq_right young] using data.value i lo hi
  · intro i lo hi
    simpa only [route i lo hi] using data.advance i lo hi

/-- Read-only setup is the empty-write-footprint instance. -/
theorem LoopData.memory_eq {maps domain a b count start before expected} {after : Config}
    (data : LoopData maps domain a b count start before expected)
    (memory : after.σ.mem = before.σ.mem) :
    LoopData maps domain a b count start after expected := by
  apply data.frame (ws := [])
  · exact ⟨True.intro, True.intro, True.intro, True.intro,
      fun _ _ _ => True.intro,
      fun _ _ _ _ => ⟨True.intro, True.intro, True.intro, True.intro⟩,
      fun _ _ _ _ => True.intro⟩
  · intro a _
    rw [memory]

end OCaml.Vm.Gc.MixedField
