import OCaml.Vm.Gc.MixedField
import OCaml.Vm.Gc.ForwardedObservations
import Vsa.Sim.IndexedLoop

namespace OCaml.Vm.Gc.MixedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Initial heap observations for a mixed copy/forwarded suffix. Register
maps are finite arithmetic predictions; `advance` relates them to the branch
computed from initial, framed words. No future machine state is supplied. -/
structure LoopData (maps : Nat → Nat → BitVec 64) (domain : BitVec 64)
    (a b count start : Nat) (initial : Config) (expected : Nat → BitVec 64) : Prop where
  geometry : FieldCopy.Geometry a b count
  slot : ∀ i, start ≤ i → i < count → maps i 8 = scanPtr a i
  delta : ∀ i, start ≤ i → i < count → maps i 18 = BitVec.ofNat 64 b - BitVec.ofNat 64 a
  target : ∀ i, start ≤ i → i < count → maps i 19 = BitVec.ofNat 64 b
  index : ∀ i, start ≤ i → i < count → maps i 9 = BitVec.ofNat 64 i
  runtime : ∀ i, start ≤ i → i < count → maps i 22 = BitVec.ofNat 64 Layout.sym_Caml_state
  nativeWindow : ∀ i, start ≤ i → i < count → MopupCall.nativeWindow (maps i) = MopupCall.nativeWindow (maps start)
  stackWindows : ∀ i, start ≤ i → i < count → ∀ cell ∈ OldifyEntry.saves,
    WriteWindow (OldifyEntry.frameSp (maps i) + BitVec.ofNat 64 cell.2) 8
  stack : (MopupCall.nativeWindow (maps start)).hi ≤ b - 8 ∨
    b + 8 * count ≤ (MopupCall.nativeWindow (maps start)).lo
  root : word initial Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  rootOutside : OutWRange (MopupCall.scanFootprint (maps start) b start count) Layout.sym_Caml_state 8
  lowerOutside : OutWRange (MopupCall.scanFootprint (maps start) b start count)
    (domain + BitVec.ofNat 64 Layout.off_young_start).toNat 8
  upperOutside : OutWRange (MopupCall.scanFootprint (maps start) b start count)
    (domain + BitVec.ofNat 64 Layout.off_young_end).toNat 8
  header : (word initial (b - 8)).toNat / 1024 = count
  headerOutside : OutWRange (MopupCall.scanFootprint (maps start) b start count) (b - 8) 8
  sourceOutside : ∀ i, start ≤ i → i < count →
    OutWRange (MopupCall.scanFootprint (maps start) b start count) (scanPtr a i).toNat 8
  conditions : ∀ i, start ≤ i → i < count →
    needsOldify domain (word initial (scanPtr a i).toNat) initial →
    ForwardedCall.Conditions (ForwardedField.args (maps i) initial) domain initial
  observations : ∀ i, start ≤ i → i < count →
    needsOldify domain (word initial (scanPtr a i).toNat) initial →
    ForwardedCall.ObservationsOutside (ForwardedField.args (maps i) initial) domain
      (MopupCall.scanFootprint (maps start) b start count)
  forwardingOutside : ∀ i, start ≤ i → i < count →
    needsOldify domain (word initial (scanPtr a i).toNat) initial →
    OutWRange (MopupCall.scanFootprint (maps start) b start count)
      (word initial (scanPtr a i).toNat).toNat 8
  value : ∀ i, start ≤ i → i < count → expected i =
    if needsOldify domain (word initial (scanPtr a i).toNat) initial
    then word initial (word initial (scanPtr a i).toNat).toNat else word initial (scanPtr a i).toNat
  advance : ∀ i, start ≤ i → i < count → maps (i + 1) =
    next (maps i) (decide (needsOldify domain (word initial (scanPtr a i).toNat) initial))

/-- Shared relocated scan plus the exact next native call interface. -/
structure LoopAt (maps : Nat → Nat → BitVec 64) (a b count start : Nat)
    (initial : Config) (expected : Nat → BitVec 64) (i : Nat) (c : Config) : Prop where
  scan : FieldCopy.ScanAtWith [1,8,9,10,11,12,14,15] a b count start initial i c
    (MopupCall.scanFootprint (maps start) b start count) expected
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (ForwardedField.carried (maps i))

theorem LoopAt.source {maps domain a b count start initial expected i c}
    (data : LoopData maps domain a b count start initial expected)
    (atHead : LoopAt maps a b count start initial expected i c) (bound : i < count) :
    word c (scanPtr a i).toNat = word initial (scanPtr a i).toNat :=
  frame_word atHead.scan.memory (data.sourceOutside i atHead.scan.lower bound)

/-- Parity and strict nursery membership are stable across preceding scan
writes, so the concrete route agrees with the arithmetic map prediction. -/
theorem LoopAt.route {maps domain a b count start initial expected i c}
    (data : LoopData maps domain a b count start initial expected)
    (atHead : LoopAt maps a b count start initial expected i c) (bound : i < count) :
    needsOldify domain (word c (maps i 8).toNat) c =
      needsOldify domain (word initial (scanPtr a i).toNat) initial := by
  unfold needsOldify
  rw [data.slot i atHead.scan.lower bound, atHead.source data bound]
  have lower := frame_word atHead.scan.memory data.lowerOutside
  have upper := frame_word atHead.scan.memory data.upperOutside
  change word c _ = word initial _ at lower upper
  simp only [Young.lowerWord, Young.upperWord, lower, upper]

theorem LoopAt.input {maps domain a b count start initial expected i c}
    (data : LoopData maps domain a b count start initial expected)
    (atHead : LoopAt maps a b count start initial expected i c) (bound : i < count) :
    Input (maps i) domain c := by
  have lower := atHead.scan.lower
  have slot := data.slot i lower bound
  have delta := data.delta i lower bound
  have target := data.target i lower bound
  have index := data.index i lower bound
  have registers : GHolds c.σ (FieldCopy.regs (maps i 8) (maps i 18) (maps i 19) (maps i 9)) := by
    simpa only [slot,delta,target,index] using atHead.scan.registers
  refine ⟨⟨atHead.scan.good, atHead.scan.minstret, atHead.scan.tick, atHead.scan.code,
    registers, ?_⟩, atHead.code, atHead.registers, ?_, ?_, ?_,
    (frame_word atHead.scan.memory data.rootOutside).trans data.root,
    data.windows, data.stackWindows i lower bound, ?_⟩
  · simpa only [slot] using data.geometry.sourceRange.window bound
  · simpa only [target] using FieldCopy.header_window data.geometry.targetRange
  · simpa only [slot,delta] using (data.geometry.windows bound).destination
  · have pin : gprGet c.σ 22 = some (maps i 22) := gholds_lookup _ atHead.registers rfl
    simpa only [data.runtime i lower bound] using pin
  · intro young
    have original : needsOldify domain (word initial (scanPtr a i).toNat) initial :=
      (atHead.route data bound) ▸ young
    have argsSame : ForwardedField.args (maps i) c = ForwardedField.args (maps i) initial := by
      funext n
      simp only [ForwardedField.args, slot, atHead.source data bound]
    rw [argsSame]
    exact (data.conditions i lower bound original).frame
      (data.observations i lower bound original) atHead.scan.memory

end OCaml.Vm.Gc.MixedField
