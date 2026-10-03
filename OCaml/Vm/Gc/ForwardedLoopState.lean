import OCaml.Vm.Gc.ForwardedContext
import OCaml.Vm.Gc.ForwardedObservations
import Vsa.Sim.IndexedLoop

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Register map at an indexed field boundary. The first iteration retains
its incoming return register; subsequent ones retain the actual mopup link. -/
def cursor (R : Nat → BitVec 64) (a start i n : Nat) : BitVec 64 :=
  if n = 1 then (if i = start then R 1 else MopupCall.call.link)
  else if n = 8 then scanPtr a i else if n = 9 then BitVec.ofNat 64 i else R n

theorem cursor_next {R a start i} (lower : start ≤ i) :
    next (cursor R a start i) = cursor R a start (i + 1) := by
  funext n
  have later : i + 1 ≠ start := by omega
  by_cases one : n = 1
  · subst n; simp [next, cursor, later]
  by_cases eight : n = 8
  · subst n; simp [next, cursor, scanPtr_succ]
  by_cases nine : n = 9
  · subst n; simp [next, cursor, BitVec.ofNat_add]
  simp [next, cursor, one, eight, nine]

/-- Fixed observations and geometry for a suffix whose young fields already
have forwarding headers. These are heap/data facts, not execution premises.
The fresh-copy case will extend the partial relocation while scanning. -/
structure LoopData (R : Nat → BitVec 64) (domain : BitVec 64)
    (a b count start : Nat) (initial : Config) (expected : Nat → BitVec 64) : Prop where
  geometry : FieldCopy.Geometry a b count
  delta : R 18 = BitVec.ofNat 64 b - BitVec.ofNat 64 a
  target : R 19 = BitVec.ofNat 64 b
  runtime : R 22 = BitVec.ofNat 64 Layout.sym_Caml_state
  stackWindows : ∀ cell ∈ OldifyEntry.saves,
    WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  stack : (MopupCall.nativeWindow R).hi ≤ b - 8 ∨
    b + 8 * count ≤ (MopupCall.nativeWindow R).lo
  header : (word initial (b - 8)).toNat / 1024 = count
  headerOutside : OutWRange (MopupCall.scanFootprint R b start count) (b - 8) 8
  sourceOutside : ∀ i, start ≤ i → i < count →
    OutWRange (MopupCall.scanFootprint R b start count) (scanPtr a i).toNat 8
  even : ∀ i, start ≤ i → i < count → (word initial (scanPtr a i).toNat).toNat % 2 = 0
  conditions : ∀ i, start ≤ i → i < count →
    ForwardedCall.Conditions (args (cursor R a start i) initial) domain initial
  observations : ∀ i, start ≤ i → i < count →
    ForwardedCall.ObservationsOutside (args (cursor R a start i) initial) domain
      (MopupCall.scanFootprint R b start count)
  forwardingOutside : ∀ i, start ≤ i → i < count →
    OutWRange (MopupCall.scanFootprint R b start count)
      (word initial (scanPtr a i).toNat).toNat 8
  forwarding : ∀ i, start ≤ i → i < count →
    word initial (word initial (scanPtr a i).toNat).toNat = expected i

/-- The ordinary scan invariant augmented by the callee code image and its
next native register inputs. All remaining field observations are framed
from the fixed initial boundary by LoopData. -/
structure LoopAt (R : Nat → BitVec 64) (a b count start : Nat)
    (initial : Config) (expected : Nat → BitVec 64) (i : Nat) (c : Config) : Prop where
  scan : FieldCopy.ScanAtWith [1,8,9,10,11,12,14,15] a b count start initial i c
    (MopupCall.scanFootprint R b start count) expected
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (carried (cursor R a start i))

theorem LoopAt.source {R domain a b count start initial expected i c}
    (data : LoopData R domain a b count start initial expected)
    (atHead : LoopAt R a b count start initial expected i c) (bound : i < count) :
    word c (scanPtr a i).toNat = word initial (scanPtr a i).toNat :=
  frame_word atHead.scan.memory (data.sourceOutside i atHead.scan.lower bound)

theorem LoopAt.input {R domain a b count start initial expected i c}
    (data : LoopData R domain a b count start initial expected)
    (atHead : LoopAt R a b count start initial expected i c) (bound : i < count) :
    Input (cursor R a start i) domain c := by
  have source := atHead.source data bound
  have argsSame : args (cursor R a start i) c = args (cursor R a start i) initial := by
    funext n
    simp only [args, show cursor R a start i 8 = scanPtr a i from rfl, source]
  refine ⟨atHead.scan.good, atHead.scan.minstret, atHead.scan.tick, atHead.scan.code,
    atHead.code, atHead.registers, data.geometry.sourceRange.window bound, ?_, ?_,
    data.stackWindows, ?_, ?_⟩
  · simpa only [show cursor R a start i 19 = R 19 from rfl, data.target] using
      FieldCopy.header_window data.geometry.targetRange
  · have pin : gprGet c.σ 22 = some (R 22) := gholds_lookup _ atHead.registers rfl
    simpa only [data.runtime] using pin
  · simpa only [show cursor R a start i 8 = scanPtr a i from rfl, source] using
      data.even i atHead.scan.lower bound
  · rw [argsSame]
    exact (data.conditions i atHead.scan.lower bound).frame
      (data.observations i atHead.scan.lower bound) atHead.scan.memory

end OCaml.Vm.Gc.ForwardedField
