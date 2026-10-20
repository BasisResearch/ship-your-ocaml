import OCaml.Vm.Sim.StringAllocEntry
import OCaml.Vm.Sim.LibraryEntry
import OCaml.Vm.Sim.CopyStringInput
import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Gc.ImageLibrary
import OCaml.Vm.Primitives.Channel.MlOpen
import OCaml.Vm.Primitives.Channel.OpenRepr

/-!
# `caml_ml_open_descriptor_out` at a C_CALL site

The runtime side is the named premise `OpenOutRuntime L` (lane a6-gc, who
discharges it for `Gc.f1Layout` with `CustomMemCall`): the custom
allocation's readiness, the agreed major-slice open premise (`budget`), newlib's
heap invariant and the console statics at every runtime config, and the
runtime after the opening (`after`).

`open_out_entry` turns the C_CALL entry into `ml_open_descriptor_out`'s
premises: `OutInput` from `LibHeapAt` (`out_input`), `OutNursery`
(`out_nursery`, with the nursery's room and bounds from the geometry), and one
custom allocation's readiness.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup (NativeFrame)

/-- **The runtime across `caml_ml_open_descriptor_out`** (named premise, lane
a6-gc, who discharges it for `Gc.f1Layout` together with `CustomMemCall`).
`L.runtimeOk` carries no custom-allocation state, so the call's readiness and
the runtime after the opening are supplied here. -/
structure OpenOutRuntime (L : OCaml.Layout) where
  Ready : Nat → Config → Prop
  state : Config → Nat → Prop
  custom : Gc.CustomMemCall Ready state
  /-- **The agreed major-slice open premise**: one more channel custom
  allocation is quiet. False after the fifth since the cut, when
  `caml_alloc_custom_mem` requests a major slice (G2). -/
  budget : ∀ c, L.runtimeOk c → ∃ k, Ready (k + 1) c
  /-- newlib's heap invariant (F1: `F1Pins.libHeap`) -/
  heap : ∀ c, L.runtimeOk c → Gc.LibHeap c
  /-- the console statics (F1: `F1Pins.console`) -/
  console : ∀ c, L.runtimeOk c → ConsoleWrite.ConsoleRuntime c
  /-- the runtime after the opening, from the heap invariant at the entry and
  everything the primitive's summary exports (the call's whole
  `CustomMemReturned` at its site, `Ready k`) -/
  after : ∀ {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {k : Nat}
    {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config},
    L.runtimeOk c → Gc.LibHeapAt H cap chs c →
    Channel.OpenedOut imageLive Ready state k H (cap - 65616) 65616 sp ra s0 s1 s2 v head c d →
    L.runtimeOk d

theorem _root_.OCaml.Vm.Gc.placedChannels_length (cp : ChanPlace) (n : Nat) : (Gc.placedChannels cp n).length ≤ n := by
  unfold Gc.placedChannels
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

/-- **`caml_ml_open_descriptor_out`'s premises at the C_CALL entry**: newlib's
heap over the placed channel records, the primitive's input on the native
stack, the collector's side, and one quiet custom allocation. -/
theorem open_out_entry {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {c : Config}
    (rt : OpenOutRuntime L) (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (fits : s.heap.words + 3 ≤ L.budget.heapWords) (bound : s.world.chans.length < Gc.maxChannels)
    {v : BitVec 64} (value : gpr c 10 = some v) (console : v = 3#64 ∨ v = 5#64) :
    ∃ (H : List (Nat × Nat)) (cap N k : Nat) (s0 s1 s2 : BitVec 64),
      Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c ∧
      Channel.OutInput imageLive H (cap - 65616) 65616 (BitVec.ofNat 64 N) ra s0 s1 s2 v
        (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)) c ∧
      Channel.OutNursery H (Gc.placedChannels cp s.world.chans.length) c ∧ rt.Ready (k + 1) c ∧
      gpr c 2 = some (BitVec.ofNat 64 N) := by
  have input := setup.input
  obtain ⟨H, cap, chs, heap⟩ := rt.heap c input.runtime
  have ng := setup.geometry.nursery
  have same : chs = Gc.placedChannels cp s.world.chans.length :=
    Gc.OpenChannels.unique heap.channels ng.channelsListed
  subst same
  obtain ⟨N, e⟩ := StringAllocEntry.of_setup setup fits
  obtain ⟨k, ready⟩ := rt.budget c input.runtime
  have nl := e.nativeLow
  have nh := e.nativeHigh
  have top : Layout.sym_stack_top < 2 ^ 64 := by decide
  have hN : (BitVec.ofNat 64 N).toNat = N := toNat_ofNat_small (Nat.lt_of_le_of_lt nh top)
  have frame : NativeFrame (BitVec.ofNat 64 N) 592 :=
    ⟨by rw [hN]; exact Nat.le_trans (Nat.add_le_add_left (by decide) _) nl, by rw [hN]; exact nh, by rw [hN]; exact e.nativeAligned,
      by decide⟩
  obtain ⟨s0, h0⟩ := Option.isSome_iff_exists.mp (setup.calleeSaved 8 (by simp))
  obtain ⟨s1, h1⟩ := Option.isSome_iff_exists.mp (setup.calleeSaved 9 (by simp))
  obtain ⟨s2, h2⟩ := Option.isSome_iff_exists.mp (setup.calleeSaved 18 (by simp))
  have platform : VsaIris.Inst.VsaOk imageLive c :=
    ⟨input.good, input.tick, fun n lo hi => input.loop.gprs.get n lo (by omega), imageLive_present input.image,
      input.loop.htifIdle⟩
  have room := e.room
  have lowM := ng.nurseryLow
  refine ⟨H, cap, N, k, s0, s1, s2, heap,
    Channel.out_input heap (Nat.lt_of_le_of_lt (Gc.placedChannels_length _ _) bound) input.toLeafInput platform
      (roR_of_gp input.loop.gp).1 e.stack frame h0 h1 h2 value (rt.console c input.runtime) console,
    Channel.out_nursery heap (by omega) e.youngAligned (by omega) ng.nurseryHigh, ready, e.stack⟩

end OCaml.Vm.Sim
