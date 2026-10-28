import OCaml.Vm.Sim.CountedPrimAdapter
import OCaml.Vm.Sim.F1Console
import OCaml.Vm.Sim.ConsoleCounts

/-! Actual console windows preserve the counted runtime. Frozen count places
are related to the selected open list, independently of the caller's places. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Refcounts and links occupy the fixed middle of each record. The target
record is handled by its offsets; every other record by ledger separation. -/
theorem console_fixed_out {a b sp x : Nat}
    (low : Vsa.Sim.DlHeap.heapStart ≤ b)
    (high : b + Gc.chanRecordBytes ≤ Vsa.Sim.DlHeap.heapEnd)
    (apart : b = a ∨ b + Gc.chanRecordBytes ≤ a ∨ a + Gc.chanRecordBytes ≤ b)
    (native : Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ sp)
    (lo : b + 32 ≤ x) (hi : x < b + 72) : OutW (consoleWindows sp a) x := by
  apply Gc.outW_of
  intro w hw
  simp only [consoleWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [Gc.chanRecordBytes, chanOffBuff, ioBufferSize, nativeHeadroom,
    Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at *
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Layout.sym_errno, Layout.sym_impure_data] <;> (try dsimp only) <;>
    rcases apart with eq | apart | apart <;> omega

/-- Static observations other than errno miss the actual console windows. -/
theorem console_static_out {a sp x : Nat}
    (record : Vsa.Sim.DlHeap.heapStart ≤ a)
    (native : Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ sp)
    (low : x < Vsa.Sim.DlHeap.heapStart)
    (errno : x < Layout.sym_errno ∨ Layout.sym_errno + 4 ≤ x)
    (impure : x < Layout.sym_impure_data ∨ Layout.sym_impure_data + 4 ≤ x) :
    OutW (consoleWindows sp a) x := by
  apply Gc.outW_of
  intro w hw
  simp only [consoleWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at *
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> (try dsimp only) <;> omega

/-- The actual physical, refcount and open-link frame for console calls.
The selected LibHeapAt supplies bounds, record disjointness and custom-space
separation; CustomMemCall supplies the physical accounting law. -/
theorem f1_console_channelCountFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    {c d : Config} {a sp : Nat}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Runtime c)
    (counts : ChannelCustomsRepr Customs c cp world) (opened : Gc.OpenAt c a)
    (native : Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ sp)
    (frame : FrameOnD (consoleWindows sp a) c.σ.mem d.σ.mem) :
    ChannelCountFrame Customs cp world c d := by
  obtain ⟨H, cap, chs, heap⟩ := runtime.freeListShape.libHeap
  have target := heap.open_mem opened
  have bounds (b : Nat) (member : b ∈ chs) :
      Vsa.Sim.DlHeap.heapStart ≤ b ∧ b + Gc.chanRecordBytes ≤ Vsa.Sim.DlHeap.heapEnd := by
    obtain ⟨e, he, lo, hi⟩ := heap.records b member
    have arena := heap.ready.block_bounds he
    dsimp only at lo hi
    omega
  have targetLow := (bounds a target).1
  have member (id : Nat) (ch : Chan) (b : Nat) (at_ : world.chans[id]? = some ch)
      (placed : cp id = some b) : b ∈ chs := by
    rw [← counts.opened.unique heap.channels]
    exact List.mem_filterMap.mpr ⟨id, List.mem_reverse.mpr (List.mem_range.mpr
      (List.getElem?_eq_some_iff.mp at_).1), placed⟩
  have fixed (b off n : Nat) (mem : b ∈ chs) (lo : 32 ≤ off) (hi : off + n ≤ 72) :
      bytesT d.σ.mem (b + off) n = bytesT c.σ.mem (b + off) n := by
    apply Reloc.bytesT_congr
    intro j hj
    have apart : b = a ∨ b + Gc.chanRecordBytes ≤ a ∨ a + Gc.chanRecordBytes ≤ b := by
      by_cases eq : b = a
      · exact Or.inl eq
      · exact Or.inr (heap.recordsDisjoint b mem a target eq)
    have same := frame (b + off + j) (console_fixed_out (bounds b mem).1 (bounds b mem).2 apart native
      (by omega) (by omega))
    simp only [bytesT, same]
  have static (addr n : Nat) (low : addr + n ≤ Vsa.Sim.DlHeap.heapStart)
      (errno : addr + n ≤ Layout.sym_errno ∨ Layout.sym_errno + 4 ≤ addr)
      (impure : addr + n ≤ Layout.sym_impure_data ∨ Layout.sym_impure_data + 4 ≤ addr) :
      bytesT d.σ.mem addr n = bytesT c.σ.mem addr n := by
    apply Reloc.bytesT_congr
    intro j hj
    have same := frame (addr + j) (console_static_out targetLow native (by omega) (by omega) (by omega))
    simp only [bytesT, same]
  apply ChannelCountFrame.of_observations
  · constructor
    intro n physical
    simpa only [Nat.add_zero] using custom.accounting.frame physical (fun x hx => by
      have apart := custom.apart c x hx
      have recordApart := heap.custom_apart_record (custom.footprint c x hx) target
      have stat := apart.static
      have out : OutW (consoleWindows sp a) x := by
        apply Gc.outW_of
        intro w hw
        simp only [consoleWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
        have below := apart.belowStack
        have statBound : x < Vsa.Sim.DlHeap.heapStart →
            Layout.sym_caml_extra_heap_resources ≤ x ∧ x < Layout.sym_caml_extra_heap_resources + 8 := stat
        simp only [Gc.chanRecordBytes, chanOffBuff, ioBufferSize, nativeHeadroom,
          Vsa.Sim.DlHeap.heapEnd, Vsa.Sim.DlHeap.heapStart] at *
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Layout.sym_errno, Layout.sym_impure_data, Layout.sym_caml_extra_heap_resources] at * <;>
          (try dsimp only) <;> omega
      exact frame x out)
      (static Layout.sym_Caml_state 8 (by decide) (by decide) (by decide))
  · intro id ch b at_ placed
    exact fixed b chanOffRefcount 4 (member id ch b at_ placed) (by decide) (by decide)
  · constructor
    · exact static Layout.sym_caml_all_opened_channels 8 (by decide) (by decide) (by decide)
    · intro b mem
      rw [counts.opened.unique heap.channels] at mem
      exact fixed b Gc.chanOffNext 8 mem (by decide) (by decide)

/-- ConsoleStable at the local counted layout, with no stronger global
runtime premise and no restriction on mutable channel data. -/
theorem counted_console_stable {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp0 : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    ConsoleStable (countedLayout Gc.f1Layout Customs cp0 world) := by
  intro P s c pl cp high id ch a sp geometry runtime at_ placed low highSp d frame
  obtain ⟨chs, list, places, _⟩ := geometry.nursery.channelsListed_mem
  have opened : Gc.OpenAt c a := ⟨chs, list, places id ch a at_ placed⟩
  exact ⟨f1_console_stable P s c pl cp high id ch a sp (geometry.retarget rfl)
    runtime.1 at_ placed low highSp d frame,
    (f1_console_channelCountFrame custom runtime.1 runtime.2 opened low frame).repr runtime.2⟩

end OCaml.Vm.Sim
