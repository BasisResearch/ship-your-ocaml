import OCaml.Vm.Sim.CountedRuntime
import OCaml.Vm.Sim.F1GrowthPaths

/-! Actual counted barrier effects. RefCustomApart comes from the selected
LibHeapAt custom-space invariant. Full-table
collection requires BarrierGrowthFull at the local counted layout itself;
the base-layout obligation does not imply that stronger instantiation. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Insertion frames use the real struct/entry windows and the selected
ledger's custom-space evidence. -/
theorem f1_insert_channelCountFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c d : Config} {cp : ChanPlace} {world : World}
    {tbl ptr limit slot : BitVec 64}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Runtime c)
    (counts : ChannelCustomsRepr Customs c cp world)
    (table : Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem)
    (room : ptr.toNat < limit.toNat)
    (memory : d.σ.mem = writeLog c.σ.mem (Gc.Barrier.insertLog tbl ptr slot)) :
    ChannelCountFrame Customs cp world c d := by
  obtain ⟨rfl, rfl, rfl⟩ := Gc.f1_table_eq runtime table
  obtain ⟨H, cap, chs, heap⟩ := runtime.freeListShape.libHeap
  let ws := Gc.insertWindows (word c (Gc.refTable + Layout.off_ref_table_ptr)).toNat
  have inside : LogInW ws (Gc.Barrier.insertLog (BitVec.ofNat 64 Gc.refTable)
      (word c (Gc.refTable + Layout.off_ref_table_ptr)) slot) := by
    apply log_in_windows_of_mem
    intro e he
    simp only [Gc.Barrier.insertLog, BitVec.add_zero, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact insideW_of_mem (List.mem_cons_self ..) (Nat.le_refl _) (Nat.le_refl _)
    · exact insideW_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (Nat.le_refl _) (Nat.le_refl _)
  have frame : FrameOn ws c.σ.mem d.σ.mem := by
    rw [memory]; exact frameOn_writeLog _ _ _ inside
  have windows := heap.insert_outside room
  have selected := counts.opened.unique heap.channels
  have statics (a n : Nat) (bound : a + n ≤ Layout.sym_bss_end) :
      bytesT d.σ.mem a n = bytesT c.σ.mem a n := by
    apply Reloc.bytesT_congr
    intro j hj
    have same := frame (a + j) (Gc.outW_of fun w hw =>
      Or.inl (by have := (windows w hw).1; omega))
    simp only [bytesT, same]
  apply ChannelCountFrame.of_frame frame
  · intro id ch r at_ placed y lo hi
    have member : r ∈ Gc.placedChannels cp world.chans.length :=
      List.mem_filterMap.mpr ⟨id, List.mem_reverse.mpr (List.mem_range.mpr
        (List.getElem?_eq_some_iff.mp at_).1), placed⟩
    rw [selected] at member
    apply Gc.outW_of
    intro w hw
    have sep := (windows w hw).2 r member
    simp only [Gc.chanRecordBytes] at sep
    omega
  · intro y lo hi
    exact Gc.outW_of fun w hw => Or.inl (by
      have := (windows w hw).1
      have : Layout.sym_caml_all_opened_channels + 8 ≤ Layout.sym_bss_end := by decide
      omega)
  · constructor
    intro n physical
    simpa only [Nat.add_zero] using custom.accounting.frame physical (fun x hx => by
      have out : OutW ws x := by
        apply Gc.outW_of
        intro w hw
        simp only [ws, Gc.insertWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have sep := (custom.apart c x hx).covered (Gc.refTable, 56) (by decide) (by decide)
          by_cases low : x < Gc.refTable + Layout.off_ref_table_ptr
          · exact Or.inl low
          · right
            apply Classical.byContradiction
            intro no
            apply sep
            constructor <;> dsimp only at * <;>
              simp only [Layout.off_ref_table_ptr] at * <;> omega
        · exact heap.refCustomApart.entry_outside heap room (custom.footprint c x hx)
      exact congrArg (fun v => v.getD 0) (frame x out))
      (statics _ 8 (by decide))

/-- Local counted BarrierRuntime from actual selected spatial evidence.
Table windows are transported with identical geometry. -/
theorem counted_barrierRuntime {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    BarrierRuntime (countedLayout Gc.f1Layout Customs cp world) where
  idle c before := f1_barrierRuntime.idle c before.1
  table c before := by
    obtain ⟨tbl, ptr, limit, table, arena, separated⟩ := Gc.f1_tableRuntime before.1
    exact ⟨tbl, ptr, limit, table, arena, fun P s pl cp0 high geometry =>
      separated P s pl cp0 high (geometry.retarget rfl)⟩
  insert c tbl ptr limit slot before table room after memory young :=
    ⟨Gc.f1_insert c tbl ptr limit slot before.1 table room after memory young.1,
      (f1_insert_channelCountFrame custom before.1 before.2
        table room memory).repr before.2⟩

/-- The real unallocated growth return keeps all count components. Refcount
and link words are live record bytes in the entry's selected ledger; physical
state uses CustomMemCall.owned and GrowDone.kept. -/
theorem f1_grow_channelCountFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c d : Config} {cp : ChanPlace} {world : World}
    {H : List (Nat × Nat)} {cap capacity : Nat} {chs : List Nat} {slot value ra sp : BitVec 64}
    (custom : Gc.CustomMemCall Ready state Customs) (heap : Gc.LibHeapAt H cap chs c)
    (counts : ChannelCustomsRepr Customs c cp world)
    (done : Gc.Barrier.GrowDone imageLive H capacity slot value ra sp
      (BitVec.ofNat 64 Gc.refTable) 0x40000#64 c d)
    (chunks : Gc.InHeapChunks (slot + BitVec.ofNat 64 0).toNat 8) :
    ChannelCountFrame Customs cp world c d := by
  have record (r : Nat) (member : r ∈ chs) (off n : Nat)
      (bound : off + n ≤ Gc.chanRecordBytes) :
      bytesT d.σ.mem (r + off) n = bytesT c.σ.mem (r + off) n := by
    have tableApart := heap.recordsApart r member (Gc.refTable, 56) (by decide)
    have minor := heap.recordsApart r member (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo) (by decide)
    have major := heap.recordsApart r member (Gc.majorRegion.lo, Gc.majorRegion.hi - Gc.majorRegion.lo) (by decide)
    dsimp only at tableApart minor major
    apply Reloc.bytesT_congr
    intro j hj
    have kept := Gc.kept_covered (sp := sp) heap (heap.records r member)
      (a := r + off + j) (by omega) (by omega) (by omega)
    have outside : r + off + j < (slot + BitVec.ofNat 64 0).toNat ∨
        (slot + BitVec.ofNat 64 0).toNat + 8 ≤ r + off + j := by
      rcases chunks with ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
        simp only [Gc.minorRegion, Gc.majorRegion] at * <;> omega
    simp only [bytesT, done.kept _ kept outside]
  have member (id : Nat) (ch : Chan) (r : Nat)
      (at_ : world.chans[id]? = some ch) (placed : cp id = some r) : r ∈ chs := by
    rw [← counts.opened.unique heap.channels]
    exact List.mem_filterMap.mpr ⟨id, List.mem_reverse.mpr (List.mem_range.mpr
      (List.getElem?_eq_some_iff.mp at_).1), placed⟩
  refine ⟨Gc.f1_afterGrow_custom custom heap done chunks, ?_, ⟨?_, ?_⟩⟩
  · intro id ch r at_ placed
    exact congrArg BitVec.toNat (record r (member id ch r at_ placed) chanOffRefcount 4 (by decide))
  · apply Gc.grow_word done
    · intro j hj
      apply Gc.kept_static
      · simp only [Layout.sym_caml_all_opened_channels, Vsa.Sim.DlHeap.heapStart]; omega
      · unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange
        simp only [Layout.sym_caml_all_opened_channels]; omega
    · rcases chunks with ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
        simp only [Gc.minorRegion, Gc.majorRegion, Layout.sym_caml_all_opened_channels] at * <;> omega
  · intro r hr
    rw [counts.opened.unique heap.channels] at hr
    exact record r hr Gc.chanOffNext 8 (by decide)

/-- The counted runtime frame consumes the native allocator post directly. -/
theorem counted_growRuntime {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    BarrierGrowRuntime (countedLayout Gc.f1Layout Customs cp world) where
  afterGrow c d H cap chs slot value ra sp before heap unallocated done chunks slotPrivate0 := by
    change Gc.f1Runtime d ∧ ChannelCustomsRepr Customs d cp world
    constructor
    · exact Gc.f1_afterGrow before.1 heap unallocated done chunks slotPrivate0
    · exact (f1_grow_channelCountFrame custom heap before.2 done chunks).repr before.2

/-- The unallocated path is composed at countedLayout from its actual native
post. Its idle observation comes from the base runtime; insertion separation
is not required for this path. -/
theorem counted_barrierGrowth {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    BarrierGrowth (countedLayout Gc.f1Layout Customs cp world) :=
  barrierGrowth_of_runtime rfl (fun _ h => h.1) (fun c h => Gc.f1_gcIdle c h.1)
    (counted_growRuntime custom)

/-- Shared adapter for the six barrier opcodes. The full-table supplier is
G2 at each local counted layout, including physical accounting, references,
links and all ordinary native fields. Its base-layout instance is insufficient.
The insertion spatial supplier is derived from the actual selected heap. -/
theorem counted_barrier_row {P : Prog} {op : Opcode}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (full : ∀ cp world, BarrierGrowthFull (countedLayout Gc.f1Layout Customs cp world))
    (row : ∀ cp world,
      BarrierRuntime (countedLayout Gc.f1Layout Customs cp world) →
      BarrierGrowth (countedLayout Gc.f1Layout Customs cp world) →
      BarrierGrowthFull (countedLayout Gc.f1Layout Customs cp world) →
      RaiseRuntimeFrame (countedLayout Gc.f1Layout Customs cp world) Gc.f1High Gc.f1Domain →
      (∀ s c, (countedLayout Gc.f1Layout Customs cp world).runtimeOk c →
        8 * s.stack.length ≤ Layout.stackBytes →
        FieldWriteReady (countedLayout Gc.f1Layout Customs cp world) P s c) →
      MemoryStable (countedLayout Gc.f1Layout Customs cp world).runtimeOk →
      OCaml.OpArm P (OCaml.LoopAt (countedLayout Gc.f1Layout Customs cp world) P) op)
    (channels : ∀ (s : St) (i : Instr) (s' : St),
      i.op = op → stepI P s i = .next s' → s'.world.chans = s.world.chans) :
    OCaml.OpArm P (CountedLoopAt Customs Gc.f1Layout P) op :=
  counted_row (fun cp world => row cp world (counted_barrierRuntime custom)
    (counted_barrierGrowth custom) (full cp world)
    (counted_raiseRuntimeFrame custom) (fun _ _ => counted_fieldWriteReady custom)
    (counted_memoryStable f1_memoryStable custom.accounting)) channels

end OCaml.Vm.Sim
