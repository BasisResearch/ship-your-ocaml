import OCaml.Vm.Sim.CountedInvariant
import OCaml.Vm.Sim.ChannelCountFrame
import OCaml.RefinementF1
import OCaml.Vm.Sim.F1Frame
import OCaml.Vm.Sim.F1RaiseRuntime

/-! Reuse generic rows under a local runtime invariant. Channel calls change
the frozen world and use their counted machine summaries instead. Ordinary
rows still need actual frame instances for the effects they perform. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

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

/-- Stack-only caller effects: VM windows and native stack windows above
newlib's arena. Allocation and barrier windows are deliberately absent. -/
def CountStackWindow (w : Vsa.Sim.W) : Prop :=
  VmWindow Gc.f1High Gc.f1Domain w ∨ Vsa.Sim.DlHeap.heapEnd ≤ w.lo

/-- Caller windows start beyond the observed static words. -/
theorem CountStackWindow.above_statics {w : Vsa.Sim.W} (allowed : CountStackWindow w) :
    Layout.sym_bss_end ≤ w.lo := by
  rcases allowed with (⟨low, high⟩ | ⟨off, member, rfl⟩) | native
  · have bound : Layout.sym_bss_end ≤ Gc.f1High - Layout.stackBytes := by decide
    omega
  · have bound : Layout.sym_bss_end ≤ Gc.f1Domain := by decide
    dsimp only
    omega
  · have bound : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
    omega

/-- The named physical custom state misses VM and native stack stores.
The domain exception is only the existing resource word, which none of the
four VM field windows writes. -/
theorem CountStackWindow.custom_outside {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c : Config} {a : Nat} {w : Vsa.Sim.W}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Layout.runtimeOk c)
    (ha : state c a) (allowed : CountStackWindow w) : a < w.lo ∨ w.hi ≤ a := by
  have apart := custom.apart c a ha
  rcases allowed with (⟨low, high⟩ | ⟨off, member, rfl⟩) | native
  · have outside := apart.covered
      (Gc.f1High - Layout.stackBytes, Layout.stackBytes)
      (by simp only [Gc.f1Covered, Gc.f1High]; simp) (by decide)
    simp only [VsaIris.InExt] at outside
    omega
  · have domain := apart.domainField
    simp only [Gc.domainAddr, Gc.f1_domain runtime] at domain
    have offsets : ∀ off ∈ vmDomainOffsets,
        off + 8 ≤ Layout.domainStateBytes ∧
        (off + 8 ≤ Layout.off_extra_heap_resources_minor ∨
          Layout.off_extra_heap_resources_minor + 8 ≤ off) := by decide
    have fields := offsets off member
    simp only [VsaIris.InExt] at domain
    dsimp only
    omega
  · have below := apart.belowStack
    omega

/-- The selected physical ledger frames all channel words. Window suppliers
provide static, live-block and custom-state separation independently. -/
theorem f1_channelCountFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    {c d : Config} {ws : List Vsa.Sim.W}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Layout.runtimeOk c)
    (counts : ChannelCustomsRepr Customs c cp world)
    (above : ∀ w ∈ ws, Layout.sym_bss_end ≤ w.lo)
    (safe : ∀ w ∈ ws, Gc.F1HeapSafe w)
    (outside : ∀ w ∈ ws, ∀ a, state c a → a < w.lo ∨ w.hi ≤ a)
    (frame : Vsa.Sim.FrameOn ws c.σ.mem d.σ.mem) :
    ChannelCountFrame Customs cp world c d := by
  have statics (a n : Nat) (bound : a + n ≤ Layout.sym_bss_end) :
      bytesT d.σ.mem a n = bytesT c.σ.mem a n := by
    apply Reloc.bytesT_congr
    intro j hj
    have same := frame (a + j) (Gc.outW_of fun w hw =>
      Or.inl (by have := above w hw; omega))
    simp only [bytesT, same]
  apply ChannelCountFrame.of_frame frame
  · obtain ⟨H, cap, chs, heap⟩ := runtime.freeListShape.libHeap
    have same := counts.opened.unique heap.channels
    intro id ch a at_ placed y lo hi
    have member : a ∈ Gc.placedChannels cp world.chans.length := by
      apply List.mem_filterMap.mpr
      exact ⟨id, List.mem_reverse.mpr (List.mem_range.mpr
        (List.getElem?_eq_some_iff.mp at_).1), placed⟩
    rw [same] at member
    apply Gc.outW_of
    intro w hw
    exact (safe w hw).outside heap member lo
      (by simpa only [Gc.chanRecordBytes, Nat.add_assoc] using hi)
  · intro y lo hi
    exact Gc.outW_of fun w hw => Or.inl (by
      have := above w hw
      have b : Layout.sym_caml_all_opened_channels + 8 ≤ Layout.sym_bss_end := by decide
      omega)
  · constructor
    intro n physical
    simpa only [Nat.add_zero] using custom.accounting.frame physical
      (fun a ha => congrArg (fun x => x.getD 0)
        (frame a (Gc.outW_of fun w hw => outside w hw a ha)))
      (statics _ 8 (by decide))

/-- Complete counts survive VM/native stack and allowed domain-field writes.
All separation comes from the entry runtime and named custom allocator. -/
theorem f1_stack_channelCountFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    {c d : Config} {ws : List Vsa.Sim.W}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Layout.runtimeOk c)
    (counts : ChannelCustomsRepr Customs c cp world)
    (allowed : ∀ w ∈ ws, CountStackWindow w)
    (frame : Vsa.Sim.FrameOn ws c.σ.mem d.σ.mem) :
    ChannelCountFrame Customs cp world c d :=
  f1_channelCountFrame custom runtime counts
    (fun w hw => (allowed w hw).above_statics)
    (fun w hw => by
      rcases allowed w hw with vm | native
      · exact f1_vmWindow_heapSafe vm
      · exact Gc.heapSafe_native native)
    (fun w hw a ha => (allowed w hw).custom_outside custom runtime ha) frame

/-- All RuntimeFrame fields lift at the actual pinned F1 runtime. No stronger
WindowStable premise or global runtime coherence is assumed. -/
theorem counted_runtimeFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {w : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    RuntimeFrame (countedLayout Gc.f1Layout Customs cp w) Gc.f1High Gc.f1Domain where
  domainWord c h := f1_runtimeFrame.domainWord c h.1
  stackHigh c h := f1_runtimeFrame.stackHigh c h.1
  windows ws vm c d frame before :=
    ⟨f1_runtimeFrame.windows ws vm c d frame before.1,
      (f1_stack_channelCountFrame custom before.1 before.2
        (fun w hw => Or.inl (vm w hw)) frame).repr before.2⟩
  threshold c h := f1_runtimeFrame.threshold c h.1
  quiet c h := f1_runtimeFrame.quiet c h.1
  barrier c h := f1_runtimeFrame.barrier c h.1
  backtrace c h := f1_runtimeFrame.backtrace c h.1

/-- Native caught division raises use the already proved VM/native stack
count frame. The scratch bound comes from the real invocation's headroom. -/
theorem counted_raiseRuntimeFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {w : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    RaiseRuntimeFrame (countedLayout Gc.f1Layout Customs cp w) Gc.f1High Gc.f1Domain where
  hook c h := f1_raiseRuntimeFrame.hook c h.1
  scratch ws D valid each c d frame before :=
    ⟨f1_raiseRuntimeFrame.scratch ws D valid each c d frame before.1,
      (f1_stack_channelCountFrame custom before.1 before.2 (fun window member => by
        rcases each window member with vm | rfl
        · exact Or.inl vm
        · exact Or.inr (Nat.le_sub_of_add_le valid.headroom)) frame).repr before.2⟩

/-- Shared application operation for APPLY, tail calls and RETURN. -/
theorem counted_enter_channels {s s' : St} {stack : List Val} {extra : Nat}
    (effect : enter s stack extra = .next s') : s'.world.chans = s.world.chans := by
  simp only [enter, opt] at effect
  repeat' split at effect
  all_goals cases effect <;> rfl

/-- Caught and uncaught semantic raises retain the channel model. Reachable
F1 rows still discharge caughtness using their existing GoodF1 supplier. -/
theorem counted_raiseTo_channels {P : Prog} {s s' : St} {v : Val}
    (effect : raiseTo P s v = .next s') : s'.world.chans = s.world.chans := by
  simp only [raiseTo] at effect
  repeat' split at effect
  all_goals cases effect <;> rfl

/-- Tagged binary arithmetic does not change channels. -/
theorem counted_intOp_channels {s s' : St} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (effect : intOp s f = .next s') : s'.world.chans = s.world.chans := by
  simp only [intOp, opt] at effect
  repeat' split at effect
  all_goals cases effect <;> rfl

/-- Shared comparison operation. -/
theorem counted_cmpOp_channels {s s' : St} {f : BitVec 64 → BitVec 64 → Bool}
    (effect : cmpOp s f = .next s') : s'.world.chans = s.world.chans := by
  simp only [cmpOp, opt] at effect
  repeat' split at effect
  all_goals cases effect <;> rfl

/-- Shared immediate branch operation. -/
theorem counted_brOp_channels {s s' : St} {n ofs : Int} {f : BitVec 64 → BitVec 64 → Bool}
    (effect : brOp s n ofs f = .next s') : s'.world.chans = s.world.chans := by
  simp only [brOp, opt] at effect
  repeat' split at effect
  all_goals cases effect <;> rfl

/-- Reuse a generic row at the local counted runtime. Its actual runtime
frame supplies the count observations; linked-list coherence recovers them
at the ordinary producer's selected stack placement. No preservation
supplier is added to the headline. -/
theorem counted_row {L : OCaml.Layout} {P : Prog} {op : Opcode}
    {Customs : Config → Nat → Prop}
    (row : ∀ cp world, OCaml.OpArm P (OCaml.LoopAt (countedLayout L Customs cp world) P) op)
    (channels : ∀ (s : St) (i : Instr) (s' : St),
      i.op = op → stepI P s i = .next s' → s'.world.chans = s.world.chans) :
    OCaml.OpArm P (CountedLoopAt Customs L P) op := by
  intro s c i reach h decoded opcode fragment
  obtain ⟨pl, cp, sp, high, repr, geometry⟩ := h.running.countedStack
  let L' := countedLayout L Customs cp s.world
  have running : OCaml.Running L' P s c :=
    h.running.toRunning.retarget ⟨h.running.platform.runtime, repr.counts⟩ rfl
  have outcome := row cp s.world
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

/-- Memory-only specialization of the shared row adapter. -/
theorem counted_memory_row {L : OCaml.Layout} {P : Prog} {op : Opcode}
    {Customs : Config → Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (stable : MemoryStable L.runtimeOk) (accounting : Gc.CustomAccounting Ready state Customs)
    (row : ∀ L' : OCaml.Layout, MemoryStable L'.runtimeOk → OCaml.OpArm P (OCaml.LoopAt L' P) op)
    (channels : ∀ (s : St) (i : Instr) (s' : St),
      i.op = op → stepI P s i = .next s' → s'.world.chans = s.world.chans) :
    OCaml.OpArm P (CountedLoopAt Customs L P) op :=
  counted_row (fun _ _ => row _ (counted_memoryStable stable accounting)) channels

/-- Stack-writing specialization. Every runtime premise is produced by the
entry runtime and named custom accounting, before applying the generic row. -/
theorem counted_stack_row {P : Prog} {op : Opcode}
    {Customs : Config → Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (row : ∀ L' : OCaml.Layout, RuntimeFrame L' Gc.f1High Gc.f1Domain →
      MemoryStable L'.runtimeOk → OCaml.OpArm P (OCaml.LoopAt L' P) op)
    (channels : ∀ (s : St) (i : Instr) (s' : St),
      i.op = op → stepI P s i = .next s' → s'.world.chans = s.world.chans) :
    OCaml.OpArm P (CountedLoopAt Customs Gc.f1Layout P) op :=
  counted_row (fun _ _ => row _ (counted_runtimeFrame custom)
    (counted_memoryStable f1_memoryStable custom.accounting)) channels

end OCaml.Vm.Sim
