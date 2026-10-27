import OCaml.Vm.Sim.CountedRuntime
import OCaml.Vm.Sim.PrimAllocFrame

/-! Counted frames for the existing G1 allocation contracts. The entry's
physical ledger supplies channel separation even when the local frozen
channel placement differs from the nursery geometry's placement. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The actual allocation effects: caller windows, free nursery, young pointer
and local roots. No allocator metadata, custom allocation or GC is admitted. -/
def CountAllocWindow (c : Config) (w : W) : Prop :=
  CountStackWindow w ∨
    ((runtimeFields c).youngLimit ≤ w.lo ∧ w.hi ≤ (runtimeFields c).youngPtr) ∨
    (Gc.domainAddr c Layout.off_young_ptr ≤ w.lo ∧ w.hi ≤ Gc.domainAddr c Layout.off_young_ptr + 8) ∨
    (Gc.domainAddr c Layout.off_local_roots ≤ w.lo ∧ w.hi ≤ Gc.domainAddr c Layout.off_local_roots + 8)

/-- All allocation windows miss static words. -/
theorem CountAllocWindow.above_statics {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {high : Nat} {w : W}
    (runtime : Gc.f1Layout.runtimeOk c) (g : Gc.NurseryGeometry P s c pl cp high)
    (allowed : CountAllocWindow c w) : Layout.sym_bss_end ≤ w.lo := by
  rcases allowed with stack | nursery | young | roots
  · exact stack.above_statics
  · have := g.statics; simp only [Gc.nurseryFree] at this; omega
  · have := Gc.f1_domain runtime
    simp only [Gc.domainAddr, this] at young
    have : Layout.sym_bss_end ≤ Gc.f1Domain := by decide
    omega
  · have := Gc.f1_domain runtime
    simp only [Gc.domainAddr, this] at roots
    have : Layout.sym_bss_end ≤ Gc.f1Domain := by decide
    omega

/-- Ownership separation follows from the real live-block ledger. -/
theorem CountAllocWindow.heapSafe {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {high : Nat} {w : W}
    (runtime : Gc.f1Layout.runtimeOk c) (g : Gc.NurseryGeometry P s c pl cp high)
    (allowed : CountAllocWindow c w) : Gc.F1HeapSafe w := by
  rcases allowed with (vm | native) | nursery | young | roots
  · exact f1_vmWindow_heapSafe vm
  · exact Gc.heapSafe_native native
  · have low := g.nurseryLow
    have high := g.nurseryHigh
    exact Gc.heapSafe_minor (by omega) (by omega)
  · have dom := Gc.f1_domain runtime
    simp only [Gc.domainAddr, dom] at young
    exact (young_sub_safe young.1 young.2).2
  · have dom := Gc.f1_domain runtime
    simp only [Gc.domainAddr, dom] at roots
    exact (roots_sub_safe roots.1 roots.2).2

/-- Custom-state separation uses the named allocator's actual footprint law. -/
theorem CountAllocWindow.custom_outside {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {high a : Nat} {w : W}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Layout.runtimeOk c)
    (g : Gc.NurseryGeometry P s c pl cp high) (ha : state c a)
    (allowed : CountAllocWindow c w) : a < w.lo ∨ w.hi ≤ a := by
  have apart := custom.apart c a ha
  rcases allowed with stack | nursery | young | roots
  · exact stack.custom_outside custom runtime ha
  · have low := g.nurseryLow
    have high := g.nurseryHigh
    rcases apart.minor with lo | hi <;> omega
  · rcases apart.youngPtr with lo | hi <;> omega
  · rcases apart.localRoots with lo | hi <;> omega

/-- A log of actual allocation entries frames all three count components.
The window list is reflected from the log; no post-runtime supplier is used. -/
theorem f1_alloc_channelCountFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp cp0 : ChanPlace} {world : World} {high : Nat} {log : List WEntry}
    (custom : Gc.CustomMemCall Ready state Customs) (runtime : Gc.f1Layout.runtimeOk c)
    (g : Gc.NurseryGeometry P s c pl cp0 high)
    (counts : ChannelCustomsRepr Customs c cp world)
    (entries : ∀ e ∈ log, CountAllocWindow c ⟨e.1, e.1 + e.2.1⟩)
    (observed : ∀ a : Nat, (d.σ.mem[a]?).getD 0 = ((writeLog c.σ.mem log)[a]?).getD 0) :
    ChannelCountFrame Customs cp world c d := by
  let ws : List W := log.map (fun e => ⟨e.1, e.1 + e.2.1⟩)
  have allowed : ∀ w ∈ ws, CountAllocWindow c w := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact entries e he
  let mid : Config := { c with σ := { c.σ with mem := writeLog c.σ.mem log } }
  have inside : LogInW ws log := log_in_windows_of_mem fun e he => by
    exact insideW_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩) (Nat.le_refl _) (Nat.le_refl _)
  have frame := f1_channelCountFrame (d := mid) custom runtime counts
    (fun w hw => (allowed w hw).above_statics runtime g)
    (fun w hw => (allowed w hw).heapSafe runtime g)
    (fun w hw a ha => (allowed w hw).custom_outside custom runtime g ha)
    (frameOn_writeLog ws c.σ.mem log inside)
  have same (a n : Nat) : bytesT d.σ.mem a n = bytesT mid.σ.mem a n :=
    Reloc.bytesT_congr fun j _ => by simp only [bytesT, observed]; rfl
  refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
  · constructor
    intro n physical
    have midPhysical := frame.physical.count physical
    simpa only [Nat.add_zero] using custom.accounting.frame midPhysical
      (fun a _ => observed a) (same Layout.sym_Caml_state 8)
  · intro id ch a at_ placed
    exact (congrArg BitVec.toNat (same (a + chanOffRefcount) 4)).trans
      (frame.references id ch a at_ placed)
  · exact (same Layout.sym_caml_all_opened_channels 8).trans frame.links.head
  · intro a ha
    exact (same (a + Gc.chanOffNext) 8).trans (frame.links.next a ha)

/-- The native allocating primitive contract lifted to countedLayout. -/
theorem counted_primAllocFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    PrimAllocFrame (countedLayout Gc.f1Layout Customs cp world) := by
  constructor
  intro P s c pl cp0 high log before g entries young after observed runtime
  refine ⟨f1_primAllocFrame.allocW P s c pl cp0 high log before.1 g entries young
    after observed runtime.1, ?_⟩
  apply ChannelCountFrame.repr (f1_alloc_channelCountFrame (log := log) custom before.1 g before.2 ?_ ?_) runtime.2
  · intro e he
    rcases entries e he with nursery | native | young | roots
    · exact Or.inr (Or.inl nursery)
    · exact Or.inl (Or.inr native)
    · exact Or.inr (Or.inr (Or.inl young))
    · exact Or.inr (Or.inr (Or.inr roots))
  · intro a
    have h := observed a
    simp only [byte, bytesT, BitVec.append] at h
    simpa using h

/-- The opcode allocation contract lifted from its real reservation/body log. -/
theorem counted_allocFrame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) :
    AllocFrame (countedLayout Gc.f1Layout Customs cp world) := by
  constructor
  intro P s c pl cp0 high a log before g inside low below aligned after memory runtime
  refine ⟨f1_allocFrame.allocW P s c pl cp0 high a log before.1 g inside low below aligned
    after memory runtime.1, ?_⟩
  apply ChannelCountFrame.repr (f1_alloc_channelCountFrame custom before.1 g before.2 ?_
    (fun x => by rw [memory])) runtime.2
  intro e he
  rcases List.mem_append.mp he with reserve | body
  · simp only [grabReserveLog, List.mem_singleton] at reserve
    subst e
    exact Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩))
  · have high : domainWord c Layout.off_stack_high = Gc.f1High :=
      f1_runtimeFrame.stackHigh c before.1
    rw [high] at inside
    rcases logInW_mem inside body with nursery | stack | empty
    · exact Or.inr (Or.inl nursery)
    · exact Or.inl (Or.inl (Or.inl stack))
    · exact False.elim empty

/-- Reuse allocating opcode rows after producing their complete local frames. -/
theorem counted_alloc_row {P : Prog} {op : Opcode}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (row : ∀ cp world,
      AllocFrame (countedLayout Gc.f1Layout Customs cp world) →
      RuntimeFrame (countedLayout Gc.f1Layout Customs cp world) Gc.f1High Gc.f1Domain →
      MemoryStable (countedLayout Gc.f1Layout Customs cp world).runtimeOk →
      OCaml.OpArm P (OCaml.LoopAt (countedLayout Gc.f1Layout Customs cp world) P) op)
    (channels : ∀ (s : St) (i : Instr) (s' : St),
      i.op = op → stepI P s i = .next s' → s'.world.chans = s.world.chans) :
    OCaml.OpArm P (CountedLoopAt Customs Gc.f1Layout P) op :=
  counted_row (fun cp world => row cp world (counted_allocFrame custom) (counted_runtimeFrame custom)
    (counted_memoryStable f1_memoryStable custom.accounting)) channels

end OCaml.Vm.Sim
