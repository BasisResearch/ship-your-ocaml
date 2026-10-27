import OCaml.Vm.Sim.OpenOutFrame
import OCaml.Vm.Sim.PayloadObserved
import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Sim.InvariantUse

/-!
# `caml_ml_open_descriptor_out` keeps what the payload reads

Every `PayloadObserved` byte of the entry lies in a region F1 covers (code,
VM stack, heap objects in the minor heap or the major chunk), in an open
record outside its link words, in a `Caml_state` field the payload reads, or
in a static word; `OpenOutFrame`'s lemmas keep each.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
variable {Customs : Vsa.Machine.Config → Nat → Prop}
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel

theorem payloadStatics_open : ∀ a ∈ payloadStatics, a ∈ openStatics := by decide

/-- A byte apart from the minor heap misses the custom block. -/
theorem block_of_outside_minor {c : Config} {x : Nat}
    (low : Gc.minorRegion.lo + 24 ≤ (runtimeFields c).youngPtr) (high : (runtimeFields c).youngPtr ≤ Gc.minorRegion.hi)
    (out : x < Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ x) :
    x + 24 < (runtimeFields c).youngPtr ∨ (runtimeFields c).youngPtr ≤ x := by omega

/-- The code buffer at an F1 entry is the cut's. -/
theorem codeBase_eq {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {spV high : Nat}
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) :
    pl.codeBase = Boot.WhileMinHeapChunks.codeBufferPayload := by
  rw [← data.codeBase, pins.codeWord]; rfl

/-- The atom table at an F1 entry is the cut's. -/
theorem atomBase_eq {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {spV high : Nat}
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) : pl.atomBase = Gc.atomTableAddr := by
  rw [← data.atomBase, pins.atomsWord]; rfl

/-- The VM stack at an F1 entry ends at the cut's `stack_high`. -/
theorem high_eq {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {spV high : Nat}
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high)
    (domain : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain) :
    high = Boot.WhileMinEntry.high := by
  have e := data.stackHigh
  rw [domain, show Boot.WhileMinRuntime.domain = Gc.f1Domain from rfl, pins.stackHigh] at e
  rw [← e]; rfl

/-- **Every byte the entry's payload reads is kept** across the primitive. -/
theorem open_out_observed {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {spV high : Nat}
    {live : Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {H : List (Nat × Nat)} {cap cap' charge : Nat} {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
    (custom : Gc.CustomMemCall Ready state Customs)
    {code : Channel.OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra s0 s1 s2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput live H cap' charge sp ra s0 s1 s2 v head c)
    (N : OutNursery H (Gc.placedChannels cp s.world.chans.length) c)
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) (g : OCaml.LoopGeometry L P s c pl cp high)
    (fits : 8 * s.stack.length ≤ Layout.stackBytes) :
    ∀ x, PayloadObserved P s c pl cp spV x → byte d x = byte c x := by
  intro x obs
  rw [byte_total, byte_total]
  have low := N.low
  have hi := N.high
  have room := N.room
  have nonMinor : ∀ e ∈ Gc.f1Covered, e.1 ≠ Gc.minorRegion.lo → VsaIris.InExt e x →
      x + 24 < (runtimeFields c).youngPtr ∨ (runtimeFields c).youngPtr ≤ x := fun e he ne ix => by
    have m := Channel.f1Covered_minor e he ne
    obtain ⟨xl, xh⟩ := ix
    exact block_of_outside_minor low hi (by omega)
  cases obs with
  | @static a _ mem hx =>
    obtain ⟨lo, hi'⟩ := hx
    have e := static_kept custom o h N (payloadStatics_open a mem) (j := x - a) (by omega)
    rwa [Nat.add_sub_cancel' lo] at e
  | @domainField off _ mem hx =>
    obtain ⟨lo, hi'⟩ := hx
    rw [h.domain] at lo hi'
    have facts : off + 8 ≤ Layout.domainStateBytes ∧ Layout.off_young_ptr + 8 ≤ off ∧
        (off + 8 ≤ Layout.off_extra_heap_resources_minor ∨ Layout.off_extra_heap_resources_minor + 8 ≤ off) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> decide
    exact domainField_kept custom o h N facts.1 facts.2.1 facts.2.2 lo hi'
  | @code i w _ found hx =>
    obtain ⟨lo, hi'⟩ := hx
    have base := codeBase_eq pins data
    have size : i < P.code.size := (Array.getElem?_eq_some_iff.mp found).1
    have codeFits := g.nursery.codeFits
    have he : (Boot.WhileMinHeapChunks.codeBufferPayload, Gc.f1CodeBytes) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
    have ix : VsaIris.InExt (Boot.WhileMinHeapChunks.codeBufferPayload, Gc.f1CodeBytes) x := by
      rw [base] at lo hi'; constructor <;> dsimp only <;> omega
    exact covered_kept custom o heap h he (by decide) ix (nonMinor _ he (by decide) ix)
  | @stack i val _ found hx =>
    obtain ⟨lo, hi'⟩ := hx
    have top := high_eq pins data h.domain
    have len : i < s.stack.length := (List.getElem?_eq_some_iff.mp found).1
    have span := data.stack.1
    have space := stack_space data.stack fits
    have he : (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes) ∈ Gc.f1Covered := by
      simp [Gc.f1Covered]
    have below : Layout.stackBytes ≤ Boot.WhileMinEntry.high := by decide
    have ix : VsaIris.InExt (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes) x := by
      rw [top] at span space; constructor <;> dsimp only <;> omega
    exact covered_kept custom o heap h he (by decide) ix (nonMinor _ he (by decide) ix)
  | @header l a ob _ found placed hx =>
    obtain ⟨lo, hi'⟩ := hx
    have chunks := g.nursery.heapChunks l a ob placed found
    have free := g.nursery.heap l a ob placed found
    simp only [OutWRange, Gc.nurseryFree, and_true] at free
    rcases chunks with ⟨cl, ch⟩ | ⟨cl, ch⟩
    · have he : (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
      exact covered_kept custom o heap h he (by decide) ⟨by dsimp only; omega, by dsimp only; omega⟩ (by omega)
    · have he : (Gc.majorRegion.lo, Gc.majorRegion.hi - Gc.majorRegion.lo) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
      have ix : VsaIris.InExt (Gc.majorRegion.lo, Gc.majorRegion.hi - Gc.majorRegion.lo) x := by
        simp only [Gc.majorRegion] at cl ch ⊢; constructor <;> dsimp only <;> omega
      exact covered_kept custom o heap h he (by decide) ix (nonMinor _ he (by decide) ix)
  | @fields l a ob _ found placed hx =>
    obtain ⟨lo, hi'⟩ := hx
    have chunks := g.nursery.heapChunks l a ob placed found
    have free := g.nursery.heap l a ob placed found
    have low8 := g.toStackGeometry.heapLow l a ob placed found
    simp only [OutWRange, Gc.nurseryFree, and_true] at free
    rcases chunks with ⟨cl, ch⟩ | ⟨cl, ch⟩
    · have he : (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
      exact covered_kept custom o heap h he (by decide) ⟨by dsimp only; omega, by dsimp only; omega⟩ (by omega)
    · have he : (Gc.majorRegion.lo, Gc.majorRegion.hi - Gc.majorRegion.lo) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
      have ix : VsaIris.InExt (Gc.majorRegion.lo, Gc.majorRegion.hi - Gc.majorRegion.lo) x := by
        simp only [Gc.majorRegion] at cl ch ⊢; constructor <;> dsimp only <;> omega
      exact covered_kept custom o heap h he (by decide) ix (nonMinor _ he (by decide) ix)
  | @chanFront id ch a _ found placed hx =>
    obtain ⟨lo, hi'⟩ := hx
    have mem : a ∈ Gc.placedChannels cp s.world.chans.length :=
      Gc.mem_placedChannels.2 ⟨id, (List.getElem?_eq_some_iff.mp found).1, placed⟩
    have big : 48 ≤ chanOffBuff + ioBufferSize := by decide
    exact record_kept custom o heap h N mem lo (by unfold Gc.chanRecordBytes; omega) (fun _ => Or.inl (by omega))
  | @chanBack id ch a _ found placed hx =>
    obtain ⟨lo, hi'⟩ := hx
    have mem : a ∈ Gc.placedChannels cp s.world.chans.length :=
      Gc.mem_placedChannels.2 ⟨id, (List.getElem?_eq_some_iff.mp found).1, placed⟩
    have big : 64 ≤ chanOffBuff + ioBufferSize := by decide
    exact record_kept custom o heap h N mem (by omega) (by unfold Gc.chanRecordBytes; omega) (fun _ => Or.inr lo)
  | named f =>
    obtain ⟨chains, table⟩ := data.named
    exact named_kept custom o heap h N ⟨pl, s.world.named, chains, table, f⟩

section More

variable {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {spV high : Nat}
  {live : Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
  {H : List (Nat × Nat)} {cap cap' charge : Nat} {sp ra r0 r1 r2 v head : BitVec 64} {c d : Config}

/-- **A VM stack byte is kept.** -/
theorem vmStack_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : Channel.OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra r0 r1 r2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput live H cap' charge sp ra r0 r1 r2 v head c)
    (N : OutNursery H (Gc.placedChannels cp s.world.chans.length) c)
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) {x : Nat}
    (lo : high - Layout.stackBytes ≤ x) (hi : x < high) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  have top := high_eq pins data h.domain
  have he : (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes) ∈ Gc.f1Covered := by
    simp [Gc.f1Covered]
  have below : Layout.stackBytes ≤ Boot.WhileMinEntry.high := by decide
  have ix : VsaIris.InExt (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes) x := by
    rw [top] at lo hi; constructor <;> dsimp only <;> omega
  have m := Channel.f1Covered_minor _ he (by decide)
  exact covered_kept custom o heap h he (by decide) ix
    (block_of_outside_minor N.low N.high (by obtain ⟨xl, xh⟩ := ix; dsimp only at m xl xh; omega))

/-- **A primitive-table byte is kept.** -/
theorem primTable_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : Channel.OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra r0 r1 r2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput live H cap' charge sp ra r0 r1 r2 v head c)
    (N : OutNursery H (Gc.placedChannels cp s.world.chans.length) c) {x : Nat}
    (lo : Boot.WhileMinHeapChunks.primTablePayload ≤ x)
    (hi : x < Boot.WhileMinHeapChunks.primTablePayload + 8 * Gc.f1PrimCapacity) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  have he : (Boot.WhileMinHeapChunks.primTablePayload, 8 * Gc.f1PrimCapacity) ∈ Gc.f1Covered := by
    simp [Gc.f1Covered]
  have m := Channel.f1Covered_minor _ he (by decide)
  exact covered_kept custom o heap h he (by decide) ⟨lo, hi⟩
    (block_of_outside_minor N.low N.high (by dsimp only at m; omega))

/-- **A byte at or above the C call's native stack pointer is kept** (the
interpreter's frames). -/
theorem native_kept (custom : Gc.CustomMemCall Ready state Customs)
    {code : Channel.OpenCode} (o : OpenedOut code live Ready state Customs k H cap' charge sp ra r0 r1 r2 v head c d)
    (h : OutInput live H cap' charge sp ra r0 r1 r2 v head c)
    (N : OutNursery H (Gc.placedChannels cp s.world.chans.length) c) {x : Nat}
    (above : sp.toNat ≤ x) :
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
  have lower := h.frame.lower
  have lowM := N.low
  have highM := N.high
  have hSE : Vsa.Sim.DlHeap.heapStart ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have hM : Gc.minorRegion.hi ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have hD : Boot.WhileMinRuntime.domain + Layout.off_young_ptr + 8 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have far : Vsa.Sim.DlHeap.heapEnd ≤ x := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans lower above)
  refine o.kept x (fun st => by have := (custom.apart c x st).belowStack; omega) ?_ ?_ (Or.inr above)
    (Or.inr (by omega)) (Or.inr (by unfold Gc.domainAddr; rw [h.domain]; exact Nat.le_trans hD far))
  · rintro (g | ⟨_, l, _⟩)
    · rcases VsaIris.VsaHeap.allocGlobal_off_arena _ g with y | y
      · omega
      · unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange at g; unfold Vsa.Sim.DlHeap.heapEnd at y; omega
    · omega
  · have pHigh := o.opening.high
    unfold recordBytes at pHigh
    have hSt : 0x80064d4c ≤ Vsa.Sim.DlHeap.heapEnd := by decide
    have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
      have e := outFrame_slot (h.frame.resize (small := 16) (by decide) (by decide)) (off := 0) (by decide)
      rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e; rw [e]; omega
    apply OCaml.Vm.Gc.outW_all
    intro w hw
    unfold openWindows at hw
    rcases List.mem_append.mp hw with hw | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · right; dsimp only; rw [sp16]; omega
      all_goals (right; dsimp only; try unfold recordBytes
                 omega)
    · by_cases hz : head = 0#64
      · simp [hz] at hw
      · simp only [hz, ite_false, List.mem_singleton] at hw
        subst hw
        obtain ⟨⟨e, he, _, hi'⟩, _⟩ := h.headLive hz
        have bounds := h.ready.heap.block_bounds (q := e.1) (n := e.2) he
        right; dsimp only; omega

end More

end OCaml.Vm.Sim
