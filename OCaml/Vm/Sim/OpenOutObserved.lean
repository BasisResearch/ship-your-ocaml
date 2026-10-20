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
    (custom : Gc.CustomMemCall Ready state)
    (o : OpenedOut live Ready state k H cap' charge sp ra s0 s1 s2 v head c d)
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

end OCaml.Vm.Sim
