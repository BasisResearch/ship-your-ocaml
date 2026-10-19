import OCaml.Vm.Primitives.Uncaught.FormatFill
import OCaml.Vm.Boot.Startup.StatAllocReady
import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Boot.Startup.TableAllocatorInput
import OCaml.Vm.Boot.Startup.AllocatorImage
import OCaml.Vm.Gc.ReallocSuffix
import OCaml.Vm.Gc.ImageLibrary

/-!
# `caml_format_exception` on a constant exception: `caml_stat_alloc_noexc(len + 1)`

The allocation is a0-boot's `stat_alloc_ready` (dispatch, then the landed
malloc) under allocator readiness `RuntimeReadyL` over the image-only live set
`imageLive` (a6-gc's `LibraryLive` instance), the one the library leaves
(`memmove_leaf`, `strlen_ready`) keep.
`FormatHeap` is the entry's allocator fact; `ready_transport` carries it from
the entry to the call, since the front half writes only the native frame.
-/

namespace OCaml.Vm.Primitives.Uncaught.FormatException
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  VsaIris VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Inst

/-- A leaf caller with the library facts is a platform state of `imageLive`. -/
theorem _root_.OCaml.Vm.Primitives.LibraryReady.vsaOk {ra : BitVec 64} {c : Config} (r : LibraryReady c)
    (leaf : LeafInput ra c) : VsaOk imageLive c :=
  ⟨leaf.good, leaf.tick, r.gprs, imageLive_present leaf.image, r.htifIdle⟩

/-- Allocator readiness gives the library facts. -/
theorem _root_.OCaml.Vm.Boot.Startup.RuntimeReadyL.library {live : Nat → Prop} {H : List (Nat × Nat)}
    {capacity : Nat} {sp ra : BitVec 64} {c : Config} (r : RuntimeReadyL live H capacity sp ra c) : LibraryReady c :=
  ⟨r.platform.gpr, library_gpr r.platform (by decide) (by decide) (r.readOnly.1 (gp, gpV) (by simp [roR])),
    r.platform.htifIdle⟩

/-- **Readiness across a run that keeps the low memory and the allocator's
footprint**, landing at a leaf caller with the library facts. -/
theorem ready_transport {H : List (Nat × Nat)} {capacity : Nat} {sp ra oldsp oldra : BitVec 64} {before after : Config}
    (ready : RuntimeReadyL imageLive H capacity oldsp oldra before) (leaf : LeafInput ra after)
    (library : LibraryReady after)
    (low : ∀ a, a < heapStart → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (heap : ∀ a, vsaFoot H a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (stack : gprGet after.σ 2 = some sp) : RuntimeReadyL imageLive H capacity sp ra after := by
  refine ⟨leaf, library.vsaOk leaf, ⟨?_, ?_⟩, ?_, stack, ?_, ?_⟩
  · intro p hp
    simp only [roR, List.mem_singleton] at hp
    subst hp
    change vsaReg after 3 = gpV
    rw [vsaReg_gpr (by decide)]
    change (gpr after 3).getD 0 = gpV
    rw [library.gp]; rfl
  · intro p hp
    change (after.σ.mem[p.1]?).getD 0 = p.2
    rw [low p.1 (allocator_sources p hp).geometry.high]
    exact ready.readOnly.2 p hp
  · apply roomLocal_vsaRoomB H _ _ capacity ?_ ready.room
    intro a ha
    exact (heap a ha).symm
  · rw [word_observed (m := before.σ.mem) _ (fun i _ => low _ (by unfold heapStart Layout.sym_Caml_state; omega))]
    exact ready.domainWord
  · exact lpins8_observed ready.poolZero (fun i _ => low _ (by unfold heapStart Layout.sym_pool; omega))

/-- **The allocator facts at entry**: readiness with room for the copy, and
stack for `caml_stat_alloc_noexc` below the 432-byte frame. -/
structure FormatHeap (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra : BitVec 64) (len : Nat) (c : Config) :
    Prop where
  ready : RuntimeReadyL imageLive H (capacity + charge) sp ra c
  frame : NativeFrame sp (432 + allocHeadroom)
  charged : vsaChg (len + 1) charge

theorem FormatHeap.allocFrame {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra : BitVec 64} {len : Nat}
    {c : Config} (h : FormatHeap H capacity charge sp ra len c) :
    NativeFrame (sp + 18446744073709551184#64) allocHeadroom := by
  have nested := h.frame.nested (front := 432) (by decide)
  unfold nativeStack at nested
  rwa [show -BitVec.ofNat 64 432 = 18446744073709551184#64 by decide] at nested

/-- After `caml_stat_alloc_noexc(len + 1)` returns: the fresh block `res`. -/
structure Allocated (H : List (Nat × Nat)) (capacity : Nat) (sp : BitVec 64) (len : Nat) (res : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, len + 1) :: H) capacity (sp + 18446744073709551184#64)
    0x8000ddd8#64 after
  pc : PCAt 0x8000ddd8#64 after
  result : gprGet after.σ 10 = some res
  nonzero : res ≠ 0#64
  low : heapStart ≤ res.toNat
  high : res.toNat + (len + 1) ≤ heapEnd
  disjoint : ∀ e ∈ H, ∀ a, InExt (res.toNat, len + 1) a → ¬ InExt e a
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k
  caller : ∀ a, sp.toNat - 432 ≤ a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  blocks : ∀ q m a, (q, m) ∈ H → heapStart ≤ q → q + m ≤ heapEnd → q ≤ a → a < q + m →
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- **`caml_stat_alloc_noexc(len + 1)`** from the filled buffer. -/
theorem format_alloc {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra : BitVec 64} {name : List (BitVec 8)}
    {c0 base f : Config} (heap : FormatHeap H capacity charge sp ra name.length c0) (fits : name.length ≤ 255)
    (filled : Filled c0 sp name base f)
    (ready : RuntimeReadyL imageLive H (capacity + charge) (sp + 18446744073709551184#64) 0x8000ddd8#64 f) :
    ∃ g res, Steps f g ∧ Allocated H capacity sp name.length res f g := by
  have frameA := heap.allocFrame
  have sizeNat : (BitVec.ofNat 64 (name.length + 1)).toNat = name.length + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  obtain ⟨g, run, ⟨S⟩⟩ := (stat_alloc_ready f H capacity charge (BitVec.ofNat 64 (name.length + 1)) _ _ ready
    frameA filled.size (by rw [sizeNat]; exact heap.charged)).run f ⟨filled.pc, rfl⟩
  obtain ⟨pNonzero, pLow, pHigh, pDisjoint⟩ := S.allocation.result.fresh.destruct
  change (vsaReg g 10).toNat ≠ 0 at pNonzero
  change heapStart ≤ (vsaReg g 10).toNat at pLow
  change (vsaReg g 10).toNat + (BitVec.ofNat 64 (name.length + 1)).toNat ≤ heapEnd at pHigh
  rw [sizeNat] at pHigh pDisjoint
  have readyG := S.ready
  rw [sizeNat] at readyG
  have stackNat : (sp + 18446744073709551184#64).toNat = sp.toNat - 432 := by
    have := heap.frame.lower; have := heap.frame.upper
    simp only [heapEnd, allocHeadroom, Layout.sym_stack_top] at *
    bv_omega
  refine ⟨g, vsaReg g 10, run, ?_⟩
  exact
    { ready := readyG
      pc := library_pc S.allocation.good S.allocation.result.frame.pc
      result := library_gpr S.ready.platform (by decide) (by decide) rfl
      nonzero := fun h => pNonzero (by rw [h]; rfl)
      low := pLow
      high := pHigh
      disjoint := pDisjoint
      saved := fun k hk => S.saved_gpr hk
      caller := fun a ha => S.caller_byte frameA (by rw [stackNat]; exact ha)
      blocks := fun q m a member lo hi qa aq =>
        OCaml.Vm.Gc.Realloc.alloc_live_byte S frameA member lo hi ⟨qa, aq⟩
      output := by
        have alloc : Vsa.Machine.output g.σ = Vsa.Machine.output S.atMalloc.σ := S.allocation.output
        rw [alloc]
        simp only [Vsa.Machine.output, S.dispatch.output] }

end OCaml.Vm.Primitives.Uncaught.FormatException
