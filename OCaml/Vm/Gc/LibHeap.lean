import OCaml.Vm.Boot.Startup.HeapFrame
import Vsa.Sim.FrameOn

/-!
# The newlib heap under the interpreter's writes

a0-boot's `HeapReady H capacity c` (newlib's heap shape and room for the live
blocks `H`) survives any write that misses what it reads: the allocator's
footprint outside the `errno` words, its code pins, the `Caml_state` word and
the pool word. `HeapSafe H w` classifies the windows the interpreter writes:
inside a live block, above the arena, an `errno` word, or a low static word
the allocator never reads. `HeapReady.frame_windows` keeps `HeapReady` under
a frame on such windows.
-/

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris VsaIris.VsaHeap

/-- The bytes `HeapReady` reads outside the allocator's footprint: the
allocator's code, the `_impure_ptr` word, the `Caml_state` and pool words. -/
def HeapPinned (a : Nat) : Prop :=
  a < Image.textBase + Image.textSize ∨ (allocatorImpureAddr ≤ a ∧ a < allocatorImpureAddr + 8) ∨
    (Layout.sym_Caml_state ≤ a ∧ a < Layout.sym_Caml_state + 8) ∨ (Layout.sym_pool ≤ a ∧ a < Layout.sym_pool + 8)

/-- Writes keep `HeapReady` when every byte it reads, other than the `errno`
words, is unchanged. -/
theorem HeapReady.frame_read {H capacity c c'} (heap : HeapReady H capacity c)
    (keep : ∀ a, a ∉ errnoBytes → (vsaRead H a ∨ HeapPinned a) →
      (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) : HeapReady H capacity c' where
  room := vsaRoomB_errno heap.room fun a ha =>
    (keep a (fun h => by rcases errnoBytes_mem.1 h with e | e; exact ha.2.1 e; exact ha.2.2 e) (Or.inl ha)).symm
  text := fun pin hp => by
    have source := allocator_sources pin hp
    refine (keep _ (fun h => ?_) (Or.inr ?_)).trans (heap.text pin hp)
    · unfold AllocatorByteSource at source
      rw [errnoBytes_mem] at h
      unfold InRange at h
      split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega
    · unfold AllocatorByteSource at source
      split at source
      · exact Or.inl (by assumption)
      · exact Or.inr (Or.inl ⟨source.1, source.2.1⟩)
  domainWord := (word_observed _ fun i hi => keep _ (fun h => by
    rw [errnoBytes_mem] at h; unfold InRange Layout.sym_Caml_state at *; omega)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans heap.domainWord
  poolZero := lpins8_observed heap.poolZero fun i hi => keep _ (fun h => by
    rw [errnoBytes_mem] at h; unfold InRange Layout.sym_pool at *; omega)
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

/-- A write window `HeapReady H` tolerates. -/
def HeapSafe (H : List (Nat × Nat)) (w : W) : Prop :=
  (∃ e ∈ H, e.1 ≤ w.lo ∧ w.hi ≤ e.1 + e.2) ∨ heapEnd ≤ w.lo ∨
    (∀ a, w.lo ≤ a → a < w.hi → a ∈ errnoBytes) ∨
    (w.hi ≤ heapStart ∧ ∀ a, w.lo ≤ a → a < w.hi → ¬ allocGlobal a ∧ ¬ HeapPinned a)

theorem outW_all {ws : List W} {a : Nat} (h : ∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a) : OutW ws a := by
  induction ws with
  | nil => trivial
  | cons w ws ih => exact ⟨h w List.mem_cons_self, ih fun v hv => h v (List.mem_cons_of_mem _ hv)⟩

theorem HeapPinned.low {a : Nat} (h : HeapPinned a) : a < heapStart := by
  unfold HeapPinned at h
  simp only [Image.textBase, Image.textSize, allocatorImpureAddr, Layout.sym_Caml_state, Layout.sym_pool,
    heapStart] at *
  omega

/-- **The newlib heap survives writes confined to safe windows**, given
byte equality outside them. -/
theorem HeapReady.keep_windows {H capacity c c'} (heap : HeapReady H capacity c) {ws : List W}
    (safe : ∀ w ∈ ws, HeapSafe H w)
    (keep : ∀ a, (∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a) → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) :
    HeapReady H capacity c' := by
  apply HeapReady.frame_read heap
  intro a notErr reads
  apply keep a
  intro w hw
  rcases Nat.lt_or_ge a w.lo with h | h
  · exact Or.inl h
  rcases Nat.lt_or_ge a w.hi with g | g
  · exfalso
    rcases safe w hw with ⟨e, he, lo, hi⟩ | above | errno | ⟨wh, low⟩
    · have eLow := (heap.block_bounds he).1
      rcases reads with r | r
      · rcases r.1 with global | ⟨_, _, apart⟩
        · unfold allocGlobal InRange heapStart at *; omega
        · exact apart e he ⟨by omega, by omega⟩
      · have := r.low; omega
    · rcases reads with r | r
      · have := allocator_foot_below r.1; omega
      · have := r.low; unfold heapStart heapEnd at *; omega
    · exact notErr (errno a h g)
    · obtain ⟨notGlobal, notPinned⟩ := low a h g
      rcases reads with r | r
      · rcases r.1 with global | ⟨hs, _, _⟩
        · exact notGlobal global
        · omega
      · exact notPinned r
  · exact Or.inr g

/-- `HeapReady.keep_windows` for a frame. -/
theorem HeapReady.frame_windows {H capacity c c'} (heap : HeapReady H capacity c) {ws : List W}
    (safe : ∀ w ∈ ws, HeapSafe H w) (frame : FrameOn ws c.σ.mem c'.σ.mem) : HeapReady H capacity c' :=
  HeapReady.keep_windows heap safe fun a out => by rw [frame a (outW_all out)]

end OCaml.Vm.Gc
