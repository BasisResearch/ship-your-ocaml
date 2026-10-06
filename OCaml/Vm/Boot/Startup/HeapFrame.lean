import OCaml.Vm.Boot.Startup.HeapReady
import OCaml.Vm.Boot.Startup.ReadyPerm
import OCaml.Vm.Boot.Startup.AllocatorImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Every live block of a ready heap lies inside the allocator arena. -/
theorem HeapReady.block_bounds {H capacity c} (heap : HeapReady H capacity c) {q n : Nat}
    (member : (q, n) ∈ H) : heapStart ≤ q ∧ q + n ≤ heapEnd := by
  obtain ⟨_, m, top, brkv, chunks, bins, _, ⟨⟨hp, _⟩, _, _⟩, _⟩ := heap.room
  obtain ⟨chunk, inChunks, _, low, high⟩ := hp.live (q, n) member
  have bounds := chunkWalk_mem_bounds hp.walk inChunks
  have := hp.top_le
  have := hp.brk_le
  dsimp only at low high
  omega

/-- `HeapReady` reads only the heap foot, the allocator's code bytes, the
`Caml_state` word and the pool word. -/
theorem HeapReady.frame {H capacity c c'} (heap : HeapReady H capacity c)
    (foot : ∀ a, vsaFoot H a → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (text : ∀ pin ∈ VsaIris.Sym.allocText, (c'.σ.mem[pin.1]?).getD 0 = (c.σ.mem[pin.1]?).getD 0)
    (domain : ∀ i, i < 8 →
      (c'.σ.mem[Layout.sym_Caml_state + i]?).getD 0 = (c.σ.mem[Layout.sym_Caml_state + i]?).getD 0)
    (pool : ∀ i, i < 8 → (c'.σ.mem[Layout.sym_pool + i]?).getD 0 = (c.σ.mem[Layout.sym_pool + i]?).getD 0) :
    HeapReady H capacity c' where
  room := by
    apply roomLocal_vsaRoomB H _ _ capacity ?_ heap.room
    intro a ha
    exact (foot a ha).symm
  text := fun pin hp => (text pin hp).trans (heap.text pin hp)
  domainWord := (word_observed _ domain).trans heap.domainWord
  poolZero := lpins8_observed heap.poolZero pool

private theorem outW_of_forall {ws : List W} {a : Nat} (h : ∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a) : OutW ws a := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨h w (List.mem_cons_self ..), ih (fun v hv => h v (List.mem_cons_of_mem _ hv))⟩

/-- Writes confined to windows that each lie inside one live block keep
`HeapReady`: such windows miss the heap foot and every global it reads. -/
theorem HeapReady.frame_live {H capacity c c'} (heap : HeapReady H capacity c) (ws : List W)
    (inside : ∀ w ∈ ws, ∃ e ∈ H, e.1 ≤ w.lo ∧ w.hi ≤ e.1 + e.2)
    (frame : FrameOn ws c.σ.mem c'.σ.mem) : HeapReady H capacity c' := by
  have low (a : Nat) (below : a < heapStart) : OutW ws a := by
    apply outW_of_forall
    intro w hw
    obtain ⟨e, he, lo, _⟩ := inside w hw
    have := (heap.block_bounds he).1
    omega
  have keep (a : Nat) (out : OutW ws a) : (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    rw [frame a out]
  apply heap.frame
  · intro a ha
    apply keep
    rcases ha with global | ⟨lo, hi, apart⟩
    · apply low
      unfold allocGlobal InRange at global
      unfold heapStart
      omega
    · apply outW_of_forall
      intro w hw
      obtain ⟨e, he, elo, ehi⟩ := inside w hw
      rcases Nat.lt_or_ge a w.lo with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge a w.hi with g | g
        · exact absurd ⟨by omega, by omega⟩ (apart e he)
        · exact Or.inr g
  · intro pin hp
    exact keep _ (low _ (allocator_sources pin hp).geometry.high)
  · intro i hi
    exact keep _ (low _ (by unfold Layout.sym_Caml_state heapStart; omega))
  · intro i hi
    exact keep _ (low _ (by unfold Layout.sym_pool heapStart; omega))
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMin
open Startup

/-- **The newlib heap at the captured cut, covering given extents** (named
obligation, a0-boot). `cut_heapReady_Statement` with the live-block list
also covering each `[lo, lo + len)` of `E`. a6-gc instantiates `E` with the
blocks the F1 arms write. -/
def cut_heapReady_covers_Statement (E : List (Nat × Nat)) : Prop :=
  ∃ H capacity, 2 ^ 24 ≤ capacity ∧ HeapReady H capacity (Vsa.Densify.fillZero cut) ∧
    ∀ x ∈ E, ∃ e ∈ H, e.1 ≤ x.1 ∧ x.1 + x.2 ≤ e.1 + e.2
end OCaml.Vm.Boot.WhileMin
