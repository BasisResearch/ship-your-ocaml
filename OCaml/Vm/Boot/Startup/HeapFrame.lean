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

/-- The bytes of newlib's two `errno` words (`_impure_data._errno`, `errno`). -/
def errnoBytes : List Nat :=
  [0x80064668, 0x80064669, 0x8006466a, 0x8006466b, 0x80064d48, 0x80064d49, 0x80064d4a, 0x80064d4b]

theorem errnoBytes_mem {a : Nat} :
    a ∈ errnoBytes ↔ InRange 0x80064668 0x8006466c a ∨ InRange 0x80064d48 0x80064d4c a := by
  simp only [errnoBytes, List.mem_cons, List.not_mem_nil, or_false, InRange]
  omega

private theorem insert_all_get (img : Nat → BitVec 8) :
    ∀ (xs : List Nat) (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat),
      (xs.foldl (fun m x => m.insert x (img x)) m)[a]? = if a ∈ xs then some (img a) else m[a]?
  | [], m, a => by simp
  | x :: xs, m, a => by
    rw [List.foldl_cons, insert_all_get img xs, Std.ExtHashMap.getElem?_insert]
    by_cases hx : a ∈ xs
    · simp [hx]
    · by_cases ha : a = x
      · subst ha; simp
      · simp [hx, ha, Ne.symm ha]

/-- The heap's room ignores the `errno` words: the shape reads `vsaRead`,
which excludes them, so a new image there is re-pinned by a fresh witness. -/
theorem vsaRoomB_errno {H : List (Nat × Nat)} {img img' : Nat → BitVec 8} {k : Nat}
    (room : vsaRoomB img H k) (same : ∀ a, vsaRead H a → img a = img' a) : vsaRoomB img' H k := by
  obtain ⟨starts, m, top, brkv, chunks, bins, on, shape, roomy⟩ := room
  let m' := errnoBytes.foldl (fun m x => m.insert x (img' x)) m
  refine ⟨starts, m', top, brkv, chunks, bins, fun a ha => ?_, shape.transport_read fun a ha => ?_, roomy⟩
  · rw [insert_all_get]
    split
    · rfl
    · rename_i out
      rw [errnoBytes_mem] at out
      rw [on a ha, same a ⟨ha, fun h => out (.inl h), fun h => out (.inr h)⟩]
  · rw [insert_all_get]
    split
    · rename_i inside
      rw [errnoBytes_mem] at inside
      rcases inside with h | h
      · exact absurd h ha.2.1
      · exact absurd h ha.2.2
    · rfl

/-- Stores to the `errno` words keep `HeapReady`. -/
theorem HeapReady.frame_errno {H capacity c c'} (heap : HeapReady H capacity c)
    (keep : ∀ a, a ∉ errnoBytes → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) : HeapReady H capacity c' where
  room := vsaRoomB_errno heap.room fun a ha =>
    (keep a fun h => by rcases errnoBytes_mem.1 h with e | e; exact ha.2.1 e; exact ha.2.2 e).symm
  text := fun pin hp => by
    refine (keep _ fun h => ?_).trans (heap.text pin hp)
    have source := allocator_sources pin hp
    unfold AllocatorByteSource at source
    rw [errnoBytes_mem] at h
    unfold InRange at h
    split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega
  domainWord := (word_observed _ fun i hi => keep _ fun h => by
    rw [errnoBytes_mem] at h; unfold InRange Layout.sym_Caml_state at *; omega).trans heap.domainWord
  poolZero := lpins8_observed heap.poolZero fun i hi => keep _ fun h => by
    rw [errnoBytes_mem] at h; unfold InRange Layout.sym_pool at *; omega
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
