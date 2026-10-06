import OCaml.Vm.Boot.Startup.RuntimeReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem vsaFoot_perm {H H' : List (Nat × Nat)} (perm : H.Perm H') (a : Nat) : vsaFoot H a ↔ vsaFoot H' a := by
  unfold vsaFoot
  constructor
  · rintro (g | ⟨lo, hi, out⟩)
    · exact Or.inl g
    · exact Or.inr ⟨lo, hi, fun e he => out e (perm.mem_iff.2 he)⟩
  · rintro (g | ⟨lo, hi, out⟩)
    · exact Or.inl g
    · exact Or.inr ⟨lo, hi, fun e he => out e (perm.mem_iff.1 he)⟩

theorem vsaRoomB_perm {img : Nat → BitVec 8} {H H' : List (Nat × Nat)} {k : Nat} (perm : H.Perm H')
    (h : vsaRoomB img H k) : vsaRoomB img H' k := by
  obtain ⟨starts, m, top, brkv, chunks, bins, img', heap, room⟩ := h
  refine ⟨(perm.map Prod.fst).nodup_iff.1 starts, m, top, brkv, chunks, bins, ?_, ?_, room⟩
  · intro a ha
    exact img' a ((vsaFoot_perm perm a).2 ha)
  · obtain ⟨⟨hp, topRoom⟩, page, bb⟩ := heap
    exact ⟨⟨{ hp with
        live := fun e he => hp.live e (perm.mem_iff.2 he)
        exact := fun e he hr => hp.exact e (perm.mem_iff.2 he) (perm.mem_iff.2 hr) }, topRoom⟩, page, bb⟩

/-- Readiness depends on the live blocks only as a set. -/
theorem RuntimeReady.perm {H H' : List (Nat × Nat)} {capacity sp ra c} (ready : RuntimeReady H capacity sp ra c)
    (perm : H.Perm H') : RuntimeReady H' capacity sp ra c :=
  { ready with room := vsaRoomB_perm perm ready.room }

theorem chunkWalk_mem_bounds {m : Vsa.MemRepr.Mem} {p top : Nat} {cs : List Chunk} (walk : ChunkWalk m p top cs)
    {c : Chunk} (member : c ∈ cs) : p ≤ c.addr ∧ c.addr + c.size ≤ top := by
  induction walk with
  | top => cases member
  | chunk _ _ _ _ _ rest ih =>
    have tail := rest.le
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨Nat.le_refl _, tail⟩
    · have := ih later
      omega

/-- Every live block lies inside the allocator arena. -/
theorem RuntimeReady.block_bounds {H capacity sp ra c} (ready : RuntimeReady H capacity sp ra c)
    {q n : Nat} (member : (q, n) ∈ H) : heapStart ≤ q ∧ q + n ≤ heapEnd := by
  obtain ⟨_, m, top, brkv, chunks, bins, _, ⟨⟨hp, topRoom⟩, _, _⟩, _⟩ := ready.room
  obtain ⟨chunk, inChunks, _, low, high⟩ := hp.live (q, n) member
  have bounds := chunkWalk_mem_bounds hp.walk inChunks
  have := hp.top_le
  have := hp.brk_le
  dsimp only at low high
  omega
end OCaml.Vm.Boot.Startup
