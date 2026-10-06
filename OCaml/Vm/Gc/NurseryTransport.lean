import OCaml.Vm.Gc.NurseryDefs
import OCaml.Vm.Sim.InvariantUse
import OCaml.Vm.Primitives.MemoryFrame

/-!
# Preserving the nursery geometry

Low enough for a1-arms' restore sites (`Sim/ReadOnly.lean` and below):
`NurseryGeometry.same`/`transport`/`frame_log` for non-allocating steps and
`NurseryGeometry.alloc` after a nursery reservation, mirroring
`StackGeometry`'s.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Sim OCaml.Vm.Primitives

/-- After the reservation the free window ends at `a - 8`, so the new block
lies outside it (`OutWRange.shrink` keeps the older separations). -/
theorem reserve_outside {c' : Config} {count a : Nat}
    (after : (runtimeFields c').youngPtr = a - 8) :
    OutWRange [nurseryFree c'] (a - 8) (8 * count + 8) :=
  ⟨Or.inr (by simp only [nurseryFree, after]; omega), trivial⟩

/-- A range separated from the old free window is separated from the shrunk one. -/
theorem OutWRange.shrink {c c' : Config} {x n : Nat}
    (h : OutWRange [nurseryFree c] x n)
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (lower : (runtimeFields c').youngPtr ≤ (runtimeFields c).youngPtr) :
    OutWRange [nurseryFree c'] x n := by
  obtain ⟨h, -⟩ := h
  simp only [nurseryFree] at h
  exact ⟨by simp only [nurseryFree, limit]; omega, trivial⟩

/-- The open-channel list survives when its head and every placed record's
`next` word are unchanged and the channel ids are kept. -/
theorem channelsListed_transfer {s s' : St} {c c' : Config} {cp : ChanPlace}
    (h : ∃ chs, OpenChannelList c.σ.mem chs ∧
      (∀ id ch a, s.world.chans[id]? = some ch → cp id = some a → a ∈ chs) ∧
      ∀ b ∈ chs, ∃ id ch, s.world.chans[id]? = some ch ∧ cp id = some b)
    (ids : ∀ id : Nat, (s'.world.chans[id]?).isSome = (s.world.chans[id]?).isSome)
    (head : word c' Layout.sym_caml_all_opened_channels = word c Layout.sym_caml_all_opened_channels)
    (links : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
      word c' (a + chanOffNext) = word c (a + chanOffNext)) :
    ∃ chs, OpenChannelList c'.σ.mem chs ∧
      (∀ id ch a, s'.world.chans[id]? = some ch → cp id = some a → a ∈ chs) ∧
      ∀ b ∈ chs, ∃ id ch, s'.world.chans[id]? = some ch ∧ cp id = some b := by
  obtain ⟨chs, list, placed, listed⟩ := h
  refine ⟨chs, ?_, fun id _ a h hp => let ⟨ch, hc⟩ := Sim.chan_back ids h; placed id ch a hc hp,
    fun b hb => ?_⟩
  rotate_left
  · obtain ⟨id, ch, hc, hp⟩ := listed b hb
    obtain ⟨ch', hc'⟩ := Sim.chan_back (s := s') (s' := s) (fun id => (ids id).symm) hc
    exact ⟨id, ch', hc', hp⟩
  unfold OpenChannelList
  change bytesT c'.σ.mem _ 8 = bytesT c.σ.mem _ 8 at head
  rw [head]
  refine OpenChannels.congr list fun b hb => ?_
  obtain ⟨id, ch, hc, hp⟩ := listed b hb
  exact links id ch b hc hp

/-- **Transport** across a step that keeps object sizes, the channel ids, the
`Caml_state` and primitive-table pointers, and the `young_limit`/`young_ptr`
words (every non-allocating arm, and channel primitives), mirroring
`StackGeometry.transport_ids`. -/
theorem NurseryGeometry.transport_ids {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : NurseryGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (ids : ∀ id : Nat, (s'.world.chans[id]?).isSome = (s.world.chans[id]?).isSome)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr)
    (head : word c' Layout.sym_caml_all_opened_channels = word c Layout.sym_caml_all_opened_channels)
    (links : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
      word c' (a + chanOffNext) = word c (a + chanOffNext)) :
    NurseryGeometry P s' c' pl cp high := by
  have window : nurseryFree c' = nurseryFree c := by simp only [nurseryFree, limit, ptr]
  exact {
    statics := by rw [window]; exact g.statics
    domain := by rw [window, domain]; exact g.domain
    stack := by rw [window]; exact g.stack
    code := by rw [window]; exact g.code
    heap := fun l a o' placed object => by
      obtain ⟨o, ho, size⟩ := objects l o' object
      rw [window, ← size]; exact g.heap l a o placed ho
    channels := fun id _ a h hp => by
      obtain ⟨ch, hc⟩ := Sim.chan_back ids h
      rw [window]; exact g.channels id ch a hc hp
    channelsPrivate := fun id _ a h hp => let ⟨ch, hc⟩ := Sim.chan_back ids h; g.channelsPrivate id ch a hc hp
    primitives := by rw [window, prims]; exact g.primitives
    top := by rw [ptr]; exact g.top
    aligned := by rw [ptr]; exact g.aligned
    domainLow := by rw [domain]; exact g.domainLow
    domainHigh := by rw [domain]; exact g.domainHigh
    domainAligned := by rw [domain]; exact g.domainAligned
    codeRange := by rw [window]; exact g.codeRange
    atoms := by rw [window]; exact g.atoms
    arena := by rw [ptr]; exact g.arena
    heapDomain := fun l a o' placed object => by
      obtain ⟨o, ho, size⟩ := objects l o' object
      rw [domain, ← size]; exact g.heapDomain l a o placed ho
    heapPrivate := fun l a o' placed object => by
      obtain ⟨o, ho, size⟩ := objects l o' object
      rw [← size]; exact g.heapPrivate l a o placed ho
    belowPrivate := by rw [ptr]; exact g.belowPrivate
    channelsListed := channelsListed_transfer g.channelsListed ids head links
    heapChunks := fun l a o' placed object => by
      obtain ⟨o, ho, size⟩ := objects l o' object
      rw [← size]; exact g.heapChunks l a o placed ho
    nurseryLow := by rw [limit]; exact g.nurseryLow
    nurseryHigh := by rw [ptr]; exact g.nurseryHigh
    stackAbove := by rw [ptr]; exact g.stackAbove
    codeFits := g.codeFits
    primsFit := g.primsFit }

/-- **Transport** across a step that keeps the channel table. -/
theorem NurseryGeometry.transport {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : NurseryGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr)
    (head : word c' Layout.sym_caml_all_opened_channels = word c Layout.sym_caml_all_opened_channels)
    (links : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
      word c' (a + chanOffNext) = word c (a + chanOffNext)) :
    NurseryGeometry P s' c' pl cp high :=
  g.transport_ids objects (fun id => by rw [chans]) domain prims limit ptr head links

/-- **Transport across a write log** missing the `Caml_state` and
primitive-table pointers and the `young_limit`/`young_ptr` words (VM-stack
stores, object field stores, other `Caml_state` fields). -/
theorem NurseryGeometry.frame_log {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {log : List WEntry} (g : NurseryGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (limit : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8)
    (ptr : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) 8)
    (head : OutLRange log Layout.sym_caml_all_opened_channels 8)
    (links : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a → OutLRange log (a + chanOffNext) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : NurseryGeometry P s' c' pl cp high := by
  have keep : ∀ x, OutLRange log x 8 → word c' x = word c x := fun x h => by
    change bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8
    rw [memory, bytesT_writeLog_out _ h]
  have dom := keep _ domain
  refine g.transport objects chans dom (keep _ contents) ?_ ?_ (keep _ head)
    (fun id ch a hc hp => keep _ (links id ch a hc hp))
  · simp only [runtimeFields, domainWord, dom]; rw [keep _ limit]
  · simp only [runtimeFields, domainWord, dom]; rw [keep _ ptr]

/-- **Allocation** of `o` at a reserved address `a`: the free window shrinks
to end at `a - 8`, and the new object lies outside it. -/
theorem NurseryGeometry.alloc {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high count a : Nat} {o : Obj} (g : NurseryGeometry P s c pl cp high)
    (placed : pl.φ (s.heap.alloc o).2 = some a) (size : o.wosize ≤ count)
    (heap : s'.heap = (s.heap.alloc o).1) (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (before : (runtimeFields c).youngPtr = a + 8 * count)
    (after : (runtimeFields c').youngPtr = a - 8) (room : 8 ≤ a) (aligned : (a - 8) % 8 = 0)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8)
    (head : word c' Layout.sym_caml_all_opened_channels = word c Layout.sym_caml_all_opened_channels)
    (links : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
      word c' (a + chanOffNext) = word c (a + chanOffNext)) :
    NurseryGeometry P s' c' pl cp high := by
  have lower : (runtimeFields c').youngPtr ≤ (runtimeFields c).youngPtr := by omega
  have sh : ∀ {x n}, OutWRange [nurseryFree c] x n → OutWRange [nurseryFree c'] x n :=
    fun h => OutWRange.shrink h limit lower
  exact {
    statics := by simp only [nurseryFree, limit]; exact g.statics
    domain := by rw [domain]; exact sh g.domain
    stack := sh g.stack
    code := fun i v hv => sh (g.code i v hv)
    heap := fun l a' o' found object => by
      rw [heap] at object
      rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
      · exact sh (g.heap l a' o' found old)
      · rw [placed] at found
        cases found
        have := reserve_outside (c' := c') (count := o'.wosize) after
        simpa only [Nat.add_comm] using this
    channels := by rw [chans]; exact fun id ch x h1 h2 => sh (g.channels id ch x h1 h2)
    channelsPrivate := by rw [chans]; exact g.channelsPrivate
    primitives := by rw [prims]; exact fun i name h => sh (g.primitives i name h)
    top := by have := g.top; omega
    aligned := by rw [after]; exact aligned
    domainLow := by rw [domain]; exact g.domainLow
    domainHigh := by rw [domain]; exact g.domainHigh
    domainAligned := by rw [domain]; exact g.domainAligned
    codeRange := sh g.codeRange
    atoms := sh g.atoms
    arena := by have := g.arena; omega
    heapDomain := fun l a' o' found object => by
      rw [domain]
      rw [heap] at object
      rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
      · exact g.heapDomain l a' o' found old
      · rw [placed] at found
        cases found
        have dom := g.domain
        obtain ⟨h, -⟩ := dom
        simp only [nurseryFree] at h
        exact ⟨by dsimp only; omega, trivial⟩
    heapPrivate := fun l a' o' found object => by
      rw [heap] at object
      rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
      · exact g.heapPrivate l a' o' found old
      · rw [placed] at found
        cases found
        have := g.belowPrivate
        exact ⟨Or.inl (by omega), trivial⟩
    belowPrivate := by have := g.belowPrivate; omega
    channelsListed := channelsListed_transfer g.channelsListed (fun id => by rw [chans]) head links
    heapChunks := fun l a' o' found object => by
      rw [heap] at object
      rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
      · exact g.heapChunks l a' o' found old
      · rw [placed] at found
        cases found
        have := g.nurseryLow
        have := g.nurseryHigh
        exact Or.inl ⟨by omega, by omega⟩
    nurseryLow := by rw [limit]; exact g.nurseryLow
    nurseryHigh := by have := g.nurseryHigh; omega
    stackAbove := by have := g.stackAbove; omega
    codeFits := g.codeFits
    primsFit := g.primsFit }

/-- A step that keeps heap, world and memory keeps the geometry. -/
theorem NurseryGeometry.same {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : NurseryGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) (memory : c'.σ.mem = c.σ.mem) :
    NurseryGeometry P s' c' pl cp high :=
  g.transport (fun l o' h => ⟨o', heap ▸ h, rfl⟩) (by rw [world])
    (by simp only [word, memory]) (by simp only [word, memory])
    (by simp only [runtimeFields, domainWord, word, memory]) (by simp only [runtimeFields, domainWord, word, memory])
    (by simp only [word, memory]) (fun _ _ _ _ _ => by simp only [word, memory])

/-- The reserved block `[a - 8, a + 8 * count)` lies in the free nursery, so
its initializing writes miss the payload (`WindowSeparated.payload`). -/
theorem reserved_inside {c : Config} {count a : Nat} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) {b k : Nat}
    (low : a - 8 ≤ b) (high : b + k ≤ a + 8 * count) : InsideW [nurseryFree c] b k :=
  Or.inl ⟨by simp only [nurseryFree]; omega, by simp only [nurseryFree]; omega⟩

/-- A range inside the free nursery misses any range separated from it. -/
theorem apart_of_inside {c : Config} {x n y k : Nat} (outside : OutWRange [nurseryFree c] x n)
    (low : (runtimeFields c).youngLimit ≤ y) (high : y + k ≤ (runtimeFields c).youngPtr) :
    y + k ≤ x ∨ x + n ≤ y := by
  obtain ⟨h, -⟩ := outside
  simp only [nurseryFree] at h
  omega

/-- **`NurseryPlacement` for a nursery reservation**: an object of at most
`count` fields reserved below `young_ptr = a + 8 * count`, within capacity. -/
theorem NurseryGeometry.placement {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {count a : Nat} {o : Obj} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) (room : 8 ≤ a) (size : o.wosize ≤ count) :
    NurseryPlacement P pl high a o := by
  have statics := g.statics
  have arena := g.arena
  simp only [nurseryFree] at statics
  have low : (runtimeFields c).youngLimit ≤ a - 8 := capacity
  have high' : a - 8 + (8 * o.wosize + 8) ≤ (runtimeFields c).youngPtr := by omega
  refine ⟨⟨?_, trivial⟩, by omega, by omega, ⟨?_, trivial⟩, ⟨?_, trivial⟩⟩
  · have := apart_of_inside g.stack low high'
    simp only [stackWindow]
    omega
  · have := apart_of_inside g.codeRange low high'
    omega
  · have := apart_of_inside g.atoms low high'
    omega

end OCaml.Vm.Gc
