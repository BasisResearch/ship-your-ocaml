import OCaml.Vm.Sim.LoopGeometry
import OCaml.Vm.Primitives.Channel.OpenRepr

/-!
# The geometry across a channel opening

`openChan` appends channel `n = chans.length` and the placement gains its
record `r` (`ChanPlace.put`). Every channel-quantified geometry field splits
into the old ids (the old geometry) and the new one (`NewChannelPlaced`, the
record's separation facts). The heap is unchanged here; the custom block's
allocation is the separate `alloc` step.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A channel of the opened table under the extended placement is an old one
or the new record. -/
theorem opened_cases {cs : List Chan} {ch ch' : Chan} {cp : ChanPlace} {r id a : Nat}
    (h : (cs ++ [ch])[id]? = some ch') (hp : cp.put cs.length r id = some a) :
    (cs[id]? = some ch' ∧ cp id = some a ∧ id < cs.length) ∨ (id = cs.length ∧ a = r) := by
  rcases chans_append_cases h with ⟨hc, lt⟩ | ⟨rfl, -⟩
  · rw [ChanPlace.put_other cp (Nat.ne_of_lt lt)] at hp
    exact Or.inl ⟨hc, hp, lt⟩
  · rw [ChanPlace.put_self] at hp
    exact Or.inr ⟨rfl, (Option.some.inj hp).symm⟩

/-- **The new record's separation** at `c`: `chanOffBuff + ioBufferSize`
bytes at `r`, apart from everything the geometry places. -/
structure NewChannelPlaced (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (high r : Nat) :
    Prop where
  stack : OutWRange [stackWindow high] r (chanOffBuff + ioBufferSize)
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [⟨r, r + (chanOffBuff + ioBufferSize)⟩] (a - 8) (8 * o.wosize + 8)
  arena : r + (chanOffBuff + ioBufferSize) ≤ Vsa.Sim.DlHeap.heapEnd
  low : Layout.sym_bss_end ≤ r
  code : OutWRange [⟨pl.codeBase, pl.codeBase + 4 * P.code.size⟩] r (chanOffBuff + ioBufferSize)
  atoms : OutWRange [⟨pl.atomBase, pl.atomBase + atomTableBytes⟩] r (chanOffBuff + ioBufferSize)
  prims : ∀ (i : Nat) name, P.prims[i]? = some name →
    OutWRange [⟨(word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i,
      (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i + 8⟩]
      r (chanOffBuff + ioBufferSize)
  apart : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    r + (chanOffBuff + ioBufferSize) ≤ a ∨ a + (chanOffBuff + ioBufferSize) ≤ r
  domain : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
    (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] r (chanOffBuff + ioBufferSize)
  nursery : OutWRange [Gc.nurseryFree c] r (chanOffBuff + ioBufferSize)
  private_ : OutWRange [Gc.privateRegion] r (chanOffBuff + ioBufferSize)

/-- **The stack geometry across an opening** (same heap). -/
theorem StackGeometry.openChan {P : Prog} {s s' : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high r : Nat} {ch : Chan} (g : StackGeometry P s c pl cp high) (new : NewChannelPlaced P s c pl cp high r)
    (heap : s'.heap = s.heap) (chans : s'.world.chans = s.world.chans ++ [ch]) :
    StackGeometry P s' c pl (cp.put s.world.chans.length r) high := by
  have objects : ∀ l o', s'.heap.get? l = some o' → s.heap.get? l = some o' := fun l o' h => heap ▸ h
  exact {
    statics := g.statics, top := g.top, aligned := g.aligned, domain := g.domain, code := g.code
    heap := fun l a o placed object => g.heap l a o placed (objects l o object)
    channels := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.channels id ch' a hc hp
      · exact new.stack
    primitives := g.primitives, arena := g.arena, domainArena := g.domainArena
    domainLow := g.domainLow, domainAligned := g.domainAligned
    heapArena := fun l a o placed object => g.heapArena l a o placed (objects l o object)
    even := g.even, words := g.words
    heapLow := fun l a o placed object => g.heapLow l a o placed (objects l o object)
    codeLow := g.codeLow, codeArena := g.codeArena, atomLow := g.atomLow, atomArena := g.atomArena
    codeAtoms := g.codeAtoms
    heapCode := fun l a o placed object => g.heapCode l a o placed (objects l o object)
    heapAtoms := fun l a o placed object => g.heapAtoms l a o placed (objects l o object)
    heapChannels := fun l a o placed object id ch' b h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.heapChannels l a o placed (objects l o object) id ch' b hc hp
      · exact new.heap l a o placed (objects l o object)
    primsRam := g.primsRam
    channelArena := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.channelArena id ch' a hc hp
      · exact new.arena
    primsArena := g.primsArena
    channelLow := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.channelLow id ch' a hc hp
      · exact new.low
    channelCode := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.channelCode id ch' a hc hp
      · exact new.code
    channelAtoms := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.channelAtoms id ch' a hc hp
      · exact new.atoms
    channelPrims := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.channelPrims id ch' a hc hp
      · exact new.prims
    channelsApart := fun id id' ch₁ ch₂ a a' ne h h' hp hp' => by
      rw [chans] at h h'
      rcases opened_cases h hp with ⟨hc, hq, _⟩ | ⟨e, rfl⟩ <;>
        rcases opened_cases h' hp' with ⟨hc', hq', _⟩ | ⟨e', rfl⟩
      · exact g.channelsApart id id' ch₁ ch₂ a a' ne hc hc' hq hq'
      · exact (new.apart id ch₁ a hc hq).symm
      · exact new.apart id' ch₂ a' hc' hq'
      · exact absurd (e.trans e'.symm) ne
    primsLow := g.primsLow
    heapPrims := fun l a o placed object => g.heapPrims l a o placed (objects l o object)
    domainCode := g.domainCode
    domainHeap := fun l a o placed object => g.domainHeap l a o placed (objects l o object)
    domainChannels := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hp, _⟩ | ⟨_, rfl⟩
      · exact g.domainChannels id ch' a hc hp
      · exact new.domain
    domainPrims := g.domainPrims }

/-- **The nursery geometry across an opening** (same heap): the
configuration may change in the words the geometry reads, and the open-channel
list gains the new record at its head. -/
theorem _root_.OCaml.Vm.Gc.NurseryGeometry.openChan {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high r : Nat} {ch : Chan} (g : Gc.NurseryGeometry P s c pl cp high) (new : NewChannelPlaced P s c pl cp high r)
    (heap : s'.heap = s.heap) (chans : s'.world.chans = s.world.chans ++ [ch])
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr)
    (listed : Gc.OpenChannelList c'.σ.mem (r :: Gc.placedChannels cp s.world.chans.length)) :
    Gc.NurseryGeometry P s' c' pl (cp.put s.world.chans.length r) high := by
  have window : Gc.nurseryFree c' = Gc.nurseryFree c := by simp only [Gc.nurseryFree, limit, ptr]
  have objects : ∀ l o', s'.heap.get? l = some o' → s.heap.get? l = some o' := fun l o' h => heap ▸ h
  exact {
    statics := by rw [window]; exact g.statics
    domain := by rw [window, domain]; exact g.domain
    stack := by rw [window]; exact g.stack
    code := by rw [window]; exact g.code
    heap := fun l a o placed object => by rw [window]; exact g.heap l a o placed (objects l o object)
    channels := fun id ch' a h hp => by
      rw [chans] at h
      rw [window]
      rcases opened_cases h hp with ⟨hc, hq, _⟩ | ⟨_, rfl⟩
      · exact g.channels id ch' a hc hq
      · exact new.nursery
    channelsPrivate := fun id ch' a h hp => by
      rw [chans] at h
      rcases opened_cases h hp with ⟨hc, hq, _⟩ | ⟨_, rfl⟩
      · exact g.channelsPrivate id ch' a hc hq
      · exact new.private_
    primitives := by rw [window, prims]; exact g.primitives
    top := by rw [ptr]; exact g.top
    aligned := by rw [ptr]; exact g.aligned
    domainLow := by rw [domain]; exact g.domainLow
    domainHigh := by rw [domain]; exact g.domainHigh
    domainAligned := by rw [domain]; exact g.domainAligned
    codeRange := by rw [window]; exact g.codeRange
    atoms := by rw [window]; exact g.atoms
    arena := by rw [ptr]; exact g.arena
    heapDomain := fun l a o placed object => by rw [domain]; exact g.heapDomain l a o placed (objects l o object)
    heapPrivate := fun l a o placed object => g.heapPrivate l a o placed (objects l o object)
    belowPrivate := by rw [ptr]; exact g.belowPrivate
    channelsListed := by
      rw [chans, List.length_append, List.length_singleton,
        Gc.placedChannels_push (fun id lt => ChanPlace.put_other cp (Nat.ne_of_lt lt)) (ChanPlace.put_self cp _ r)]
      exact listed
    heapChunks := fun l a o placed object => g.heapChunks l a o placed (objects l o object)
    nurseryLow := by rw [limit]; exact g.nurseryLow
    nurseryHigh := by rw [ptr]; exact g.nurseryHigh
    stackAbove := by rw [ptr]; exact g.stackAbove
    codeFits := g.codeFits
    primsFit := g.primsFit }

/-- **The loop geometry across an opening** (same heap). -/
theorem _root_.OCaml.LoopGeometry.openChan {L : OCaml.Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high r : Nat} {ch : Chan} (g : OCaml.LoopGeometry L P s c pl cp high)
    (new : NewChannelPlaced P s c pl cp high r)
    (heap : s'.heap = s.heap) (chans : s'.world.chans = s.world.chans ++ [ch])
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr)
    (listed : Gc.OpenChannelList c'.σ.mem (r :: Gc.placedChannels cp s.world.chans.length)) :
    OCaml.LoopGeometry L P s' c' pl (cp.put s.world.chans.length r) high :=
  ⟨⟨(g.toStackGeometry.openChan new heap chans).transport_ids (fun l o' h => ⟨o', h, rfl⟩)
      (fun _ => rfl) domain prims,
    g.nursery.openChan new heap chans domain prims limit ptr listed⟩,
   ⟨by rw [limit, ptr, heap]; exact g.room.nursery⟩⟩

end OCaml.Vm.Sim
