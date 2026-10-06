import OCaml.Vm.Repr
import OCaml.Vm.ImageData
import Vsa.Sim.FrameOn
import Vsa.Sim.DlHeap

/-!
# The running invariant: VM stack geometry (a1-arms)

`caml_init_stack` allocates the VM stack once, `Stack_size` bytes below
`Caml_state->stack_high`. Under the budget (`Fits`), `check_stacks` never
reaches `caml_realloc_stack`, so the stack stays in the window
`[high - stackBytes, high)` for the whole run.

`StackGeometry` places that window in writable RAM above every static
symbol, and separates it from every other part of the represented payload:
the `Caml_state` record, the code words, the live heap objects, the channel
records and the primitive-table entries. Consumers (`InvariantUse.lean`)
derive the arms' read/write windows and `PayloadOutside` certificates from it.
The code geometry facts are a2-sem's (`CodeFacts.lean`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- Only alignment, not a heap graph property: necessary for ISINT to
classify represented pointers and bytecode addresses as non-integers. A
property of the placement alone, so every arm preserves it. -/
structure EvenPlace (pl : Place) : Prop where
  code : pl.codeBase % 2 = 0
  heap : ∀ l a, pl.φ l = some a → a % 2 = 0
  atoms : pl.atomBase % 2 = 0

/-- The atom table: 256 zero-size atoms, each one header word, from the
table base (`Atom(t) = atomBase + 8 * t + 8`). -/
def atomTableBytes : Nat := 8 * 257

/-- Word alignment of the placement (malloc'd code buffer, word-aligned
blocks and atom table). Needed where the runtime tests low bits of a value
(`Is_exception_result` at STOP: `(res & 3) == 2`). Implies `EvenPlace`. -/
structure WordPlace (pl : Place) : Prop where
  code : pl.codeBase % 4 = 0
  heap : ∀ l a, pl.φ l = some a → a % 8 = 0
  atoms : pl.atomBase % 8 = 0

theorem WordPlace.even {pl : Place} (h : WordPlace pl) : EvenPlace pl :=
  ⟨by have := h.code; omega, fun l a ha => by have := h.heap l a ha; omega,
    by have := h.atoms; omega⟩

/-- The VM stack's allocation, `[high - stackBytes, high)`. -/
def stackWindow (high : Nat) : W := ⟨high - Layout.stackBytes, high⟩

/-- **Stack geometry** of a represented state under its placement. Every
field is placement-level or names a config word the arms frame anyway. -/
structure StackGeometry (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop where
  /-- the whole allocation lies above `.bss` (hence above the image, `tohost`
  and every static runtime variable) -/
  statics : Layout.sym_bss_end + Layout.stackBytes ≤ high
  /-- and inside RAM -/
  top : high ≤ 0x100000000
  aligned : high % 8 = 0
  domain : OutWRange [stackWindow high] (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes
  code : ∀ i w, P.code[i]? = some w → OutWRange [stackWindow high] (pl.codeBase + 4 * i) 4
  /-- every placed object, live or not: no arm then depends on the roots -/
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [stackWindow high] (a - 8) (8 * o.wosize + 8)
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutWRange [stackWindow high] a (chanOffBuff + ch.buffer.length)
  primitives : ∀ i name, P.prims[i]? = some name →
    OutWRange [stackWindow high]
      ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8
  /-- the VM stack, the `Caml_state` record and every placed object lie in the
  allocator arena, below the native stack (`NativeValid.low`) -/
  arena : high ≤ Vsa.Sim.DlHeap.heapEnd
  domainArena : (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  /-- the `Caml_state` record is allocated above `.bss` -/
  domainLow : Layout.sym_bss_end ≤ (word c Layout.sym_Caml_state).toNat
  domainAligned : (word c Layout.sym_Caml_state).toNat % 8 = 0
  heapArena : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    a + 8 * o.wosize ≤ Vsa.Sim.DlHeap.heapEnd
  /-- placed words are even (ISINT, BRANCHIF, block SWITCH) -/
  even : EvenPlace pl
  /-- placed words are word-aligned (STOP's exception-result test) -/
  words : WordPlace pl
  /-- every placed object starts above `.bss` (its header included) -/
  heapLow : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → Layout.sym_bss_end + 8 ≤ a
  /-- the code buffer and the atom table lie in the arena, apart from each
  other and from every placed object (word equality, code reads) -/
  codeLow : Layout.sym_bss_end ≤ pl.codeBase
  codeArena : pl.codeBase + 4 * P.code.size ≤ Vsa.Sim.DlHeap.heapEnd
  atomLow : Layout.sym_bss_end ≤ pl.atomBase
  atomArena : pl.atomBase + atomTableBytes ≤ Vsa.Sim.DlHeap.heapEnd
  codeAtoms : pl.codeBase + 4 * P.code.size ≤ pl.atomBase ∨ pl.atomBase + atomTableBytes ≤ pl.codeBase
  heapCode : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [⟨pl.codeBase, pl.codeBase + 4 * P.code.size⟩] (a - 8) (8 * o.wosize + 8)
  heapAtoms : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [⟨pl.atomBase, pl.atomBase + atomTableBytes⟩] (a - 8) (8 * o.wosize + 8)
  /-- placed objects are apart from the channel records and the primitive
  entries (object stores keep them) -/
  heapChannels : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    ∀ id ch b, s.world.chans[id]? = some ch → cp id = some b →
      OutWRange [⟨b, b + (chanOffBuff + ch.buffer.length)⟩] (a - 8) (8 * o.wosize + 8)
  heapPrims : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    ∀ i name, P.prims[i]? = some name →
      OutWRange [⟨(word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i, (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i + 8⟩] (a - 8) (8 * o.wosize + 8)
  /-- the `Caml_state` record is apart from the code, every placed object,
  the channel records and the primitive entries (its fields are written) -/
  domainCode : OutWRange [⟨pl.codeBase, pl.codeBase + 4 * P.code.size⟩]
    (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes
  domainHeap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] (a - 8) (8 * o.wosize + 8)
  domainChannels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] a (chanOffBuff + ch.buffer.length)
  domainPrims : ∀ i name, P.prims[i]? = some name →
    OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩]
      ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

/-- **Placement of a fresh object** (named obligation of the allocating
families, supplied by the nursery bounds, lane a6-gc): apart from the VM
stack window, the code buffer and the atom table, inside the arena and above
`.bss`. -/
structure NurseryPlacement (P : Prog) (pl : Place) (high a : Nat) (o : Obj) : Prop where
  stackApart : OutWRange [stackWindow high] (a - 8) (8 * o.wosize + 8)
  arenaEnd : a + 8 * o.wosize ≤ Vsa.Sim.DlHeap.heapEnd
  low : Layout.sym_bss_end + 8 ≤ a
  codeApart : OutWRange [⟨pl.codeBase, pl.codeBase + 4 * P.code.size⟩] (a - 8) (8 * o.wosize + 8)
  atomApart : OutWRange [⟨pl.atomBase, pl.atomBase + atomTableBytes⟩] (a - 8) (8 * o.wosize + 8)

/-- The geometry depends on the state only through object sizes and the
channel records, and on the configuration only through two pointer words. -/
theorem StackGeometry.transport {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} (g : StackGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)) :
    StackGeometry P s' c' pl cp high where
  statics := g.statics
  top := g.top
  aligned := g.aligned
  domain := by rw [domain]; exact g.domain
  code := g.code
  heap l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    simpa only [size] using g.heap l a o placed ho
  channels := by rw [chans]; exact g.channels
  primitives := by rw [prims]; exact g.primitives
  arena := g.arena
  domainArena := by rw [domain]; exact g.domainArena
  domainLow := by rw [domain]; exact g.domainLow
  domainAligned := by rw [domain]; exact g.domainAligned
  heapArena l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    simpa only [size] using g.heapArena l a o placed ho
  even := g.even
  words := g.words
  heapLow l a o' placed object := by
    obtain ⟨o, ho, -⟩ := objects l o' object
    exact g.heapLow l a o placed ho
  codeLow := g.codeLow
  codeArena := g.codeArena
  atomLow := g.atomLow
  atomArena := g.atomArena
  codeAtoms := g.codeAtoms
  heapCode l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    simpa only [size] using g.heapCode l a o placed ho
  heapAtoms l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    simpa only [size] using g.heapAtoms l a o placed ho
  heapChannels l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    rw [chans, ← size]; exact g.heapChannels l a o placed ho
  heapPrims l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    rw [prims, ← size]; exact g.heapPrims l a o placed ho
  domainCode := by rw [domain]; exact g.domainCode
  domainHeap l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    rw [domain]; simpa only [size] using g.domainHeap l a o placed ho
  domainChannels := by rw [domain, chans]; exact g.domainChannels
  domainPrims := by rw [domain, prims]; exact g.domainPrims

/-- Same heap and world: only the two pointer words need framing. -/
theorem StackGeometry.same {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} (g : StackGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) (memory : c'.σ.mem = c.σ.mem) :
    StackGeometry P s' c' pl cp high :=
  g.transport (fun l o' h => ⟨o', heap ▸ h, rfl⟩) (by rw [world])
    (by simp only [word, memory]) (by simp only [word, memory])

/-- A state change that keeps the heap and the world keeps the geometry. -/
theorem StackGeometry.state {P : Prog} {s s' : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} (g : StackGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) :
    StackGeometry P s' c pl cp high :=
  g.same heap world rfl

/-- An object of the allocated heap is the fresh one or an old one. -/
theorem heap_alloc_get {h : Heap} {o o' : Obj} {l : Nat} (found : (h.alloc o).1.get? l = some o') :
    h.get? l = some o' ∨ (l = (h.alloc o).2 ∧ o' = o) := by
  simp only [Heap.alloc, Heap.get?, Array.toList_push, List.getElem?_append] at found ⊢
  split at found
  · exact Or.inl found
  · rename_i hn
    rw [List.getElem?_singleton] at found
    split at found
    · cases found
      rename_i hz
      exact Or.inr ⟨by simp only [Array.length_toList] at hn hz ⊢; omega, rfl⟩
    · cases found

/-- An allocation placed apart from the stack window keeps the geometry. -/
theorem StackGeometry.alloc {P : Prog} {s s' : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {high a : Nat} {o : Obj} (g : StackGeometry P s c pl cp high)
    (placed : pl.φ (s.heap.alloc o).2 = some a)
    (np : NurseryPlacement P pl high a o)
    (domainApart : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] (a - 8) (8 * o.wosize + 8))
    (channelsApart : ∀ id ch b, s.world.chans[id]? = some ch → cp id = some b →
      OutWRange [⟨b, b + (chanOffBuff + ch.buffer.length)⟩] (a - 8) (8 * o.wosize + 8))
    (primsApart : ∀ i name, P.prims[i]? = some name →
      OutWRange [⟨(word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i, (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i + 8⟩] (a - 8) (8 * o.wosize + 8))
    (heap : s'.heap = (s.heap.alloc o).1) (world : s'.world = s.world) :
    StackGeometry P s' c pl cp high where
  statics := g.statics
  top := g.top
  aligned := g.aligned
  domain := g.domain
  code := g.code
  heap l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heap l a' o' found old
    · rw [placed] at found
      cases found
      exact np.stackApart
  channels := by rw [world]; exact g.channels
  primitives := g.primitives
  arena := g.arena
  domainArena := g.domainArena
  domainLow := g.domainLow
  domainAligned := g.domainAligned
  heapArena l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapArena l a' o' found old
    · rw [placed] at found
      cases found
      exact np.arenaEnd
  even := g.even
  words := g.words
  heapLow l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapLow l a' o' found old
    · rw [placed] at found; cases found; exact np.low
  codeLow := g.codeLow
  codeArena := g.codeArena
  atomLow := g.atomLow
  atomArena := g.atomArena
  codeAtoms := g.codeAtoms
  heapCode l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapCode l a' o' found old
    · rw [placed] at found; cases found; exact np.codeApart
  heapAtoms l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapAtoms l a' o' found old
    · rw [placed] at found; cases found; exact np.atomApart
  heapChannels l a' o' found object := by
    rw [heap] at object
    rw [world]
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapChannels l a' o' found old
    · rw [placed] at found; cases found; exact channelsApart
  heapPrims l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapPrims l a' o' found old
    · rw [placed] at found; cases found; exact primsApart
  domainCode := g.domainCode
  domainHeap l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.domainHeap l a' o' found old
    · rw [placed] at found; cases found; exact domainApart
  domainChannels := by rw [world]; exact g.domainChannels
  domainPrims := g.domainPrims

end OCaml.Vm.Sim
