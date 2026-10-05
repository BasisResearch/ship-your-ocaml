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
  heapArena : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    a + 8 * o.wosize ≤ Vsa.Sim.DlHeap.heapEnd

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
  heapArena l a o' placed object := by
    obtain ⟨o, ho, size⟩ := objects l o' object
    simpa only [size] using g.heapArena l a o placed ho

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
    (apart : OutWRange [stackWindow high] (a - 8) (8 * o.wosize + 8))
    (below : a + 8 * o.wosize ≤ Vsa.Sim.DlHeap.heapEnd)
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
      exact apart
  channels := by rw [world]; exact g.channels
  primitives := g.primitives
  arena := g.arena
  domainArena := g.domainArena
  heapArena l a' o' found object := by
    rw [heap] at object
    rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
    · exact g.heapArena l a' o' found old
    · rw [placed] at found
      cases found
      exact below

end OCaml.Vm.Sim
