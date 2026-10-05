import OCaml.Vm.Sim.Invariant
import OCaml.Vm.RuntimeFields

/-!
# Nursery geometry: definitions

Low in the import graph (below `OCaml/Refinement.lean`) so that the loop-head
witness can carry `NurseryGeometry` beside `StackGeometry`. The lemmas are in
`OCaml/Vm/Gc/NurseryGeometry.lean`.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Sim

/-- The runtime's private major-heap region under G1: the cut's single free
block `[0x80283000, 0x8037ad00)` (`WhileMinRuntime.freeBlock`, header through
last word; `F1Runtime.privateRegion_eq`). No object is placed in it, so object
field stores never disturb the allocator state. G2 replaces it by the
free-list placement invariant (`SmallListsIn`, `LeastIn`). -/
def privateRegion : W := ⟨0x80283000, 0x8037ad00⟩

/-- A window missing every observation of the represented payload. -/
structure WindowSeparated (w : W) (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop where
  /-- above `.bss` (hence above the image, `tohost` and every static variable) -/
  statics : Layout.sym_bss_end ≤ w.lo
  domain : OutWRange [w] (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes
  stack : OutWRange [w] (high - Layout.stackBytes) Layout.stackBytes
  code : ∀ i v, P.code[i]? = some v → OutWRange [w] (pl.codeBase + 4 * i) 4
  /-- every placed object (live or not, as in `StackGeometry`) -/
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → OutWRange [w] (a - 8) (8 * o.wosize + 8)
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutWRange [w] a (chanOffBuff + ch.buffer.length)
  primitives : ∀ i name, P.prims[i]? = some name →
    OutWRange [w] ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

/-- The unallocated nursery, `[young_limit, young_ptr)`. -/
def nurseryFree (c : Config) : W := ⟨(runtimeFields c).youngLimit, (runtimeFields c).youngPtr⟩

/-- **Nursery geometry**: the free nursery misses the represented payload and
lies in RAM; the `Caml_state` record lies in aligned RAM above `tohost`. -/
structure NurseryGeometry (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop extends WindowSeparated (nurseryFree c) P s c pl cp high where
  top : (runtimeFields c).youngPtr ≤ 0x100000000
  aligned : (runtimeFields c).youngPtr % 8 = 0
  domainLow : Layout.sym_tohost + 16 ≤ (word c Layout.sym_Caml_state).toNat
  domainHigh : (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ 0x100000000
  domainAligned : (word c Layout.sym_Caml_state).toNat % 8 = 0
  /-- the whole loaded code buffer, the atom table, and the allocator arena's end -/
  codeRange : OutWRange [nurseryFree c] pl.codeBase (4 * P.code.size)
  atoms : OutWRange [nurseryFree c] pl.atomBase atomTableBytes
  arena : (runtimeFields c).youngPtr ≤ Vsa.Sim.DlHeap.heapEnd
  /-- every placed object misses the `Caml_state` record -/
  heapDomain : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] (a - 8) (8 * o.wosize + 8)
  /-- every placed object misses the runtime's private region, and the
  nursery lies below it, so fresh objects do too -/
  heapPrivate : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [privateRegion] (a - 8) (8 * o.wosize + 8)
  belowPrivate : (runtimeFields c).youngPtr ≤ privateRegion.lo

end OCaml.Vm.Gc
