import OCaml.Vm.Sim.Invariant
import OCaml.Vm.RuntimeFields
import OCaml.Vm.Gc.OpenChannels

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

/-- The minor heap `[young_start, young_end)` and the major heap chunk under
G1 (the whileMin cut's values; the chunk's extent from its chunk head). -/
def minorRegion : W := ⟨0x80082000, 0x80282000⟩
def majorRegion : W := ⟨0x80283000, 0x8037b000⟩

/-- The code buffer's and the primitive table's sizes at the F1 cut: the
requests `caml_load_code` and the primitive table's growth made (whileMin's
191 code words; capacity 768 entries). -/
def f1CodeBytes : Nat := 764

/-- `caml_exe_name`'s target at the cut: startup's `caml_stat_strdup` of
`"/prog"` (`WhileMinEntry.read_caml_exe_name`, `WhileMinEntry.exe_name`). -/
def exeNameAddr : Nat := 0x8007d700
/-- The atom table (`caml_atom_table`) at the cut: `init_atom_table`'s
`caml_stat_alloc_aligned_noexc` block, 2056 bytes. -/
def atomTableAddr : Nat := 0x8038c000

def exeNameBytes : List (BitVec 8) := [0x2f#8, 0x70#8, 0x72#8, 0x6f#8, 0x67#8, 0x0#8]
def f1PrimCapacity : Nat := 768

/-- `[x, x + n)` lies in the minor heap or in the major heap chunk. -/
def InHeapChunks (x n : Nat) : Prop :=
  (minorRegion.lo ≤ x ∧ x + n ≤ minorRegion.hi) ∨ (majorRegion.lo ≤ x ∧ x + n ≤ majorRegion.hi)

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
    OutWRange [w] a (chanOffBuff + ioBufferSize)
  /-- `named_value_table`'s bucket array and nodes -/
  named : ∀ a, NamedPlFoot pl s.world.named a → OutWRange [w] a 1
  primitives : ∀ i name, P.prims[i]? = some name →
    OutWRange [w] ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

/-- The unallocated nursery, `[young_limit, young_ptr)`. -/
def nurseryFree (c : Config) : W := ⟨(runtimeFields c).youngLimit, (runtimeFields c).youngPtr⟩

/-- The placed channel records, newest first (`caml_all_opened_channels`'s
order: each open links its record at the head, with id `chans.length`). -/
def placedChannels (cp : ChanPlace) (n : Nat) : List Nat := (List.range n).reverse.filterMap cp

theorem mem_placedChannels {cp : ChanPlace} {n b : Nat} :
    b ∈ placedChannels cp n ↔ ∃ id, id < n ∧ cp id = some b := by
  simp [placedChannels, List.mem_filterMap]

/-- Opening channel `n` at `a` puts its record at the head. -/
theorem placedChannels_push {cp cp' : ChanPlace} {n a : Nat} (below : ∀ id, id < n → cp' id = cp id)
    (new : cp' n = some a) : placedChannels cp' (n + 1) = a :: placedChannels cp n := by
  simp only [placedChannels, List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.filterMap_cons, new]
  congr 1
  have congr : ∀ l : List Nat, (∀ x ∈ l, cp' x = cp x) → l.filterMap cp' = l.filterMap cp := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x l ih =>
      intro h
      simp only [List.filterMap_cons, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
  exact congr _ fun x hx => below x (by simpa using hx)

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
  /-- every placed object lies in the minor heap or the major chunk, which
  are newlib blocks apart from the other runtime blocks -/
  heapChunks : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → InHeapChunks (a - 8) (8 * o.wosize + 8)
  /-- the free nursery lies in the minor heap, so fresh objects do too -/
  nurseryLow : minorRegion.lo ≤ (runtimeFields c).youngLimit
  nurseryHigh : (runtimeFields c).youngPtr ≤ minorRegion.hi
  /-- every placed channel record misses the runtime's private region
  (newlib's records lie outside the major heap's free block) -/
  channelsPrivate : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutWRange [privateRegion] a (chanOffBuff + ioBufferSize)
  /-- the runtime's open-channel list is exactly the placed channel records
  (`caml_ml_open_descriptor_*` links each new record; nothing unlinks under G1) -/
  channelsListed : OpenChannelList c.σ.mem (placedChannels cp s.world.chans.length)
  /-- the nursery lies below the VM stack allocation, so a reserved block sits
  below every stack slot the arms write (a1-arms' CLOSUREREC) -/
  stackAbove : (runtimeFields c).youngPtr ≤ high - Layout.stackBytes
  /-- the program fits the cut's code buffer and primitive table, so a fresh
  malloc block misses its code and its primitive entries -/
  codeFits : 4 * P.code.size ≤ f1CodeBytes
  primsFit : P.prims.size ≤ f1PrimCapacity

/-- The open-channel list holds exactly the placed records. -/
theorem NurseryGeometry.channelsListed_mem {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : NurseryGeometry P s c pl cp high) :
    ∃ chs, OpenChannelList c.σ.mem chs ∧
      (∀ id ch a, s.world.chans[id]? = some ch → cp id = some a → a ∈ chs) ∧
      ∀ b ∈ chs, ∃ id ch, s.world.chans[id]? = some ch ∧ cp id = some b := by
  refine ⟨_, g.channelsListed, fun id ch a hc hp => mem_placedChannels.2 ⟨id, ?_, hp⟩, fun b hb => ?_⟩
  · exact (List.getElem?_eq_some_iff.mp hc).1
  · obtain ⟨id, lt, hp⟩ := mem_placedChannels.1 hb
    exact ⟨id, _, List.getElem?_eq_getElem lt, hp⟩

end OCaml.Vm.Gc
