import OCaml.Vm.Reloc
import OCaml.Vm.Gc.LibHeap
import OCaml.Vm.Gc.OpenChannels
import OCaml.Vm.Boot.WhileMinHeapChunks
import OCaml.Vm.Boot.WhileMinEntryReads
import OCaml.Vm.Gc.NurseryDefs

/-!
# newlib's heap under F1

F1 paths write five fixed runtime regions, each inside one of newlib's live
malloc blocks (`f1Extents`): the `Caml_state` record, the remembered-set
struct, the minor heap, the major heap chunk and the VM stack. They also
write open channel records, each a live block of its own. `LibHeapAt H cap chs c`
holds a0-boot's `HeapReady H cap` with room `2^24`, plus the coverage of the
extents and of the open channels `chs` (read from `caml_all_opened_channels`).

`F1HeapSafe w` is the window class this invariant tolerates. It does not
depend on `H`: inside an extent, above the arena, an `errno` word, or a low
static word the allocator never reads. `LibHeapAt.frame_windows` keeps the
invariant under a frame on such windows when the list head is unchanged.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Boot.Startup VsaIris.VsaHeap

/-- The bytes of a channel record: the header fields and the buffer. -/
def chanRecordBytes : Nat := chanOffBuff + OCaml.Bytecode.ioBufferSize

/-- The remembered-set struct (`Caml_state->ref_table`, `caml_ref_table`, 7 words). -/
def refTable : Nat := Boot.WhileMinHeapChunks.refTablePayload

/-- The runtime's blocks, as `(start, bytes)`, each in one live malloc block at
the whileMin cut: the `Caml_state` record, the remembered-set struct, the
minor heap (`minorRegion`), the major heap chunk (`majorRegion`), the VM stack
`[stack_low, stack_high)`, the code buffer (`caml_load_code`'s request: whileMin's
191 words) and the primitive table's contents (`8 ×` its capacity 768). The
sizes are the blocks' requested bytes, which a0-boot's `HeapReady` records. -/
def f1Covered : List (Nat × Nat) :=
  [(Boot.WhileMinRuntime.domain, Layout.domainStateBytes), (refTable, 56),
   (minorRegion.lo, minorRegion.hi - minorRegion.lo), (majorRegion.lo, majorRegion.hi - majorRegion.lo),
   (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes),
   (Boot.WhileMinHeapChunks.codeBufferPayload, f1CodeBytes), (Boot.WhileMinHeapChunks.primTablePayload, 8 * f1PrimCapacity)]

/-- The regions F1's ordinary windows write: the `Caml_state` record around
its `minor_heap_wsz` and `ref_table` words, the minor heap, the major chunk,
the VM stack. The remembered set changes only through the write barrier's
own lemmas. -/
def f1Extents : List (Nat × Nat) :=
  [(Boot.WhileMinRuntime.domain, Layout.off_minor_heap_wsz),
   (Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz + 8,
     Layout.off_ref_table - Layout.off_minor_heap_wsz - 8),
   (Boot.WhileMinRuntime.domain + Layout.off_ref_table + 8, Layout.domainStateBytes - Layout.off_ref_table - 8),
   (minorRegion.lo, minorRegion.hi - minorRegion.lo), (majorRegion.lo, majorRegion.hi - majorRegion.lo),
   (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes)]

theorem extent_covered : ∀ x ∈ f1Extents, ∃ y ∈ f1Covered, y.1 ≤ x.1 ∧ x.1 + x.2 ≤ y.1 + y.2 := by decide

/-- The remembered set's words: the `Caml_state->ref_table` pointer, the
struct, and `Caml_state->minor_heap_wsz` (which sizes its first allocation). -/
def InTableWords (y : Nat) : Prop :=
  (Boot.WhileMinRuntime.domain + Layout.off_ref_table ≤ y ∧ y < Boot.WhileMinRuntime.domain + Layout.off_ref_table + 8) ∨
    (refTable ≤ y ∧ y < refTable + 56) ∨
    (Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz ≤ y ∧
      y < Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz + 8)

theorem extents_miss_table : ∀ x ∈ f1Extents,
    (x.1 + x.2 ≤ Boot.WhileMinRuntime.domain + Layout.off_ref_table ∨
      Boot.WhileMinRuntime.domain + Layout.off_ref_table + 8 ≤ x.1) ∧
    (x.1 + x.2 ≤ refTable ∨ refTable + 56 ≤ x.1) ∧
    (x.1 + x.2 ≤ Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz ∨
      Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz + 8 ≤ x.1) := by decide

/-- `x` lies inside a live block of `H`. -/
def Covered (H : List (Nat × Nat)) (x : Nat × Nat) : Prop :=
  ∃ e ∈ H, e.1 ≤ x.1 ∧ x.1 + x.2 ≤ e.1 + e.2

/-- A write window the F1 heap invariant tolerates, independent of the live
blocks. -/
def F1HeapSafe (w : W) : Prop :=
  (∃ x ∈ f1Extents, x.1 ≤ w.lo ∧ w.hi ≤ x.1 + x.2) ∨ heapEnd ≤ w.lo ∨
    (∀ a, w.lo ≤ a → a < w.hi → a ∈ errnoBytes) ∨
    (w.hi ≤ heapStart ∧ ∀ a, w.lo ≤ a → a < w.hi → ¬ allocGlobal a ∧ ¬ HeapPinned a)

/-- The remembered set's storage `[b, e)` with insertion pointer `p` and
limit `l` (`caml_alloc_table`: `limit = threshold ≤ end`): its own live block,
apart from the runtime's blocks and the open records. -/
structure RefStorage (H : List (Nat × Nat)) (chs : List Nat) (b e p l : Nat) : Prop where
  nonzero : b ≠ 0
  aligned : b % 8 = 0
  ptrAligned : p % 8 = 0
  limitAligned : l % 8 = 0
  low : b ≤ p
  ptrLimit : p ≤ l
  limitEnd : l ≤ e
  sized : b < e
  covered : Covered H (b, e - b)
  apartBlocks : ∀ x ∈ f1Covered, e ≤ x.1 ∨ x.1 + x.2 ≤ b
  apartRecords : ∀ a ∈ chs, e ≤ a ∨ a + chanRecordBytes ≤ b

/-- **The remembered set at an F1 state**: `Caml_state->ref_table` is the
cut's struct; the table is unallocated (as at the cut) or has its storage. -/
structure RefTableAt (H : List (Nat × Nat)) (chs : List Nat) (c : Config) : Prop where
  pointer : word c (Boot.WhileMinRuntime.domain + Layout.off_ref_table) = BitVec.ofNat 64 refTable
  /-- the minor heap's size, which sizes the table's first allocation -/
  minorWsz : word c (Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz) = 0x40000#64
  shape : ((word c (refTable + Layout.off_ref_table_base)).toNat = 0 ∧
      (word c (refTable + Layout.off_ref_table_ptr)).toNat = 0 ∧
      (word c (refTable + Layout.off_ref_table_limit)).toNat = 0) ∨
    RefStorage H chs (word c (refTable + Layout.off_ref_table_base)).toNat
      (word c (refTable + Layout.off_ref_table_end)).toNat (word c (refTable + Layout.off_ref_table_ptr)).toNat
      (word c (refTable + Layout.off_ref_table_limit)).toNat

/-- A word inside the remembered set's words survives byte equality on them. -/
theorem tableWord_keep {c c' : Config}
    (same : ∀ y, InTableWords y → (c'.σ.mem[y]?).getD 0 = (c.σ.mem[y]?).getD 0)
    {x : Nat} (h : ∀ j, j < 8 → InTableWords (x + j)) : word c' x = word c x := by
  apply Reloc.bytesT_congr
  intro j hj
  simp only [bytesT, same _ (h j hj)]

theorem structWord_keep {c c' : Config}
    (same : ∀ y, InTableWords y → (c'.σ.mem[y]?).getD 0 = (c.σ.mem[y]?).getD 0) {off : Nat} (h : off + 8 ≤ 56) :
    word c' (refTable + off) = word c (refTable + off) :=
  tableWord_keep same fun j hj => Or.inr (Or.inl ⟨by omega, by omega⟩)

/-- The remembered set survives byte equality on its words. -/
theorem RefTableAt.congr {H : List (Nat × Nat)} {chs : List Nat} {c c' : Config} (t : RefTableAt H chs c)
    (same : ∀ y, InTableWords y → (c'.σ.mem[y]?).getD 0 = (c.σ.mem[y]?).getD 0) : RefTableAt H chs c' := by
  have tw : ∀ off, off + 8 ≤ 56 → word c' (refTable + off) = word c (refTable + off) := fun off h =>
    structWord_keep same h
  refine ⟨by rw [tableWord_keep same fun j hj => Or.inl ⟨by omega, by omega⟩]; exact t.pointer,
    by rw [tableWord_keep same fun j hj => Or.inr (Or.inr ⟨by omega, by omega⟩)]; exact t.minorWsz, ?_⟩
  rw [tw _ (by decide), tw _ (by decide), tw _ (by decide), tw _ (by decide)]
  exact t.shape

/-- The C-heap charges F1 reserves after the cut: the remembered set's first
allocation (`caml_alloc_table`'s `(minor_heap_wsz/8 + 256)·8` bytes) while the
table is unallocated, and one channel record (`72 + 65536` bytes) for each of
the at most `maxChannels` channels not yet opened. Each covers newlib's
charge for that request (`vsaChg`). -/
def tableCharge : Nat := 2 ^ 19
def recordCharge : Nat := 2 ^ 17
def maxChannels : Nat := 64

def reserved (base opened : Nat) : Nat :=
  (if base = 0 then tableCharge else 0) + recordCharge * (maxChannels - opened)

/-- **newlib's heap at an F1 state**, with live blocks `H` and open channels `chs`. -/
structure LibHeapAt (H : List (Nat × Nat)) (cap : Nat) (chs : List Nat) (c : Config) : Prop where
  /-- the room still covers every allocation F1 may make -/
  room : reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length ≤ cap
  channelsBound : chs.length ≤ maxChannels
  ready : HeapReady H cap c
  extents : ∀ x ∈ f1Covered, Covered H x
  channels : OpenChannelList c.σ.mem chs
  records : ∀ a ∈ chs, Covered H (a, chanRecordBytes)
  recordsApart : ∀ a ∈ chs, ∀ x ∈ f1Covered, a + chanRecordBytes ≤ x.1 ∨ x.1 + x.2 ≤ a
  /-- distinct open records are disjoint (each its own malloc block) -/
  recordsDisjoint : ∀ a ∈ chs, ∀ b ∈ chs, a ≠ b → a + chanRecordBytes ≤ b ∨ b + chanRecordBytes ≤ a
  /-- the remembered set -/
  table : RefTableAt H chs c
  /-- its struct is a live block verbatim (the barrier's growth path frees
  nothing and reads it as `(tbl, tableBytes) ∈ H`) -/
  tableIn : (refTable, 56) ∈ H

/-- The F1 heap invariant. -/
def LibHeap (c : Config) : Prop := ∃ H cap chs, LibHeapAt H cap chs c

theorem F1HeapSafe.heapSafe {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {w : W} (s : F1HeapSafe w) : HeapSafe H w := by
  rcases s with ⟨x, hx, lo, hi⟩ | s | s | s
  · obtain ⟨y, hy, ylo, yhi⟩ := extent_covered x hx
    obtain ⟨e, he, elo, ehi⟩ := h.extents y hy
    exact Or.inl ⟨e, he, by omega, by omega⟩
  · exact Or.inr (Or.inl s)
  · exact Or.inr (Or.inr (Or.inl s))
  · exact Or.inr (Or.inr (Or.inr s))

/-- A safe window misses every open channel record. -/
theorem F1HeapSafe.outside {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {w : W} (s : F1HeapSafe w) {a : Nat} (ha : a ∈ chs) {y : Nat}
    (lo : a ≤ y) (hi : y < a + chanRecordBytes) : y < w.lo ∨ w.hi ≤ y := by
  obtain ⟨e, he, elo, ehi⟩ := h.records a ha
  have bounds := h.ready.block_bounds he
  dsimp only at elo ehi
  rcases Nat.lt_or_ge y w.lo with l | l
  · exact Or.inl l
  rcases Nat.lt_or_ge y w.hi with g | g
  · exfalso
    rcases s with ⟨x, hx, xlo, xhi⟩ | s | s | ⟨s, _⟩
    · obtain ⟨z, hz, zlo, zhi⟩ := extent_covered x hx
      rcases h.recordsApart a ha z hz with r | r <;> omega
    · omega
    · have := errnoBytes_mem.1 (s y l g)
      unfold InRange heapStart at *
      omega
    · omega
  · exact Or.inr g

/-- A safe window misses the remembered set's words. -/
theorem F1HeapSafe.misses_table {w : W} (s : F1HeapSafe w) {y : Nat} (hy : InTableWords y) :
    y < w.lo ∨ w.hi ≤ y := by
  have yr : 0x8007d140 ≤ y ∧ y < 0x86800000 := by
    unfold InTableWords refTable at hy
    simp only [Boot.WhileMinRuntime.domain, Layout.off_ref_table, Layout.off_minor_heap_wsz,
      Boot.WhileMinHeapChunks.refTablePayload] at hy
    omega
  rcases Nat.lt_or_ge y w.lo with l | l
  · exact Or.inl l
  rcases Nat.lt_or_ge y w.hi with g | g
  · exfalso
    rcases s with ⟨x, hx, xlo, xhi⟩ | s | s | ⟨s, _⟩
    · have := extents_miss_table x hx
      unfold InTableWords at hy
      omega
    · unfold heapEnd at s; omega
    · have := errnoBytes_mem.1 (s y l g); unfold InRange at this; omega
    · unfold heapStart at s; omega
  · exact Or.inr g

/-- **The F1 heap invariant survives writes confined to safe windows**, given
byte equality outside them and an unchanged open-channel list head. -/
theorem LibHeapAt.keep_windows {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT c'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (keep : ∀ a, (∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a) → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) :
    LibHeapAt H cap chs c' where
  room := by rw [structWord_keep (fun y hy => keep y fun w hw => (safe w hw).misses_table hy) (by decide)]; exact h.room
  channelsBound := h.channelsBound
  ready := HeapReady.keep_windows h.ready (fun w hw => (safe w hw).heapSafe h) keep
  extents := h.extents
  channels := by
    unfold OpenChannelList
    rw [head]
    refine OpenChannels.congr h.channels fun a ha => ?_
    apply Reloc.bytesT_congr
    intro j hj
    have same := keep (a + chanOffNext + j) fun w hw =>
      (safe w hw).outside h ha (by omega) (by unfold chanOffNext chanRecordBytes chanOffBuff at *; omega)
    simp only [bytesT, same]
  records := h.records
  recordsApart := h.recordsApart
  recordsDisjoint := h.recordsDisjoint
  tableIn := h.tableIn
  table := h.table.congr fun y hy => keep y fun w hw => (safe w hw).misses_table hy

/-- `LibHeapAt.keep_windows` for a frame. -/
theorem LibHeapAt.frame_windows {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT c'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (frame : FrameOn ws c.σ.mem c'.σ.mem) : LibHeapAt H cap chs c' :=
  h.keep_windows safe head fun a out => by rw [frame a (outW_all out)]

/-- `a` is a record on the memory's open-channel list. -/
def OpenAt (c : Config) (a : Nat) : Prop := ∃ chs, OpenChannelList c.σ.mem chs ∧ a ∈ chs

theorem LibHeapAt.open_mem {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {a : Nat} (o : OpenAt c a) : a ∈ chs := by
  obtain ⟨chs', list, mem⟩ := o
  rw [OpenChannels.unique h.channels list]
  exact mem

/-- A write window inside the open record at `a` that misses its `next` word. -/
def RecordWindow (a : Nat) (w : W) : Prop :=
  a ≤ w.lo ∧ w.hi ≤ a + chanRecordBytes ∧ (w.hi ≤ a + chanOffNext ∨ a + chanOffNext + 8 ≤ w.lo)

/-- An open record misses the remembered set's words. -/
theorem RecordWindow.misses_table {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {a : Nat} (ha : a ∈ chs) {w : W} (r : RecordWindow a w) {y : Nat}
    (hy : InTableWords y) : y < w.lo ∨ w.hi ≤ y := by
  obtain ⟨lo, hi, -⟩ := r
  have d := h.recordsApart a ha _ (List.mem_cons_self (a := (Boot.WhileMinRuntime.domain, Layout.domainStateBytes)))
  have t := h.recordsApart a ha (refTable, 56) (by decide)
  unfold InTableWords at hy
  simp only [Layout.domainStateBytes, Layout.off_ref_table, Layout.off_minor_heap_wsz] at d hy ⊢
  omega

/-- **The F1 heap invariant survives writes to one open record** (missing its
`next` word) together with safe windows. -/
theorem LibHeapAt.keep_records {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) {a : Nat} (ha : a ∈ chs) {ws : List W}
    (safe : ∀ w ∈ ws, F1HeapSafe w ∨ RecordWindow a w)
    (head : bytesT c'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (keep : ∀ x, (∀ w ∈ ws, x < w.lo ∨ w.hi ≤ x) → (c'.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0) :
    LibHeapAt H cap chs c' where
  room := by
    rw [structWord_keep (fun y hy => keep y fun w hw => by
      rcases safe w hw with s | r
      · exact s.misses_table hy
      · exact r.misses_table h ha hy) (by decide)]
    exact h.room
  channelsBound := h.channelsBound
  ready := HeapReady.keep_windows h.ready (fun w hw => by
    rcases safe w hw with s | ⟨lo, hi, _⟩
    · exact s.heapSafe h
    · obtain ⟨e, he, elo, ehi⟩ := h.records a ha
      dsimp only at elo ehi
      exact Or.inl ⟨e, he, by omega, by omega⟩) keep
  extents := h.extents
  channels := by
    unfold OpenChannelList
    rw [head]
    refine OpenChannels.congr h.channels fun b hb => ?_
    apply Reloc.bytesT_congr
    intro j hj
    have same := keep (b + chanOffNext + j) fun w hw => by
      rcases safe w hw with s | ⟨lo, hi, next⟩
      · exact s.outside h hb (by omega) (by unfold chanOffNext chanRecordBytes chanOffBuff at *; omega)
      · by_cases e : b = a
        · subst e; omega
        · have := h.recordsDisjoint b hb a ha e
          unfold chanOffNext chanRecordBytes chanOffBuff at *
          omega
    simp only [bytesT, same]
  records := h.records
  recordsApart := h.recordsApart
  recordsDisjoint := h.recordsDisjoint
  tableIn := h.tableIn
  table := h.table.congr fun y hy => keep y fun w hw => by
    rcases safe w hw with s | r
    · exact s.misses_table hy
    · exact r.misses_table h ha hy

end OCaml.Vm.Gc

namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Boot.Startup VsaIris.VsaHeap

/-- A range inside a live block of `H` misses a fresh block disjoint from `H`. -/
theorem fresh_apart_covered {H : List (Nat × Nat)} {p r : Nat}
    (fresh : ∀ e ∈ H, ∀ y, VsaIris.InExt (p, r) y → ¬ VsaIris.InExt e y) {x : Nat × Nat} (cov : Covered H x)
    (pos : 0 < x.2) {n : Nat} (npos : 0 < n) (small : n ≤ r) : p + n ≤ x.1 ∨ x.1 + x.2 ≤ p := by
  obtain ⟨e, he, lo, hi⟩ := cov
  rcases Nat.lt_or_ge x.1 (p + n) with l | l
  · rcases Nat.lt_or_ge p (x.1 + x.2) with g | g
    · exfalso
      rcases Nat.le_total p x.1 with o | o
      · have i1 : VsaIris.InExt (p, r) x.1 := ⟨o, by dsimp only; omega⟩
        have i2 : VsaIris.InExt e x.1 := ⟨lo, by omega⟩
        exact fresh e he x.1 i1 i2
      · have i1 : VsaIris.InExt (p, r) p := ⟨Nat.le_refl _, by dsimp only; omega⟩
        have i2 : VsaIris.InExt e p := ⟨by omega, by omega⟩
        exact fresh e he p i1 i2
    · exact Or.inr g
  · exact Or.inl l

theorem covered_pos : ∀ x ∈ f1Covered, 0 < x.2 := by decide

theorem record_pos : 0 < chanRecordBytes := by decide

theorem Covered.mono {H : List (Nat × Nat)} {x : Nat × Nat} (h : Covered H x) (e : Nat × Nat) :
    Covered (e :: H) x := by
  obtain ⟨f, hf, lo, hi⟩ := h
  exact ⟨f, List.mem_cons_of_mem _ hf, lo, hi⟩

/-- **Opening a channel keeps the F1 heap invariant** (`caml_ml_open_descriptor_*`):
the record `a` is a fresh malloc block of at least `chanRecordBytes`, linked at
the list head; newlib's charge fits one record's reservation; the remembered
set's words and the open records' links are unchanged. -/
theorem LibHeapAt.link {H : List (Nat × Nat)} {cap cap' charge : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) {a req : Nat}
    (bound : chs.length < maxChannels)
    (ready : HeapReady ((a, req) :: H) cap' c') (spend : cap = cap' + charge) (charged : charge ≤ recordCharge)
    (big : chanRecordBytes ≤ req)
    (fresh : ∀ e ∈ H, ∀ y, VsaIris.InExt (a, req) y → ¬ VsaIris.InExt e y)
    (linked : OpenChannelsLinked c.σ.mem c'.σ.mem a)
    (keepTable : ∀ y, InTableWords y → (c'.σ.mem[y]?).getD 0 = (c.σ.mem[y]?).getD 0)
    (keepLinks : ∀ b ∈ chs, bytesT c'.σ.mem (b + chanOffNext) 8 = bytesT c.σ.mem (b + chanOffNext) 8) :
    LibHeapAt ((a, req) :: H) cap' (a :: chs) c' where
  room := by
    rw [structWord_keep keepTable (by decide)]
    have r := h.room
    have key : ∀ X n : Nat, n < maxChannels → X + recordCharge * (maxChannels - n) ≤ cap' + charge →
        X + recordCharge * (maxChannels - (n + 1)) ≤ cap' := by
      intro X n hn hr
      simp only [maxChannels, recordCharge] at *
      omega
    simp only [reserved, List.length_cons] at r ⊢
    rw [spend] at r
    exact key _ _ bound r
  channelsBound := by simp only [List.length_cons]; omega
  ready := ready
  extents := fun x hx => (h.extents x hx).mono _
  channels := by
    unfold OpenChannelList
    rw [linked.head, BitVec.toNat_ofNat]
    have aSmall : a < 2 ^ 64 := by
      have := ready.block_bounds List.mem_cons_self
      simp only [heapEnd] at this; omega
    rw [Nat.mod_eq_of_lt aSmall]
    refine .cons linked.nonzero ?_
    rw [linked.next]
    exact OpenChannels.congr h.channels keepLinks
  records := by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨(b, req), List.mem_cons_self, Nat.le_refl _, by dsimp only; omega⟩
    · exact (h.records b hb).mono _
  recordsApart := by
    intro b hb x hx
    rcases List.mem_cons.1 hb with rfl | hb
    · exact fresh_apart_covered fresh (h.extents x hx) (covered_pos x hx) record_pos big
    · exact h.recordsApart b hb x hx
  recordsDisjoint := by
    intro b hb d hd ne
    rcases List.mem_cons.1 hb with eb | hb' <;> rcases List.mem_cons.1 hd with ed | hd'
    · exact absurd (eb.trans ed.symm) ne
    · subst eb
      rcases fresh_apart_covered fresh (h.records d hd') record_pos record_pos big with o | o
      · exact Or.inl o
      · exact Or.inr o
    · subst ed
      rcases fresh_apart_covered fresh (h.records b hb') record_pos record_pos big with o | o
      · exact Or.inr o
      · exact Or.inl o
    · exact h.recordsDisjoint b hb' d hd' ne
  table := by
    have t := h.table.congr keepTable
    refine ⟨t.pointer, t.minorWsz, ?_⟩
    rcases t.shape with u | st
    · exact Or.inl u
    · refine Or.inr { st with covered := st.covered.mono _, apartRecords := fun b hb => ?_ }
      rcases List.mem_cons.1 hb with rfl | hb
      · rcases fresh_apart_covered fresh st.covered (by have := st.sized; dsimp only; omega) record_pos big with o | o
        · have := st.limitEnd; have := st.ptrLimit; have := st.low
          dsimp only at o
          exact Or.inr (by omega)
        · dsimp only at o
          exact Or.inl (by have := st.limitEnd; have := st.ptrLimit; have := st.low; omega)
      · exact st.apartRecords b hb
  tableIn := List.mem_cons_of_mem _ h.tableIn

end OCaml.Vm.Gc
