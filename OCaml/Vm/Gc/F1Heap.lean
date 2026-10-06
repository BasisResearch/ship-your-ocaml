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

/-- The runtime regions F1 writes, as `(start, bytes)`, each in one live
malloc block at the whileMin cut:
* the `Caml_state` record;
* the remembered-set struct (`Caml_state->ref_table`, 7 words);
* the minor heap `[young_start, young_end)` (`minorRegion`);
* the major heap chunk (`majorRegion`);
* the VM stack `[stack_low, stack_high)`. -/
def f1Extents : List (Nat × Nat) :=
  [(Boot.WhileMinRuntime.domain, Layout.domainStateBytes), (Boot.WhileMinHeapChunks.refTablePayload, 56),
   (minorRegion.lo, minorRegion.hi - minorRegion.lo), (majorRegion.lo, majorRegion.hi - majorRegion.lo),
   (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes)]

/-- `x` lies inside a live block of `H`. -/
def Covered (H : List (Nat × Nat)) (x : Nat × Nat) : Prop :=
  ∃ e ∈ H, e.1 ≤ x.1 ∧ x.1 + x.2 ≤ e.1 + e.2

/-- A write window the F1 heap invariant tolerates, independent of the live
blocks. -/
def F1HeapSafe (w : W) : Prop :=
  (∃ x ∈ f1Extents, x.1 ≤ w.lo ∧ w.hi ≤ x.1 + x.2) ∨ heapEnd ≤ w.lo ∨
    (∀ a, w.lo ≤ a → a < w.hi → a ∈ errnoBytes) ∨
    (w.hi ≤ heapStart ∧ ∀ a, w.lo ≤ a → a < w.hi → ¬ allocGlobal a ∧ ¬ HeapPinned a)

/-- **newlib's heap at an F1 state**, with live blocks `H` and open channels `chs`. -/
structure LibHeapAt (H : List (Nat × Nat)) (cap : Nat) (chs : List Nat) (c : Config) : Prop where
  room : 2 ^ 24 ≤ cap
  ready : HeapReady H cap c
  extents : ∀ x ∈ f1Extents, Covered H x
  channels : OpenChannelList c.σ.mem chs
  records : ∀ a ∈ chs, Covered H (a, chanRecordBytes)
  recordsApart : ∀ a ∈ chs, ∀ x ∈ f1Extents, a + chanRecordBytes ≤ x.1 ∨ x.1 + x.2 ≤ a
  /-- distinct open records are disjoint (each its own malloc block) -/
  recordsDisjoint : chs.Pairwise fun a b => a + chanRecordBytes ≤ b ∨ b + chanRecordBytes ≤ a

/-- The F1 heap invariant. -/
def LibHeap (c : Config) : Prop := ∃ H cap chs, LibHeapAt H cap chs c

theorem F1HeapSafe.heapSafe {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {w : W} (s : F1HeapSafe w) : HeapSafe H w := by
  rcases s with ⟨x, hx, lo, hi⟩ | s | s | s
  · obtain ⟨e, he, elo, ehi⟩ := h.extents x hx
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
    · rcases h.recordsApart a ha x hx with r | r <;> omega
    · omega
    · have := errnoBytes_mem.1 (s y l g)
      unfold InRange heapStart at *
      omega
    · omega
  · exact Or.inr g

/-- Equal `next` words keep the open-channel list. -/
theorem OpenChannels.congr {m m' : Std.ExtHashMap Nat (BitVec 8)} {x : Nat} {chs : List Nat}
    (h : OpenChannels m x chs) (same : ∀ a ∈ chs, bytesT m' (a + chanOffNext) 8 = bytesT m (a + chanOffNext) 8) :
    OpenChannels m' x chs := by
  -- discipline: allow(O5-run-induction) `OpenChannels` is the shape of one linked list in a fixed memory, not a run relation
  induction h with
  | nil => exact .nil
  | @cons a chs ne _ ih =>
    refine .cons ne ?_
    rw [same a List.mem_cons_self]
    exact ih fun b hb => same b (List.mem_cons_of_mem _ hb)

/-- **The F1 heap invariant survives writes confined to safe windows**, given
byte equality outside them and an unchanged open-channel list head. -/
theorem LibHeapAt.keep_windows {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT c'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (keep : ∀ a, (∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a) → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) :
    LibHeapAt H cap chs c' where
  room := h.room
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

/-- `LibHeapAt.keep_windows` for a frame. -/
theorem LibHeapAt.frame_windows {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT c'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (frame : FrameOn ws c.σ.mem c'.σ.mem) : LibHeapAt H cap chs c' :=
  h.keep_windows safe head fun a out => by rw [frame a (outW_all out)]

end OCaml.Vm.Gc
