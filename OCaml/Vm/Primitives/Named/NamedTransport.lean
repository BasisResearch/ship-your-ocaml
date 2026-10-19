import OCaml.Vm.Primitives.Named.NamedTable

/-!
# The named-value table across memory that keeps the arena

Everything `TableShape` reads lies below `heapEnd`: the bucket array
(`.bss`), the nodes and their keys (malloc'd, `NodeAt.arena`), `strcmp`'s code
and its mask word (`.text`, `.rodata`). So the table survives any run whose
memory agrees exactly below `heapEnd` (`TableShape.transport`), for example
native frame stores. `strcmp_loaded` and `mask_pinned` give the code facts from
the image alone.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Bytecode OCaml.Vm.Primitives OCaml.Vm.Boot.Startup OCaml.Vm.Sim

/-- Fixed image bytes survive memory that agrees on them. -/
theorem fixedBytes_transport {base size : Nat} {byte : Nat → BitVec 8} {m m' : Mem}
    (h : Vsa.Sim.Code.FixedBytesLoaded base size byte m) (same : ∀ a, a < base + size → m'[a]? = m[a]?) :
    Vsa.Sim.Code.FixedBytesLoaded base size byte m' :=
  fun off lt => (same _ (by omega)).trans (h off lt)

/-- One byte of a fixed image section. -/
theorem fixed_byte {base size : Nat} {byte : Nat → BitVec 8} {m : Mem}
    (fixed : Vsa.Sim.Code.FixedBytesLoaded base size byte m) {a : Nat} {b : BitVec 8}
    (h : base ≤ a ∧ a - base < size ∧ byte (a - base) = b) : m[a]? = some b := by
  obtain ⟨lo, hi, v⟩ := h
  have := fixed (a - base) hi
  rwa [Nat.add_sub_cancel' lo, v] at this

/-- `strcmp`'s code is the image's `.text`. -/
theorem strcmp_loaded_of {m : Mem} (text : Vsa.Sim.Code.FixedBytesLoaded Image.textBase Image.textSize Image.textByte m) :
    Code.StrcmpLoaded m := by
  unfold Code.StrcmpLoaded Code.strcmpChunk0 Code.strcmpChunk1 Code.strcmpChunk2 Code.strcmpChunk3
    Code.strcmpChunk4
  repeat' apply And.intro
  all_goals exact fixed_byte text (by decide +kernel)

/-- `strcmp`'s mask word is the image's `.rodata`. -/
theorem mask_pinned_of {m : Mem}
    (rodata : Vsa.Sim.Code.FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte m) : MaskPinned m := by
  unfold MaskPinned
  repeat' apply And.intro
  all_goals exact fixed_byte rodata (by decide +kernel)

theorem strcmp_loaded {c : Config} (image : ExecutableImage c) : Code.StrcmpLoaded c.σ.mem :=
  strcmp_loaded_of image.text

theorem mask_pinned {c : Config} (image : ExecutableImage c) : MaskPinned c.σ.mem :=
  mask_pinned_of image.rodata

/-- A C string survives memory that agrees on its bytes. -/
theorem _root_.Vsa.MemRepr.CStr.transport {m m' : Mem} {a : Nat} {cs : List Char} (h : CStr m a cs)
    (same : ∀ i, i ≤ cs.length → m'[a + i]? = m[a + i]?) : CStr m' a cs := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h with
  | nil z => exact .nil (by have := same 0 (Nat.le_refl _); rw [Nat.add_zero] at this; rw [this]; exact z)
  | @cons a b cs hb ne lt _ ih =>
    refine .cons (by have := same 0 (Nat.zero_le _); rw [Nat.add_zero] at this; rw [this]; exact hb) ne lt
      (ih fun i hi => ?_)
    have := same (i + 1) (by simp only [List.length_cons]; omega)
    rwa [show a + (i + 1) = a + 1 + i by omega] at this

/-- A C string at an address is determined by memory. -/
theorem _root_.Vsa.MemRepr.CStr.unique {m : Mem} {a : Nat} {cs ds : List Char} (h : CStr m a cs) (g : CStr m a ds) : cs = ds := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h generalizing ds with
  | nil z =>
    cases g with
    | nil _ => rfl
    | cons hb ne _ _ => rw [z] at hb; cases hb; exact absurd rfl ne
  | cons hb ne _ _ ih =>
    cases g with
    | nil z => rw [z] at hb; cases hb; exact absurd rfl ne
    | cons hb' _ _ rest => rw [hb] at hb'; cases hb'; rw [ih rest]

theorem strOf_length (key : List (BitVec 8)) : (strOf key).length = key.length := by
  simp [strOf]

/-- A node survives memory that agrees below `heapEnd`. -/
theorem NodeAt.transport {m m' : Mem} {pl : Place} {node next : BitVec 64} {key : List (BitVec 8)} {v : Val}
    (h : NodeAt m pl node next key v) (same : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → m'[a]? = m[a]?) :
    NodeAt m' pl node next key v := by
  have arena := h.arena
  have heapEnd : Vsa.Sim.DlHeap.heapEnd < 2 ^ 64 := by decide
  have off (k : Nat) (hk : k ≤ 16) : (node + BitVec.ofNat 64 k).toNat = node.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have getD (a : Nat) (ha : a < Vsa.Sim.DlHeap.heapEnd) : (m'[a]?).getD 0 = (m[a]?).getD 0 := by rw [same a ha]
  have word (a : Nat) (ha : a + 8 ≤ Vsa.Sim.DlHeap.heapEnd) : bytesT m' a 8 = bytesT m a 8 :=
    word_observed a fun i hi => getD _ (by omega)
  have strSame (cs : List Char) (len : cs.length = key.length) :
      ∀ i, i ≤ cs.length → m'[(node + 16#64).toNat + i]? = m[(node + 16#64).toNat + i]? :=
    fun i hi => same _ (by rw [off 16 (by decide)]; omega)
  have lenOf (cs : List Char) (e : strOf key = String.ofList cs) : cs.length = key.length := by
    have := congrArg String.length e
    rw [strOf_length, String.length_ofList] at this
    exact this.symm
  refine ⟨h.nonnull, ?_, ?_, h.nextWindow, ?_, ?_, h.arena⟩
  · rw [word _ (by omega)]; exact h.value
  · rw [read8_value, off 8 (by decide), word _ (by omega), ← off 8 (by decide), ← read8_value]; exact h.next
  · obtain ⟨cs, str, e⟩ := h.name
    exact ⟨cs, str.transport (strSame cs (lenOf cs e)), e⟩
  · intro cs str
    obtain ⟨cs0, str0, e⟩ := h.name
    -- the string at the node is determined: its length is the key's
    have eq : cs0 = cs := (str0.transport (strSame cs0 (lenOf cs0 e))).unique str
    subst eq
    exact h.slack cs0 str0

/-- A bucket's chain survives memory that agrees below `heapEnd`. -/
theorem TableChain.transport {m m' : Mem} {pl : Place} {head : BitVec 64}
    {nodes : List (BitVec 64 × List (BitVec 8) × Val)} (h : TableChain m pl head nodes)
    (same : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → m'[a]? = m[a]?) : TableChain m' pl head nodes := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h with
  | nil => exact .nil
  | cons node _ ih => exact .cons (node.transport same) ih

/-- **The table survives memory that agrees below `heapEnd`**, given the code
facts in the new memory (`strcmp_loaded`, `mask_pinned`). -/
theorem TableShape.transport {m m' : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : TableShape m pl named chains)
    (same : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → m'[a]? = m[a]?) (code : Code.StrcmpLoaded m')
    (mask : MaskPinned m') : TableShape m' pl named chains where
  window := h.window
  heads := fun b hb => by
    have head : bytesVal .ld (read8 m' (bucketAddr b).toNat) = bytesVal .ld (read8 m (bucketAddr b).toNat) := by
      rw [read8_value, read8_value]
      apply word_observed
      intro i hi
      rw [same _ ?_]
      simp only [bucketAddr, BitVec.toNat_ofNat, Layout.sym_named_value_table, Vsa.Sim.DlHeap.heapEnd]
      omega
    rw [head]
    exact (h.heads b hb).transport same
  placed := h.placed
  entries := h.entries
  unique := h.unique
  code := code
  mask := mask

end OCaml.Vm.Primitives.Named.NamedValue
