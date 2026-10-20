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

/-- `m'` agrees with `m` at `a`: the same total read, and a present byte stays
present with its value. -/
def Agree (m m' : Mem) (a : Nat) : Prop :=
  (m'[a]?).getD 0 = (m[a]?).getD 0 ∧ ∀ b, m[a]? = some b → m'[a]? = some b

theorem agree_of_eq {m m' : Mem} {a : Nat} (h : m'[a]? = m[a]?) : Agree m m' a :=
  ⟨by rw [h], fun b hb => by rw [h, hb]⟩

/-- A total read and persistent presence give agreement. -/
theorem agree_of_getD {m m' : Mem} {a : Nat} (same : (m'[a]?).getD 0 = (m[a]?).getD 0)
    (present : (m[a]?).isSome → (m'[a]?).isSome) : Agree m m' a := by
  refine ⟨same, fun b hb => ?_⟩
  have p := present (by rw [hb]; rfl)
  revert same p
  rw [hb]
  cases m'[a]? with
  | none => intro _ p; cases p
  | some b' => intro same _; simp only [Option.getD_some] at same; rw [same]

/-- A C string survives memory that keeps its bytes. -/
theorem _root_.Vsa.MemRepr.CStr.transport {m m' : Mem} {a : Nat} {cs : List Char} (h : CStr m a cs)
    (same : ∀ i, i ≤ cs.length → ∀ b, m[a + i]? = some b → m'[a + i]? = some b) : CStr m' a cs := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h with
  | nil z => exact .nil (same 0 (Nat.le_refl _) _ (by rw [Nat.add_zero]; exact z))
  | @cons a b cs hb ne lt _ ih =>
    refine .cons (by have := same 0 (Nat.zero_le _) b (by rw [Nat.add_zero]; exact hb); rwa [Nat.add_zero] at this)
      ne lt (ih fun i hi b' hb' => ?_)
    have := same (i + 1) (by simp only [List.length_cons]; omega) b' (by rwa [show a + (i + 1) = a + 1 + i by omega])
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

/-- The bytes a node and its key occupy. -/
def NodeBytes (node : BitVec 64) (key : List (BitVec 8)) (a : Nat) : Prop :=
  node.toNat ≤ a ∧ a < node.toNat + 16 + key.length + 1

/-- A node survives memory that agrees on its bytes. -/
theorem NodeAt.transport {m m' : Mem} {pl : Place} {node next : BitVec 64} {key : List (BitVec 8)} {v : Val}
    (h : NodeAt m pl node next key v) (agree : ∀ a, NodeBytes node key a → Agree m m' a) :
    NodeAt m' pl node next key v := by
  have arena := h.arena
  have heapEnd : Vsa.Sim.DlHeap.heapEnd < 2 ^ 64 := by decide
  have off (k : Nat) (hk : k ≤ 16) : (node + BitVec.ofNat 64 k).toNat = node.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have word (a : Nat) (lo : node.toNat ≤ a) (ha : a + 8 ≤ node.toNat + 16) : bytesT m' a 8 = bytesT m a 8 :=
    word_observed a fun i hi => (agree _ ⟨by omega, by omega⟩).1
  have lenOf (cs : List Char) (e : strOf key = String.ofList cs) : cs.length = key.length := by
    have := congrArg String.length e
    rw [strOf_length, String.length_ofList] at this
    exact this.symm
  have strSame (cs : List Char) (len : cs.length = key.length) :
      ∀ i, i ≤ cs.length → ∀ b, m[(node + 16#64).toNat + i]? = some b → m'[(node + 16#64).toNat + i]? = some b :=
    fun i hi => (agree _ ⟨by rw [off 16 (by decide)]; omega, by rw [off 16 (by decide)]; omega⟩).2
  refine ⟨h.nonnull, ?_, ?_, h.nextWindow, ?_, ?_, h.arena⟩
  · rw [word _ (Nat.le_refl _) (by omega)]; exact h.value
  · rw [read8_value, off 8 (by decide), word _ (by omega) (by omega), ← off 8 (by decide), ← read8_value]; exact h.next
  · obtain ⟨cs, str, e⟩ := h.name
    exact ⟨cs, str.transport (strSame cs (lenOf cs e)), e⟩
  · intro cs str
    obtain ⟨cs0, str0, e⟩ := h.name
    -- the string at the node is determined: its length is the key's
    have eq : cs0 = cs := (str0.transport (strSame cs0 (lenOf cs0 e))).unique str
    subst eq
    exact h.slack cs0 str0

/-- A bucket's chain survives memory that agrees on its nodes' bytes. -/
theorem TableChain.transport {m m' : Mem} {pl : Place} {head : BitVec 64}
    {nodes : List (BitVec 64 × List (BitVec 8) × Val)} (h : TableChain m pl head nodes)
    (agree : ∀ e ∈ nodes, ∀ a, NodeBytes e.1 e.2.1 a → Agree m m' a) : TableChain m' pl head nodes := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h with
  | nil => exact .nil
  | cons node _ ih =>
    exact .cons (node.transport (agree _ List.mem_cons_self)) (ih fun e he => agree e (List.mem_cons_of_mem _ he))

/-- A chain's nodes lie below `heapEnd`. -/
theorem TableChain.arena {m : Mem} {pl : Place} {head : BitVec 64}
    {nodes : List (BitVec 64 × List (BitVec 8) × Val)} (h : TableChain m pl head nodes) :
    ∀ e ∈ nodes, e.1.toNat + 16 + e.2.1.length + 1 ≤ Vsa.Sim.DlHeap.heapEnd := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h with
  | nil => intro e he; cases he
  | cons node _ ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact node.arena
    · exact ih e he

/-- The bytes the table occupies: its bucket array and its nodes. -/
def TableFoot (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)) (a : Nat) : Prop :=
  (Layout.sym_named_value_table ≤ a ∧ a < Layout.sym_named_value_table + 104) ∨
    ∃ b, b < 13 ∧ ∃ e ∈ chains b, NodeBytes e.1 e.2.1 a

/-- **The table survives memory that agrees on its bytes**, given the code
facts in the new memory (`strcmp_loaded`, `mask_pinned`). -/
theorem TableShape.transport {m m' : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : TableShape m pl named chains)
    (agree : ∀ a, TableFoot chains a → Agree m m' a) (code : Code.StrcmpLoaded m')
    (mask : MaskPinned m') : TableShape m' pl named chains where
  window := h.window
  heads := fun b hb => by
    have head : bytesVal .ld (read8 m' (bucketAddr b).toNat) = bytesVal .ld (read8 m (bucketAddr b).toNat) := by
      rw [read8_value, read8_value]
      apply word_observed
      intro i hi
      apply (agree _ (Or.inl _)).1
      simp only [bucketAddr, BitVec.toNat_ofNat, Layout.sym_named_value_table]
      omega
    rw [head]
    exact (h.heads b hb).transport fun e he a ha => agree a (Or.inr ⟨b, hb, e, he, ha⟩)
  placed := h.placed
  entries := h.entries
  unique := h.unique
  code := code
  mask := mask

/-- The table across memory that agrees exactly on its bytes below `heapEnd`. -/
theorem TableShape.transport_below {m m' : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : TableShape m pl named chains)
    (same : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → TableFoot chains a → m'[a]? = m[a]?) (code : Code.StrcmpLoaded m')
    (mask : MaskPinned m') : TableShape m' pl named chains :=
  h.transport (fun a foot => agree_of_eq (same a (by
    rcases foot with ⟨-, hi⟩ | ⟨b, hb, e, he, lo, hi⟩
    · simp only [Layout.sym_named_value_table, Vsa.Sim.DlHeap.heapEnd] at hi ⊢; omega
    · have := (h.heads b hb).arena e he; omega) foot)) code mask

/-- The table across memory that agrees exactly below `heapEnd`. -/
theorem TableShape.transport_low {m m' : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : TableShape m pl named chains)
    (same : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → m'[a]? = m[a]?) (code : Code.StrcmpLoaded m')
    (mask : MaskPinned m') : TableShape m' pl named chains :=
  h.transport_below (fun a ha _ => same a ha) code mask

/-- A chain's member is a node of it. -/
theorem TableChain.node_of_mem {m : Mem} {pl : Place} {head : BitVec 64}
    {nodes : List (BitVec 64 × List (BitVec 8) × Val)} (h : TableChain m pl head nodes) :
    ∀ e ∈ nodes, ∃ next, NodeAt m pl e.1 next e.2.1 e.2.2 := by
  -- discipline: allow(O5-run-induction) induction on a C string / chain of heap nodes, not a run relation
  induction h with
  | nil => intro e he; cases he
  | cons node _ ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, node⟩
    · exact ih e he

/-- **A table entry's value slot** represents its value. -/
theorem TableShape.value_of_mem {m : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : TableShape m pl named chains)
    {b : Nat} (hb : b < 13) {e : BitVec 64 × List (BitVec 8) × Val} (he : e ∈ chains b) :
    valWord pl e.2.2 = some (bytesT m e.1.toNat 8) := by
  obtain ⟨_, node⟩ := (h.heads b hb).node_of_mem e he
  exact node.value

end OCaml.Vm.Primitives.Named.NamedValue