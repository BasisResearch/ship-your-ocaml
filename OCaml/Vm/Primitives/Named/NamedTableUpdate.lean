import OCaml.Vm.Primitives.Named.NamedTransport
import OCaml.Bytecode.NamedValues

/-!
# The named-value table across `caml_register_named_value`

`TableShape` reads the bucket array and, per node, its value and next words
and its key with the NUL (`TableFoot`); memory that agrees there keeps the
table (`TableShape.transport`). `TableBlocks H chains` records what the C
table maintains beyond `TableShape`: keys are distinct within a bucket, and
the nodes are pairwise apart, in the arena, inside live malloc blocks of `H`.

The register's two outcomes on the model's `registerNamedValue`:
* `TableShape.update`: the node of a present key gets the new value word;
* `TableShape.insert`: an absent key's fresh node is linked at its bucket's head.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Bytecode OCaml.Vm.Primitives OCaml.Vm.Boot.Startup OCaml.Vm.Sim

/-- A node of a bucket chain: address, key bytes, value. -/
abbrev Entry := BitVec 64 × List (BitVec 8) × Val

/-- **What the C table keeps beyond `TableShape`**: keys distinct within a
bucket, the nodes in the arena, pairwise apart, each inside a live malloc
block of `H`. -/
structure TableBlocks (H : List (Nat × Nat)) (chains : Nat → List Entry) : Prop where
  keys : ∀ b, b < 13 → ((chains b).map fun e => e.2.1).Nodup
  low : ∀ b, b < 13 → ∀ e ∈ chains b, Vsa.Sim.DlHeap.heapStart ≤ e.1.toNat
  apart : ∀ b b', b < 13 → b' < 13 → ∀ e ∈ chains b, ∀ e' ∈ chains b', e.1 ≠ e'.1 →
    e.1.toNat + 16 + e.2.1.length + 1 ≤ e'.1.toNat ∨ e'.1.toNat + 16 + e'.2.1.length + 1 ≤ e.1.toNat
  live : ∀ b, b < 13 → ∀ e ∈ chains b, ∃ x ∈ H, x.1 ≤ e.1.toNat ∧ e.1.toNat + 16 + e.2.1.length + 1 ≤ x.1 + x.2

/-! ### Nodes and chains under writes -/

/-- A node whose bytes past its value word agree, with a new value word. -/
theorem NodeAt.withValue {m m' : Mem} {pl : Place} {node next : BitVec 64} {key : List (BitVec 8)}
    {v0 v : Val} (h : NodeAt m pl node next key v0)
    (agree : ∀ a, NodeBytes node key a → node.toNat + 8 ≤ a → Agree m m' a)
    (value : valWord pl v = some (bytesT m' node.toNat 8)) : NodeAt m' pl node next key v := by
  have arena := h.arena
  have heapEnd : Vsa.Sim.DlHeap.heapEnd < 2 ^ 64 := by decide
  have off (k : Nat) (hk : k ≤ 16) : (node + BitVec.ofNat 64 k).toNat = node.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have strSame (cs : List Char) (len : cs.length = key.length) :
      ∀ i, i ≤ cs.length → ∀ b, m[(node + 16#64).toNat + i]? = some b → m'[(node + 16#64).toNat + i]? = some b :=
    fun i hi => (agree _ (by rw [off 16 (by decide)]; unfold NodeBytes; omega) (by rw [off 16 (by decide)]; omega)).2
  have lenOf (cs : List Char) (e : strOf key = String.ofList cs) : cs.length = key.length := by
    have := congrArg String.length e
    rw [strOf_length, String.length_ofList] at this
    exact this.symm
  refine ⟨h.nonnull, value, ?_, h.nextWindow, ?_, ?_, h.arena⟩
  · have w8 : bytesT m' (node.toNat + 8) 8 = bytesT m (node.toNat + 8) 8 :=
      word_observed _ fun i hi => (agree _ (by unfold NodeBytes; omega) (by omega)).1
    rw [read8_value, off 8 (by decide), w8, ← off 8 (by decide), ← read8_value]; exact h.next
  · obtain ⟨cs, str, e⟩ := h.name
    exact ⟨cs, str.transport (strSame cs (lenOf cs e)), e⟩
  · intro cs str
    obtain ⟨cs0, str0, e⟩ := h.name
    have eq : cs0 = cs := (str0.transport (strSame cs0 (lenOf cs0 e))).unique str
    subst eq
    exact h.slack cs0 str0

/-- Two nodes at one address in one memory have one key. -/
theorem NodeAt.same_key {m : Mem} {pl : Place} {node n1 n2 : BitVec 64} {k1 k2 : List (BitVec 8)} {v1 v2 : Val}
    (h1 : NodeAt m pl node n1 k1 v1) (h2 : NodeAt m pl node n2 k2 v2) : k1 = k2 := by
  obtain ⟨c1, s1, e1⟩ := h1.name
  obtain ⟨c2, s2, e2⟩ := h2.name
  have := s1.unique s2
  subst this
  exact strOf_inj (e1.trans e2.symm)

/-- The value of the node at `n0` set to `v`. -/
def setNode (n0 : BitVec 64) (v : Val) (e : Entry) : Entry := if e.1 = n0 then (e.1, e.2.1, v) else e

theorem setNode_fst (n0 : BitVec 64) (v : Val) (e : Entry) : (setNode n0 v e).1 = e.1 := by
  unfold setNode; split <;> rfl

theorem setNode_key (n0 : BitVec 64) (v : Val) (e : Entry) : (setNode n0 v e).2.1 = e.2.1 := by
  unfold setNode; split <;> rfl

/-- A chain with the node at `n0` given the value word `w`. -/
theorem TableChain.setValue {m m' : Mem} {pl : Place} {n0 w : BitVec 64} {v : Val} {head : BitVec 64}
    {l : List Entry} (h : TableChain m pl head l)
    (others : ∀ e ∈ l, e.1 ≠ n0 → ∀ a, NodeBytes e.1 e.2.1 a → Agree m m' a)
    (self : ∀ e ∈ l, e.1 = n0 → ∀ a, NodeBytes e.1 e.2.1 a → n0.toNat + 8 ≤ a → Agree m m' a)
    (slot : bytesT m' n0.toNat 8 = w) (repr : valWord pl v = some w) :
    TableChain m' pl head (l.map (setNode n0 v)) := by
  -- discipline: allow(O5-run-induction) induction on a chain of heap nodes, not a run relation
  induction h with
  | nil => exact .nil
  | @cons node next key v1 rest hn _ ih =>
    have tail := ih (fun e he => others e (List.mem_cons_of_mem _ he))
      (fun e he => self e (List.mem_cons_of_mem _ he))
    rw [List.map_cons]
    by_cases eq : node = n0
    · rw [show setNode n0 v (node, key, v1) = (node, key, v) from if_pos eq]
      subst eq
      exact .cons (hn.withValue (fun a ha hi => self _ List.mem_cons_self rfl a ha hi) (by rw [slot]; exact repr)) tail
    · rw [show setNode n0 v (node, key, v1) = (node, key, v1) from if_neg eq]
      exact .cons (hn.transport (others _ List.mem_cons_self eq)) tail

/-! ### The table under writes -/

theorem bucketAddr_toNat (b : Nat) (hb : b < 13) :
    (bucketAddr b).toNat = Layout.sym_named_value_table + 8 * b := by
  simp only [bucketAddr, BitVec.toNat_ofNat, Layout.sym_named_value_table]; omega

/-- A bucket's head word across memory that agrees on it. -/
theorem head_keep {m m' : Mem} {b : Nat} (hb : b < 13)
    (agree : ∀ a, (bucketAddr b).toNat ≤ a → a < (bucketAddr b).toNat + 8 → Agree m m' a) :
    bytesVal .ld (read8 m' (bucketAddr b).toNat) = bytesVal .ld (read8 m (bucketAddr b).toNat) := by
  rw [read8_value, read8_value]
  exact word_observed _ fun i hi => (agree _ (by omega) (by omega)).1

/-! ### The model's register -/

theorem registerNamedValue_present_mem {s : String} {v : Val} :
    ∀ {named : List (String × Val)}, (named.map Prod.fst).Nodup → (∃ y, (s, y) ∈ named) →
      ∀ k x, (k, x) ∈ registerNamedValue s v named ↔ (k = s ∧ x = v) ∨ (k ≠ s ∧ (k, x) ∈ named)
  | [], _, ⟨_, hy⟩ => absurd hy List.not_mem_nil
  | (key, old) :: rest, nodup, ⟨y, hy⟩ => by
    intro k x
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup
    by_cases e : key = s
    · subst e
      have restKeys : ∀ z, (k, z) ∈ rest → k ≠ key := fun z hz ek =>
        nodup.1 ⟨(k, z), hz, by simp [ek]⟩
      simp only [registerNamedValue, beq_self_eq_true, ite_true, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | tail)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨restKeys x tail, Or.inr tail⟩
      · rintro (⟨rfl, rfl⟩ | ⟨ne, ⟨rfl, rfl⟩ | tail⟩)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd rfl ne
        · exact Or.inr tail
    · have ne : (key == s) = false := beq_eq_false_iff_ne.mpr e
      have inRest : ∃ y, (s, y) ∈ rest := by
        rcases List.mem_cons.1 hy with h | h
        · cases h; exact absurd rfl e
        · exact ⟨y, h⟩
      have ih := registerNamedValue_present_mem (s := s) (v := v) nodup.2 inRest k x
      simp only [registerNamedValue, ne, Bool.false_eq_true, ite_false, List.mem_cons, Prod.mk.injEq, ih]
      constructor
      · rintro (⟨rfl, rfl⟩ | (⟨rfl, rfl⟩ | ⟨kne, tail⟩))
        · exact Or.inr ⟨e, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨kne, Or.inr tail⟩
      · rintro (⟨rfl, rfl⟩ | ⟨kne, ⟨rfl, rfl⟩ | tail⟩)
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr ⟨kne, tail⟩)

theorem registerNamedValue_present_keys {s : String} {v : Val} :
    ∀ {named : List (String × Val)}, (∃ y, (s, y) ∈ named) →
      (registerNamedValue s v named).map Prod.fst = named.map Prod.fst
  | [], ⟨_, hy⟩ => absurd hy List.not_mem_nil
  | (key, old) :: rest, ⟨y, hy⟩ => by
    by_cases e : key = s
    · subst e; simp [registerNamedValue]
    · have ne : (key == s) = false := beq_eq_false_iff_ne.mpr e
      have inRest : ∃ y, (s, y) ∈ rest := by
        rcases List.mem_cons.1 hy with h | h
        · cases h; exact absurd rfl e
        · exact ⟨y, h⟩
      simp only [registerNamedValue, ne, Bool.false_eq_true, ite_false, List.map_cons,
        registerNamedValue_present_keys inRest]

theorem registerNamedValue_absent {s : String} {v : Val} :
    ∀ {named : List (String × Val)}, (∀ y, (s, y) ∉ named) →
      registerNamedValue s v named = named ++ [(s, v)]
  | [], _ => rfl
  | (key, old) :: rest, absent => by
    have e : key ≠ s := fun e => absent old (by rw [e]; exact List.mem_cons_self)
    have ne : (key == s) = false := beq_eq_false_iff_ne.mpr e
    simp only [registerNamedValue, ne, Bool.false_eq_true, ite_false, List.cons_append,
      registerNamedValue_absent (fun y hy => absent y (List.mem_cons_of_mem _ hy))]

/-- Two entries of a bucket with one key are one entry. -/
theorem key_unique {l : List Entry} (nodup : (l.map fun e => e.2.1).Nodup) :
    ∀ {e e' : Entry}, e ∈ l → e' ∈ l → e.2.1 = e'.2.1 → e = e' := by
  induction l with
  | nil => intro e e' he; cases he
  | cons x rest ih =>
    intro e e' he he' key
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup
    rcases List.mem_cons.1 he with rfl | t <;> rcases List.mem_cons.1 he' with rfl | t'
    · rfl
    · exact absurd ⟨e', t', key.symm⟩ nodup.1
    · exact absurd ⟨e, t, key⟩ nodup.1
    · exact ih nodup.2 t t' key

/-! ### The found path -/

/-- **The found path's table**: the query's node `n0` gets the value word of
`v`; every other table byte is kept. -/
theorem TableShape.update {m m' : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List Entry} {H : List (Nat × Nat)} {name : List (BitVec 8)}
    {n0 w : BitVec 64} {kb0 : List (BitVec 8)} {v0 v : Val}
    (h : TableShape m pl named chains) (blocks : TableBlocks H chains)
    (found : (n0, kb0, v0) ∈ chains ((hashBytes name).toNat % 13)) (key : strOf kb0 = strOf name)
    (agree : ∀ a, TableFoot chains a → (a < n0.toNat ∨ n0.toNat + 8 ≤ a) → Agree m m' a)
    (slot : bytesT m' n0.toNat 8 = w) (repr : valWord pl v = some w)
    (code : Code.StrcmpLoaded m') (mask : MaskPinned m') :
    TableShape m' pl (registerNamedValue (strOf name) v named) (fun b => (chains b).map (setNode n0 v)) ∧
      TableBlocks H (fun b => (chains b).map (setNode n0 v)) := by
  let k := (hashBytes name).toNat % 13
  have kLt : k < 13 := Nat.mod_lt _ (by decide)
  have n0Low : Vsa.Sim.DlHeap.heapStart ≤ n0.toNat := blocks.low k kLt _ found
  have bucketLow : Layout.sym_named_value_table + 104 ≤ Vsa.Sim.DlHeap.heapStart := by decide
  -- a node at `n0` anywhere in the table is the found node
  have atN0 : ∀ b, b < 13 → ∀ e ∈ chains b, e.1 = n0 → e = (n0, kb0, v0) := by
    intro b hb e he eq
    obtain ⟨nx, ne⟩ := (h.heads b hb).node_of_mem e he
    obtain ⟨nx0, n0e⟩ := (h.heads k kLt).node_of_mem _ found
    have kk : e.2.1 = kb0 := by rw [eq] at ne; exact ne.same_key n0e
    have hbk : b = k := by
      have := h.placed b hb e he
      rw [kk, strOf_inj key] at this
      exact this.symm
    subst hbk
    exact key_unique (blocks.keys _ kLt) he found kk
  have keep : ∀ b, b < 13 → ∀ e ∈ chains b, e.1 ≠ n0 → ∀ a, NodeBytes e.1 e.2.1 a → Agree m m' a := by
    intro b hb e he ne a ha
    apply agree a (Or.inr ⟨b, hb, e, he, ha⟩)
    rcases blocks.apart b k hb kLt e he _ found ne with ap | ap <;> unfold NodeBytes at ha <;> dsimp only at ap <;> omega
  have selfKeep : ∀ b, b < 13 → ∀ e ∈ chains b, e.1 = n0 → ∀ a, NodeBytes e.1 e.2.1 a → n0.toNat + 8 ≤ a →
      Agree m m' a := fun b hb e he _ a ha hi => agree a (Or.inr ⟨b, hb, e, he, ha⟩) (Or.inr hi)
  have present : (strOf name, v0) ∈ named := (h.entries _ _).2 ⟨k, kLt, n0, kb0, found, key⟩
  have mem := registerNamedValue_present_mem (v := v) h.unique ⟨v0, present⟩
  refine ⟨{ window := h.window, heads := ?_, placed := ?_, entries := ?_, unique := ?_, code, mask }, ?_⟩
  · intro b hb
    rw [head_keep hb fun a lo hi => agree a (Or.inl (by
      rw [bucketAddr_toNat b hb] at lo hi; omega)) (Or.inl (by
      rw [bucketAddr_toNat b hb] at hi; omega))]
    exact (h.heads b hb).setValue (keep b hb) (selfKeep b hb) slot repr
  · intro b hb e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    rw [setNode_key]; exact h.placed b hb e0 he0
  · intro kk x
    rw [mem kk x]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨ne, member⟩)
      · exact ⟨k, kLt, n0, kb0, List.mem_map.2 ⟨_, found, by simp [setNode]⟩, key⟩
      · obtain ⟨b, hb, n, kb, he, ek⟩ := (h.entries kk x).1 member
        refine ⟨b, hb, n, kb, List.mem_map.2 ⟨_, he, ?_⟩, ek⟩
        by_cases eq : n = n0
        · have := atN0 b hb _ he eq
          simp only [Prod.mk.injEq] at this
          rw [← ek, this.2.1, key] at ne; exact absurd rfl ne
        · simp [setNode, eq]
    · rintro ⟨b, hb, n, kb, he, ek⟩
      obtain ⟨⟨n', kb', x'⟩, he', img⟩ := List.mem_map.1 he
      by_cases eq : n' = n0
      · have := atN0 b hb _ he' eq
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl⟩ := this
        simp only [setNode, if_pos rfl, Prod.mk.injEq] at img
        obtain ⟨-, rfl, rfl⟩ := img
        exact Or.inl ⟨by rw [← ek, key], rfl⟩
      · simp only [setNode, if_neg eq, Prod.mk.injEq] at img
        obtain ⟨rfl, rfl, rfl⟩ := img
        refine Or.inr ⟨fun e => ?_, (h.entries _ _).2 ⟨b, hb, n', kb', he', ek⟩⟩
        -- the same key as the query: then the found node, at `n0`
        have same' : kb' = kb0 := by rw [← ek] at e; exact strOf_inj (e.trans key.symm)
        have hbk : b = k := by
          have := h.placed b hb _ he'
          simp only at this
          rw [same', strOf_inj key] at this; exact this.symm
        subst hbk
        have := key_unique (blocks.keys _ kLt) he' found same'
        simp only [Prod.mk.injEq] at this
        exact eq this.1
  · rw [registerNamedValue_present_keys ⟨v0, present⟩]; exact h.unique
  · refine ⟨fun b hb => ?_, fun b hb e he => ?_, fun b b' hb hb' e he e' he' ne => ?_, fun b hb e he => ?_⟩
    · rw [List.map_map, show ((fun e : Entry => e.2.1) ∘ setNode n0 v) = fun e => e.2.1 from
        funext fun e => setNode_key n0 v e]
      exact blocks.keys b hb
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      rw [setNode_fst]; exact blocks.low b hb e0 he0
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.1 he'
      rw [setNode_fst, setNode_fst] at ne ⊢
      rw [setNode_key, setNode_key]
      exact blocks.apart b b' hb hb' e0 he0 e1 he1 ne
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      rw [setNode_fst, setNode_key]; exact blocks.live b hb e0 he0

/-! ### The new-node path -/

/-- The chains with `e` linked at the head of bucket `k`. -/
def insertNode (k : Nat) (e : Entry) (chains : Nat → List Entry) : Nat → List Entry :=
  fun b => if b = k then e :: chains b else chains b

/-- **The new-node path's table**: an absent key's node `p`, fresh in the
arena, linked at its bucket's head; every other table byte is kept. -/
theorem TableShape.insert {m m' : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List Entry} {H : List (Nat × Nat)} {name : List (BitVec 8)} {p : BitVec 64} {v : Val}
    {req : Nat} (h : TableShape m pl named chains) (blocks : TableBlocks H chains)
    (absent : ∀ y, (strOf name, y) ∉ named)
    (agree : ∀ a, TableFoot chains a →
      (a < (bucketAddr ((hashBytes name).toNat % 13)).toNat ∨
        (bucketAddr ((hashBytes name).toNat % 13)).toNat + 8 ≤ a) → Agree m m' a)
    (head : bytesVal .ld (read8 m' (bucketAddr ((hashBytes name).toNat % 13)).toNat) = p)
    (node : NodeAt m' pl p (bytesVal .ld (read8 m (bucketAddr ((hashBytes name).toNat % 13)).toNat)) name v)
    (low : Vsa.Sim.DlHeap.heapStart ≤ p.toNat)
    (fresh : ∀ e ∈ H, ∀ y, VsaIris.InExt (p.toNat, req) y → ¬ VsaIris.InExt e y)
    (fits : 16 + name.length + 1 ≤ req)
    (code : Code.StrcmpLoaded m') (mask : MaskPinned m') :
    TableShape m' pl (registerNamedValue (strOf name) v named)
        (insertNode ((hashBytes name).toNat % 13) (p, name, v) chains) ∧
      TableBlocks ((p.toNat, req) :: H) (insertNode ((hashBytes name).toNat % 13) (p, name, v) chains) := by
  generalize hk : (hashBytes name).toNat % 13 = k at agree head node ⊢
  have kLt : k < 13 := hk ▸ Nat.mod_lt _ (by decide)
  have bucketLow : Layout.sym_named_value_table + 104 ≤ Vsa.Sim.DlHeap.heapStart := by decide
  have kAddr := bucketAddr_toNat k kLt
  -- the fresh node lies apart from every existing node
  have nodeApart : ∀ b, b < 13 → ∀ e ∈ chains b,
      p.toNat + 16 + name.length + 1 ≤ e.1.toNat ∨ e.1.toNat + 16 + e.2.1.length + 1 ≤ p.toNat := by
    intro b hb e he
    obtain ⟨x, hx, lo, hi⟩ := blocks.live b hb e he
    rcases Nat.lt_or_ge e.1.toNat (p.toNat + 16 + name.length + 1) with l | l
    · rcases Nat.lt_or_ge p.toNat (e.1.toNat + 16 + e.2.1.length + 1) with g | g
      · exfalso
        rcases Nat.le_total p.toNat e.1.toNat with o | o
        · exact fresh x hx e.1.toNat ⟨o, by dsimp only; omega⟩ ⟨by omega, by omega⟩
        · exact fresh x hx p.toNat ⟨Nat.le_refl _, by dsimp only; omega⟩ ⟨by omega, by omega⟩
      · exact Or.inr g
    · exact Or.inl l
  have absentBucket : ∀ e ∈ chains k, e.2.1 ≠ name := by
    intro e he eq
    exact absent e.2.2 ((h.entries _ _).2 ⟨k, kLt, e.1, e.2.1, he, by rw [eq]⟩)
  have keepOld : ∀ b, b < 13 → ∀ e ∈ chains b, ∀ a, NodeBytes e.1 e.2.1 a → Agree m m' a :=
    fun b hb e he a ha => agree a (Or.inr ⟨b, hb, e, he, ha⟩) (by
      have := blocks.low b hb e he; unfold NodeBytes at ha; omega)
  refine ⟨{ window := h.window, heads := ?_, placed := ?_, entries := ?_, unique := ?_, code, mask }, ?_⟩
  · intro b hb
    by_cases eq : b = k
    · subst eq
      simp only [insertNode, ↓reduceIte]
      rw [head]
      exact .cons node ((h.heads _ hb).transport (keepOld _ hb))
    · simp only [insertNode, if_neg eq]
      rw [head_keep hb fun a lo hi => agree a (Or.inl (by
        rw [bucketAddr_toNat b hb] at lo hi; omega)) (by
        rw [bucketAddr_toNat b hb] at lo hi; rw [kAddr]
        rcases Nat.lt_or_gt_of_ne eq with l | l <;> omega)]
      exact (h.heads b hb).transport (keepOld b hb)
  · intro b hb e he
    by_cases eq : b = k
    · subst eq
      simp only [insertNode, ↓reduceIte] at he
      rcases List.mem_cons.1 he with rfl | t
      · exact hk
      · exact h.placed _ hb e t
    · simp only [insertNode, if_neg eq] at he
      exact h.placed b hb e he
  · intro kk x
    rw [registerNamedValue_absent absent, List.mem_append, List.mem_singleton]
    constructor
    · rintro (member | eq)
      · obtain ⟨b, hb, n, kb, he, ek⟩ := (h.entries kk x).1 member
        refine ⟨b, hb, n, kb, ?_, ek⟩
        by_cases eq : b = k
        · subst eq; simp only [insertNode, ↓reduceIte]; exact List.mem_cons_of_mem _ he
        · simp only [insertNode, if_neg eq]; exact he
      · cases eq
        exact ⟨k, kLt, p, name, by simp [insertNode], rfl⟩
    · rintro ⟨b, hb, n, kb, he, ek⟩
      by_cases eq : b = k
      · subst eq
        simp only [insertNode, ↓reduceIte] at he
        rcases List.mem_cons.1 he with e | t
        · cases e; exact Or.inr (by rw [ek])
        · exact Or.inl ((h.entries _ _).2 ⟨_, hb, n, kb, t, ek⟩)
      · simp only [insertNode, if_neg eq] at he
        exact Or.inl ((h.entries _ _).2 ⟨b, hb, n, kb, he, ek⟩)
  · rw [registerNamedValue_absent absent, List.map_append, List.nodup_append]
    refine ⟨h.unique, by simp, ?_⟩
    intro a ha b hb e
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb e
    obtain ⟨⟨kk, y⟩, hy, rfl⟩ := List.mem_map.1 ha
    exact absent y hy
  · refine ⟨fun b hb => ?_, fun b hb e he => ?_, fun b b' hb hb' e he e' he' ne => ?_, fun b hb e he => ?_⟩
    · by_cases eq : b = k
      · subst eq
        simp only [insertNode, ↓reduceIte, List.map_cons, List.nodup_cons, List.mem_map]
        exact ⟨fun ⟨e, he, ek⟩ => absentBucket e he ek, blocks.keys _ hb⟩
      · simp only [insertNode, if_neg eq]; exact blocks.keys b hb
    · simp only [insertNode] at he
      split at he
      · rcases List.mem_cons.1 he with rfl | t
        · exact low
        · exact blocks.low b hb e t
      · exact blocks.low b hb e he
    · simp only [insertNode] at he he'
      have old : ∀ c, c < 13 → ∀ f ∈ (if c = k then (p, name, v) :: chains c else chains c),
          f = (p, name, v) ∨ f ∈ chains c := by
        intro c _ f hf
        split at hf
        · exact List.mem_cons.1 hf
        · exact Or.inr hf
      rcases old b hb e he with rfl | t <;> rcases old b' hb' e' he' with rfl | t'
      · exact absurd rfl ne
      · exact nodeApart b' hb' e' t'
      · exact (nodeApart b hb e t).symm
      · exact blocks.apart b b' hb hb' e t e' t' ne
    · simp only [insertNode] at he
      split at he
      · rcases List.mem_cons.1 he with rfl | t
        · exact ⟨(p.toNat, req), List.mem_cons_self, Nat.le_refl _, by dsimp only; omega⟩
        · obtain ⟨x, hx, lo, hi⟩ := blocks.live b hb e t
          exact ⟨x, List.mem_cons_of_mem _ hx, lo, hi⟩
      · obtain ⟨x, hx, lo, hi⟩ := blocks.live b hb e he
        exact ⟨x, List.mem_cons_of_mem _ hx, lo, hi⟩

end OCaml.Vm.Primitives.Named.NamedValue
