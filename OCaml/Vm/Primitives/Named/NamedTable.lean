import OCaml.Vm.Primitives.Named.NamedLookup

/-!
# `named_value_table` as a representation of `world.named`

`callback.c` keeps the named values in 13 buckets of malloc'd
`{ value val; struct named_value *next; char name[]; }` nodes, each key in
bucket `hash_value_name(key) % 13`. `NamedTableAt m pl named` says the table
in `m` holds exactly the entries of BcSem's `world.named` (keys as the nodes'
C strings, values represented through `pl`). From it and a query string,
`table_bucket` gives the hashed bucket's `BucketAt`, and `table_find` says
what `caml_named_value` returns: the node of the query's entry, or `NULL`.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Bytecode OCaml.Vm.Primitives OCaml.Vm.Boot.Startup OCaml.Vm.Sim

/-- A C string's bytes as the key it spells. -/
def strOf (bytes : List (BitVec 8)) : String := String.ofList (bytes.map fun b => Char.ofNat b.toNat)

/-- One node of the table. -/
structure NodeAt (m : Mem) (pl : Place) (node next : BitVec 64) (key : List (BitVec 8)) (v : Val) : Prop where
  nonnull : node ≠ 0#64
  value : valWord pl v = some (bytesT m node.toNat 8)
  next : bytesVal .ld (read8 m (node + 8#64).toNat) = next
  nextWindow : ReadWindow (node + 8#64) 8
  name : CString m (node + 16#64).toNat (strOf key)
  slack : ∀ cs, CStr m (node + 16#64).toNat cs → StrcmpWSlack (node + 16#64) cs.length

/-- A bucket's chain of nodes, `NULL`-terminated. -/
inductive TableChain (m : Mem) (pl : Place) : BitVec 64 → List (BitVec 64 × List (BitVec 8) × Val) → Prop where
  | nil : TableChain m pl 0#64 []
  | cons {node next : BitVec 64} {key : List (BitVec 8)} {v : Val} {rest : List (BitVec 64 × List (BitVec 8) × Val)} :
      NodeAt m pl node next key v → TableChain m pl next rest → TableChain m pl node ((node, key, v) :: rest)

/-- The table with chosen bucket chains `chains`. -/
structure TableShape (m : Mem) (pl : Place) (named : List (String × Val))
    (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)) : Prop where
  window : ∀ b, b < 13 → ReadWindow (bucketAddr b) 8
  heads : ∀ b, b < 13 → TableChain m pl (bytesVal .ld (read8 m (bucketAddr b).toNat)) (chains b)
  placed : ∀ b, b < 13 → ∀ e ∈ chains b, (hashBytes e.2.1).toNat % 13 = b
  /-- the nodes are exactly the entries -/
  entries : ∀ k v, (k, v) ∈ named ↔ ∃ b, b < 13 ∧ ∃ n kb, (n, kb, v) ∈ chains b ∧ strOf kb = k
  /-- keys are unique (`caml_register_named_value` updates in place) -/
  unique : (named.map Prod.fst).Nodup
  code : Code.StrcmpLoaded m
  mask : MaskPinned m

/-- **The named-value table** represents `named` in `m`. -/
def NamedTableAt (m : Mem) (pl : Place) (named : List (String × Val)) : Prop :=
  ∃ chains, TableShape m pl named chains

/-- A chain's nodes as `strcmp` sees them, against a query. -/
theorem TableChain.chainAt {m : Mem} {pl : Place} {q : BitVec 64} {qs : String}
    (code : Code.StrcmpLoaded m) (mask : MaskPinned m) (query : CString m q.toNat qs)
    (qslack : ∀ cs, CStr m q.toNat cs → StrcmpWSlack q cs.length) :
    ∀ {head : BitVec 64} {l : List (BitVec 64 × List (BitVec 8) × Val)}, TableChain m pl head l →
      ChainAt m q qs head (l.map fun e => (e.1, strOf e.2.1))
  | _, _, .nil => .nil
  | _, _, .cons node rest =>
    .cons node.nonnull ⟨code, query, node.name, mask, qslack, node.slack⟩ node.nextWindow node.next
      (TableChain.chainAt code mask query qslack rest)

/-- **The hashed bucket** of a query, from the table. -/
theorem table_bucket {m : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {q : BitVec 64} {name : List (BitVec 8)}
    (shape : TableShape m pl named chains) (query : CString m q.toNat (strOf name))
    (qslack : ∀ cs, CStr m q.toNat cs → StrcmpWSlack q cs.length) :
    BucketAt m q (strOf name) ((hashBytes name).toNat % 13)
      ((chains ((hashBytes name).toNat % 13)).map fun e => (e.1, strOf e.2.1)) :=
  have lt : (hashBytes name).toNat % 13 < 13 := Nat.mod_lt _ (by decide)
  ⟨shape.window _ lt, _, rfl, (shape.heads _ lt).chainAt shape.code shape.mask query qslack⟩

theorem chainFind_none {qs : String} :
    ∀ {l : List (BitVec 64 × String)}, (∀ e ∈ l, e.2 ≠ qs) → chainFind qs l = 0#64
  | [], _ => rfl
  | (n, k) :: rest, h => by
    have hk : qs ≠ k := fun e => h (n, k) (List.mem_cons_self ..) e.symm
    simp only [chainFind, hk, ite_false]
    exact chainFind_none fun e he => h e (List.mem_cons_of_mem _ he)

theorem chainFind_some {qs : String} :
    ∀ {l : List (BitVec 64 × String)}, (∃ e ∈ l, e.2 = qs) → ∃ e ∈ l, e.2 = qs ∧ chainFind qs l = e.1
  | [], ⟨_, he, _⟩ => absurd he (List.not_mem_nil)
  | (n, k) :: rest, ⟨e, he, ek⟩ => by
    by_cases hk : qs = k
    · exact ⟨(n, k), List.mem_cons_self .., hk.symm, by simp [chainFind, hk]⟩
    · rcases List.mem_cons.1 he with rfl | tail
      · exact absurd ek.symm hk
      · obtain ⟨e', he', ek', find⟩ := chainFind_some ⟨e, tail, ek⟩
        exact ⟨e', List.mem_cons_of_mem _ he', ek', by simp [chainFind, hk, find]⟩

theorem lookup_of_mem {named : List (String × Val)} (unique : (named.map Prod.fst).Nodup) :
    ∀ {k : String} {v : Val}, (k, v) ∈ named → named.lookup k = some v := by
  induction named with
  | nil => intro k v h; cases h
  | cons p rest ih =>
    intro k v h
    obtain ⟨k', v'⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at unique
    rcases List.mem_cons.1 h with e | tail
    · cases e; simp [List.lookup]
    · have ne : k ≠ k' := fun e => unique.1 ⟨(k, v), tail, by simp [e]⟩
      simp [List.lookup, beq_eq_false_iff_ne.mpr ne, ih unique.2 tail]

theorem map_inj {α β : Type} {f : α → β} (inj : ∀ x y, f x = f y → x = y) :
    ∀ {a b : List α}, a.map f = b.map f → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [inj x y h.1, map_inj inj h.2]

theorem mem_of_lookup {named : List (String × Val)} {k : String} {v : Val} :
    named.lookup k = some v → (k, v) ∈ named := by
  induction named with
  | nil => intro h; cases h
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    intro h
    by_cases e : k = k'
    · subst e; simp [List.lookup] at h; subst h; exact List.mem_cons_self ..
    · simp [List.lookup, beq_eq_false_iff_ne.mpr e] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem strOf_inj {a b : List (BitVec 8)} (h : strOf a = strOf b) : a = b := by
  have h' := congrArg String.toList h
  simp only [strOf, String.toList_ofList] at h'
  apply map_inj _ h'
  intro x y e
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  have vx : Nat.isValidChar x.toNat := Or.inl (by omega)
  have vy : Nat.isValidChar y.toNat := Or.inl (by omega)
  have := congrArg Char.toNat e
  simp only [Char.ofNat, vx, vy, dite_true] at this
  simpa [Char.ofNatAux, Char.toNat] using this

/-- **What `caml_named_value` finds**: for a query `name` present in
`named`, the hashed bucket's first node with that key, whose value is the
entry's; for an absent query, `NULL`. -/
theorem table_find {m : Mem} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {name : List (BitVec 8)}
    (shape : TableShape m pl named chains) :
    (named.lookup (strOf name) = none →
      chainFind (strOf name) ((chains ((hashBytes name).toNat % 13)).map fun e => (e.1, strOf e.2.1)) = 0#64) ∧
    (∀ v, named.lookup (strOf name) = some v →
      ∃ n kb v', (n, kb, v') ∈ chains ((hashBytes name).toNat % 13) ∧ strOf kb = strOf name ∧
        chainFind (strOf name) ((chains ((hashBytes name).toNat % 13)).map fun e => (e.1, strOf e.2.1)) = n ∧
        named.lookup (strOf name) = some v') := by
  constructor
  · intro none
    apply chainFind_none
    intro e he ek
    obtain ⟨⟨n, kb, v⟩, mem, rfl⟩ := List.mem_map.1 he
    have entry : (strOf kb, v) ∈ named :=
      (shape.entries _ v).2 ⟨_, Nat.mod_lt _ (by decide), n, kb, mem, rfl⟩
    have := lookup_of_mem shape.unique entry
    simp only at ek
    rw [ek] at this
    rw [this] at none; cases none
  · intro v found
    obtain ⟨b, lt, n, kb, mem, key⟩ := (shape.entries _ v).1 (mem_of_lookup found)
    have same : kb = name := strOf_inj key
    have bucket : b = (hashBytes name).toNat % 13 := by
      rw [← same]; exact (shape.placed b lt _ mem).symm
    subst bucket
    obtain ⟨e, he, ek, find⟩ := chainFind_some (qs := strOf name)
      ⟨(n, strOf kb), List.mem_map_of_mem (f := fun e : BitVec 64 × List (BitVec 8) × Val => (e.1, strOf e.2.1)) mem, key⟩
    obtain ⟨⟨n', kb', v'⟩, mem', rfl⟩ := List.mem_map.1 he
    have entry : (strOf kb', v') ∈ named :=
      (shape.entries _ v').2 ⟨_, Nat.mod_lt _ (by decide), n', kb', mem', rfl⟩
    simp only at ek
    rw [ek] at entry
    exact ⟨n', kb', v', mem', ek, find, lookup_of_mem shape.unique entry⟩

/-- **`caml_named_value` over the table**: it returns `NULL` for a name
absent from `world.named`, and for a present name a node of the table whose
value slot represents the entry's value. -/
theorem named_value_table {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    {pl : Place} {named : List (String × Val)} {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)}
    (h : LookupInput ra sp a s0 s1 name c)
    (shape : TableShape (writeLog c.σ.mem (saveLog sp ra s0 s1)) pl named chains)
    (query : CString (writeLog c.σ.mem (saveLog sp ra s0 s1)) a.toNat (strOf name))
    (qslack : ∀ cs, CStr (writeLog c.σ.mem (saveLog sp ra s0 s1)) a.toNat cs → StrcmpWSlack a cs.length) :
    ∃ d r, Steps c d ∧ NamedFound c ra sp a s0 s1 r d ∧
      (named.lookup (strOf name) = none → r = 0#64) ∧
      (∀ v, named.lookup (strOf name) = some v → ∃ kb v', (r, kb, v') ∈ chains ((hashBytes name).toNat % 13) ∧
        strOf kb = strOf name ∧ named.lookup (strOf name) = some v') := by
  obtain ⟨d, run, found⟩ := named_value_summary h (table_bucket shape query qslack)
  refine ⟨d, _, run, found, (table_find shape).1, fun v present => ?_⟩
  obtain ⟨n, kb, v', mem, key, find, look⟩ := (table_find shape).2 v present
  rw [find]
  exact ⟨kb, v', mem, key, look⟩

end OCaml.Vm.Primitives.Named.NamedValue
