import Pilot

/-!
# Reloc: relocation equivariance by combinators (pilot entrant)

A relocation `μ` acts on placements (`reloc μ pl`), on words (a pointer word
into a placed block moves block-affinely, every other word is fixed:
`relocWord`), and on memory (a configuration `c'` is the image of `c` on an
assertion's footprint: `Eqv.Img`). A representation component is built from
the combinators of `Eqv` and inherits `Eqv.transport` for free.

Section 1 is SETUP; section 2 the held-out cases H5–H7; section 3 the extra
measured component (`HeapRepr`).
-/

namespace OCaml.Pilot.Reloc

open OCaml.Bytecode OCaml.Vm Vsa.Machine OCaml.Pilot

/-! ## 1. The abstraction -/

/-- The typed action of `μ` on a word that holds `v` under `pl`: a pointer
into a placed block moves block-affinely, every other word is fixed. -/
def relocWord (μ : Nat → Nat) (pl : Place) : Val → BitVec 64 → BitVec 64
  | .ptr l k, w => match pl.φ l with
    | some a => BitVec.ofNat 64 (μ a + 8 * k)
    | none => w
  | _, w => w

/-- THE ATOM LEMMA: the value encoding commutes with the action. -/
theorem valWord_reloc {μ : Nat → Nat} {pl : Place} {v : Val} {w : BitVec 64}
    (h : valWord pl v = some w) : valWord (reloc μ pl) v = some (relocWord μ pl v w) := by
  cases v with
  | ptr l k =>
    cases hl : pl.φ l with
    | none => simp [valWord, hl] at h
    | some a => simp_all [valWord, reloc, relocWord]
  | _ => simpa [valWord, reloc, relocWord] using h

theorem relocWord_fix {μ : Nat → Nat} {pl : Place} {v : Val} (w : BitVec 64)
    (hv : v.loc? = none) : relocWord μ pl v w = w := by
  cases v <;> simp_all [relocWord, Val.loc?]

/-- The atom, read backwards: a relocated value word IS the action's image. -/
theorem relocWord_of_post {μ : Nat → Nat} {pl : Place} {v : Val} {w w' : BitVec 64}
    (h : valWord pl v = some w) (h' : valWord (reloc μ pl) v = some w') :
    w' = relocWord μ pl v w := by
  rw [valWord_reloc h] at h'; exact (Option.some.inj h').symm

/-- `n` bytes at `x` in `c` reappear at `x'` in `c'`. -/
def Copied (c c' : Config) (x x' n : Nat) : Prop := ∀ j, j < n → byte c' (x' + j) = byte c (x + j)

theorem bytesT_congr {m m' : Std.ExtHashMap Nat (BitVec 8)} {x x' n : Nat}
    (h : ∀ j, j < n → Vsa.Sim.bytesT m' (x' + j) 1 = Vsa.Sim.bytesT m (x + j) 1) :
    Vsa.Sim.bytesT m' x' n = Vsa.Sim.bytesT m x n := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [Vsa.Sim.getLsbD_bytesT _ _ _ _ hk, Vsa.Sim.getLsbD_bytesT _ _ _ _ hk]
  have := congrArg (·.getLsbD (k % 8)) (h (k / 8) (by omega))
  rw [Vsa.Sim.getLsbD_bytesT _ _ _ _ (by omega), Vsa.Sim.getLsbD_bytesT _ _ _ _ (by omega)] at this
  simpa [Nat.div_eq_of_lt (Nat.mod_lt k (by omega : 8 > 0))] using this

theorem Copied.mono {c c' : Config} {x x' n : Nat} (h : Copied c c' x x' n) (o m : Nat)
    (hle : o + m ≤ n) : ∀ j, j < m → byte c' (x' + o + j) = byte c (x + o + j) := by
  intro j hj; have := h (o + j) (by omega); simpa [Nat.add_assoc] using this

/-- A relocation-equivariant layout assertion about a base address `b`:
`P pl b c` holds before the move; `Img μ pl b b' c c'` says `c'` is the
`μ`-image of `c` on `P`'s footprint (moved from base `b` to `b'`), and may
assume `P`; `transport` gives `P` after the move. -/
structure Eqv where
  P : Place → Nat → Config → Prop
  Img : (Nat → Nat) → Place → Nat → Nat → Config → Config → Prop
  transport : ∀ μ pl b b' c c', P pl b c → Img μ pl b b' c c' → P (reloc μ pl) b' c'

namespace Eqv

/-- A fact about the base (or no memory at all): must hold at the new base. -/
def pure (p : Nat → Prop) : Eqv := ⟨fun _ b _ => p b, fun _ _ _ b' _ _ => p b', fun _ _ _ _ _ _ _ h => h⟩

/-- A fact about the placement: must hold of the relocated placement. -/
def plFact (p : Place → Prop) : Eqv :=
  ⟨fun pl _ _ => p pl, fun μ pl _ _ _ _ => p (reloc μ pl), fun _ _ _ _ _ _ _ h => h⟩

def and (E F : Eqv) : Eqv :=
  ⟨fun pl b c => E.P pl b c ∧ F.P pl b c,
   fun μ pl b b' c c' => E.Img μ pl b b' c c' ∧ F.Img μ pl b b' c c',
   fun μ pl b b' c c' h i => ⟨E.transport μ pl b b' c c' h.1 i.1, F.transport μ pl b b' c c' h.2 i.2⟩⟩

def all {ι : Type} (E : ι → Eqv) : Eqv :=
  ⟨fun pl b c => ∀ i, (E i).P pl b c, fun μ pl b b' c c' => ∀ i, (E i).Img μ pl b b' c c',
   fun μ pl b b' c c' h i x => (E x).transport μ pl b b' c c' (h x) (i x)⟩

/-- Guarded by a pure (placement- and memory-free) premise. -/
def guard (g : Prop) (E : Eqv) : Eqv :=
  ⟨fun pl b c => g → E.P pl b c, fun μ pl b b' c c' => g → E.Img μ pl b b' c c',
   fun μ pl b b' c c' h i hg => E.transport μ pl b b' c c' (h hg) (i hg)⟩

/-- ∃ over non-address data (the image may assume the witness's pre). -/
def ex {ι : Type} (E : ι → Eqv) : Eqv :=
  ⟨fun pl b c => ∃ i, (E i).P pl b c,
   fun μ pl b b' c c' => ∀ i, (E i).P pl b c → (E i).Img μ pl b b' c c',
   fun μ pl b b' c c' ⟨x, h⟩ i => ⟨x, (E x).transport μ pl b b' c c' h (i x h)⟩⟩

/-- ∃ over an ADDRESS bound by the placement: block `l` sits at `a`, and moves to `μ a`. -/
def placed (l : Nat) (E : Eqv) : Eqv :=
  ⟨fun pl _ c => ∃ a, pl.φ l = some a ∧ E.P pl a c,
   fun μ pl _ _ c c' => ∀ a, pl.φ l = some a → E.Img μ pl a (μ a) c c',
   fun μ pl _ _ c c' ⟨a, ha, h⟩ i =>
     ⟨μ a, by simp [reloc, ha], E.transport μ pl a (μ a) c c' h (i a ha)⟩⟩

/-- A list-indexed family: `∀ i x, xs[i]? = some x → E i x`. -/
def list {α : Type} (xs : List α) (E : Nat → α → Eqv) : Eqv :=
  all fun i => all fun x => guard (xs[i]? = some x) (E i x)

/-- Value points-to at `f b`: the image word is the typed action's image. -/
def val (v : Val) (f : Nat → Nat) : Eqv :=
  ⟨fun pl b c => valWord pl v = some (word c (f b)),
   fun μ pl b b' c c' => word c' (f b') = relocWord μ pl v (word c (f b)),
   fun _ _ _ _ _ _ h i => by rw [i]; exact valWord_reloc h⟩

/-- Raw (non-value) word / 32-bit word / byte at `f b`: copied verbatim. -/
def rawW (f : Nat → Nat) (R : BitVec 64 → Prop) : Eqv :=
  ⟨fun _ b c => R (word c (f b)), fun _ _ b b' c c' => word c' (f b') = word c (f b),
   fun _ _ _ _ _ _ h i => by rw [i]; exact h⟩

def rawW32 (f : Nat → Nat) (R : BitVec 32 → Prop) : Eqv :=
  ⟨fun _ b c => R (word32 c (f b)), fun _ _ b b' c c' => word32 c' (f b') = word32 c (f b),
   fun _ _ _ _ _ _ h i => by rw [i]; exact h⟩

def rawB (f : Nat → Nat) (R : BitVec 8 → Prop) : Eqv :=
  ⟨fun _ b c => R (byte c (f b)), fun _ _ b b' c c' => byte c' (f b') = byte c (f b),
   fun _ _ _ _ _ _ h i => by rw [i]; exact h⟩

/-! ### Post-form image of a value family (the atom lemma, lifted) -/

theorem list_val_img {xs : List Val} {f : Nat → Nat → Nat} {μ pl b b' c c'}
    (h : (list xs fun i v => val v (f i)).P pl b c)
    (h' : ∀ i v, xs[i]? = some v → valWord (reloc μ pl) v = some (word c' (f i b'))) :
    (list xs fun i v => val v (f i)).Img μ pl b b' c c' :=
  fun i v hv => relocWord_of_post (h i v hv) (h' i v hv)

/-! ### Window copies: a value-free assertion inside `[b, b+n)` is imaged by copying the window -/

def CopyIn (E : Eqv) (n : Nat) : Prop :=
  ∀ μ pl b b' c c', E.P pl b c → Copied c c' b b' n → E.Img μ pl b b' c c'

theorem and_copyIn {E F : Eqv} {n} (hE : E.CopyIn n) (hF : F.CopyIn n) : (and E F).CopyIn n :=
  fun μ pl b b' c c' h hc => ⟨hE μ pl b b' c c' h.1 hc, hF μ pl b b' c c' h.2 hc⟩

theorem list_copyIn {α : Type} {xs : List α} {E : Nat → α → Eqv} {n}
    (hE : ∀ i x, xs[i]? = some x → (E i x).CopyIn n) : (list xs E).CopyIn n :=
  fun μ pl b b' c c' h hc i x hx => hE i x hx μ pl b b' c c' (h i x hx) hc

theorem rawW_copyIn {f R n} (o : Nat) (hf : ∀ b, f b = b + o) (hn : o + 8 ≤ n) :
    (rawW f R).CopyIn n := fun _ _ b b' c c' _ hc => by
  show word c' (f b') = word c (f b)
  rw [hf, hf]; exact bytesT_congr fun j hj => hc.mono o 8 hn j hj

theorem rawW32_copyIn {f R n} (o : Nat) (hf : ∀ b, f b = b + o) (hn : o + 4 ≤ n) :
    (rawW32 f R).CopyIn n := fun _ _ b b' c c' _ hc => by
  show word32 c' (f b') = word32 c (f b)
  rw [hf, hf]; exact bytesT_congr fun j hj => hc.mono o 4 hn j hj

theorem rawB_copyIn {f R n} (o : Nat) (hf : ∀ b, f b = b + o) (hn : o + 1 ≤ n) :
    (rawB f R).CopyIn n := fun _ _ b b' c c' _ hc => by
  show byte c' (f b') = byte c (f b)
  rw [hf, hf]; exact bytesT_congr fun j hj => hc.mono o 1 hn j hj

end Eqv

/-- Bridge to the REAL collector (documented premise; not used by H5–H7,
which quantify over the typed `μ`). The minor GC (`caml_oldify_one`,
`runtime/minor_gc.c`) acts on each word it visits by bit pattern:
`gcAct w` is the forwarding address when `Is_block w ∧ Is_young w`, else
`w`; it visits only roots, the ref table and fields of copied blocks
(`visited`). `ScanCoherent` says that on visited values the untyped action
agrees with the typed one. Supplied by: the Layer A minor-GC simulation
(forwarding invariant for `ptr`) plus address-range facts for `nonPtr`
(ints are odd; code, atoms and `raw` words lie outside the minor heap). -/
structure ScanCoherent (gcAct : BitVec 64 → BitVec 64) (μ : Nat → Nat) (pl : Place)
    (visited : Val → Prop) : Prop where
  /-- a visited pointer is forwarded block-affinely (young) or left in place (old: `μ a = a`) -/
  ptr : ∀ l k a, visited (.ptr l k) → pl.φ l = some a →
    gcAct (BitVec.ofNat 64 (a + 8 * k)) = BitVec.ofNat 64 (μ a + 8 * k)
  /-- a visited non-pointer's word is classified "not a young block" and kept -/
  nonPtr : ∀ v w, visited v → v.loc? = none → valWord pl v = some w → gcAct w = w

theorem ScanCoherent.act {gcAct μ pl visited} (h : ScanCoherent gcAct μ pl visited)
    {v : Val} {w : BitVec 64} (hv : visited v) (hw : valWord pl v = some w) :
    gcAct w = relocWord μ pl v w := by
  cases v with
  | ptr l k =>
    cases hl : pl.φ l with
    | none => simp [valWord, hl] at hw
    | some a =>
      simp only [valWord, hl, Option.map_some, Option.some.injEq] at hw
      simp [relocWord, hl, ← hw, h.ptr l k a hv hl]
  | _ => exact h.nonPtr _ w hv rfl hw

/-! ## 2. Held-out cases -/

theorem h5 : OCaml.Pilot.H5 := fun pl μ =>
  ⟨fun l k a h => by
    simpa [relocWord, h] using valWord_reloc (μ := μ) (w := BitVec.ofNat 64 (a + 8 * k))
      (show valWord pl (.ptr l k) = _ by simp [valWord, h]),
   fun v hv => by
    cases h : valWord pl v with
    | none => cases v <;> simp [valWord, Val.loc?] at h hv
    | some w => rw [valWord_reloc h, relocWord_fix w hv]⟩

/-- An object's payload as a combinator term (mirrors `ObjAt`'s match). -/
def payload (cp : ChanPlace) : Obj → Eqv
  | .block _ fs => Eqv.list fs fun i v => Eqv.val v (· + 8 * i)
  | .bytes b => Eqv.and (Eqv.list b fun i x => Eqv.rawB (· + i) (· = BitVec.ofNat 8 x.toNat))
      (Eqv.rawB (fun a => a + 8 * (Obj.bytes b).wosize - 1)
        fun y => y.toNat = 8 * (Obj.bytes b).wosize - 1 - b.length)
  | .double d => Eqv.rawW (fun a => a) (· = d)
  | .doubleArray ds => Eqv.list ds fun i d => Eqv.rawW (· + 8 * i) (· = d)
  | .int64 n => Eqv.and (Eqv.rawW (fun a => a) (·.toNat = Layout.sym_caml_int64_ops))
      (Eqv.rawW (· + 8) (· = n))
  | .int32 n => Eqv.and (Eqv.rawW (fun a => a) (·.toNat = Layout.sym_caml_int32_ops))
      (Eqv.rawW32 (· + 8) (· = n))
  | .nativeint n => Eqv.and (Eqv.rawW (fun a => a) (·.toNat = Layout.sym_caml_nativeint_ops))
      (Eqv.rawW (· + 8) (· = n))
  | .channel id => Eqv.and (Eqv.rawW (fun a => a) (·.toNat = Layout.sym_channel_operations))
      (Eqv.rawW (· + 8) fun w => cp id = some w.toNat)

def objEqv (cp : ChanPlace) (o : Obj) : Eqv :=
  Eqv.and (Eqv.rawW (· - 8) fun w => HeaderOk w o.wosize o.tag) (payload cp o)

theorem objAt_eq (c : Config) (pl : Place) (cp : ChanPlace) (a : Nat) (o : Obj) :
    ObjAt c pl cp a o = (objEqv cp o).P pl a c := by cases o <;> rfl

theorem payload_copyIn (cp : ChanPlace) (o : Obj) (hnb : ∀ t fs, o ≠ .block t fs) :
    (payload cp o).CopyIn (8 * o.wosize + 8) := by
  cases o with
  | block t fs => exact absurd rfl (hnb t fs)
  | bytes b =>
    refine Eqv.and_copyIn (Eqv.list_copyIn fun i x hx => ?_) (Eqv.rawB_copyIn (8 * (Obj.bytes b).wosize - 1)
      (fun _ => by simp only [Obj.wosize]; omega) (by simp only [Obj.wosize]; omega))
    have := (List.getElem?_eq_some_iff.1 hx).1
    exact Eqv.rawB_copyIn i (fun _ => rfl) (by simp only [Obj.wosize]; omega)
  | double d =>
    show (Eqv.rawW (fun a => a) (· = d)).CopyIn (8 * 1 + 8)
    exact Eqv.rawW_copyIn 0 (fun _ => rfl) (by omega)
  | doubleArray ds =>
    refine Eqv.list_copyIn fun i x hx => ?_
    have := (List.getElem?_eq_some_iff.1 hx).1
    exact Eqv.rawW_copyIn (8 * i) (fun _ => rfl) (by simp only [Obj.wosize]; omega)
  | int64 n | nativeint n | channel n =>
    exact Eqv.and_copyIn (Eqv.rawW_copyIn 0 (fun _ => rfl) (by simp [Obj.wosize]))
      (Eqv.rawW_copyIn 8 (fun _ => rfl) (by simp [Obj.wosize]))
  | int32 n =>
    exact Eqv.and_copyIn (Eqv.rawW_copyIn 0 (fun _ => rfl) (by simp [Obj.wosize]))
      (Eqv.rawW32_copyIn 8 (fun _ => rfl) (by simp [Obj.wosize]))

/-- H6's premises, named: header copied, fields relocated, raw payload copied. -/
structure ObjMoved (c c' : Config) (pl : Place) (μ : Nat → Nat) (a : Nat) (o : Obj) : Prop where
  header : word c' (μ a - 8) = word c (a - 8)
  fields : ∀ t fs, o = .block t fs → ∀ i v, fs[i]? = some v →
    valWord (reloc μ pl) v = some (word c' (μ a + 8 * i))
  raw : (∀ t fs, o ≠ .block t fs) → Copied c c' a (μ a) (8 * o.wosize + 8)

theorem objImg {c c' pl cp μ a o} (h : ObjAt c pl cp a o) (m : ObjMoved c c' pl μ a o) :
    (objEqv cp o).Img μ pl a (μ a) c c' := by
  rw [objAt_eq] at h
  refine ⟨m.header, ?_⟩
  by_cases hb : ∃ t fs, o = .block t fs
  · obtain ⟨t, fs, rfl⟩ := hb; exact Eqv.list_val_img h.2 (m.fields t fs rfl)
  · have hnb : ∀ t fs, o ≠ .block t fs := fun t fs e => hb ⟨t, fs, e⟩
    exact payload_copyIn cp o hnb μ pl a (μ a) c c' h.2 (m.raw hnb)

theorem h6 : OCaml.Pilot.H6 := by
  intro c c' pl cp μ a o h _ hhdr hf hraw
  have m : ObjMoved c c' pl μ a o := ⟨hhdr, hf, fun hnb j hj => hraw hnb j hj⟩
  have := (objEqv cp o).transport μ pl a (μ a) c c' (by rw [← objAt_eq]; exact h) (objImg h m)
  rwa [← objAt_eq] at this

def stackEqv (high : Nat) (stk : List Val) : Eqv :=
  Eqv.and (Eqv.pure fun sp => sp + 8 * stk.length = high) (Eqv.list stk fun i v => Eqv.val v (· + 8 * i))

theorem h7 : OCaml.Pilot.H7 := fun c c' pl μ sp high stk h hv =>
  (stackEqv high stk).transport μ pl sp sp c c' h ⟨h.1, Eqv.list_val_img h.2 hv⟩

/-! ## 3. Extra measured component: `HeapRepr` -/

def heapEqv (cp : ChanPlace) (P : Prog) (s : St) : Eqv :=
  Eqv.and
    (Eqv.all fun l => Eqv.guard (Live s.heap (roots P s) l) <| Eqv.placed l <|
      Eqv.ex fun o => Eqv.and (Eqv.pure fun _ => s.heap.get? l = some o) (objEqv cp o))
    (Eqv.plFact fun pl => ∀ l l' a a' o o', Live s.heap (roots P s) l → Live s.heap (roots P s) l' →
      l ≠ l' → pl.φ l = some a → pl.φ l' = some a' → s.heap.get? l = some o → s.heap.get? l' = some o' →
      a + 8 * o.wosize ≤ a' - 8 ∨ a' + 8 * o'.wosize ≤ a - 8)

theorem heapRepr_iff (c : Config) (pl : Place) (cp : ChanPlace) (P : Prog) (s : St) :
    HeapRepr c pl cp P s ↔ (heapEqv cp P s).P pl 0 c := by
  simp only [HeapRepr, heapEqv, Eqv.and, Eqv.all, Eqv.guard, Eqv.placed, Eqv.ex, Eqv.pure, Eqv.plFact,
    ← objAt_eq, exists_and_left]

/-- `HeapRepr` survives a relocation that moves every live object (H6's
premises per block) and keeps live blocks apart. -/
theorem heapRepr_reloc {c c' : Config} {pl : Place} {cp : ChanPlace} {P : Prog} {s : St}
    {μ : Nat → Nat} (h : HeapRepr c pl cp P s)
    (hmv : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
      ObjMoved c c' pl μ a o)
    (hsep : ∀ l l' a a' o o', Live s.heap (roots P s) l → Live s.heap (roots P s) l' → l ≠ l' →
      pl.φ l = some a → pl.φ l' = some a' → s.heap.get? l = some o → s.heap.get? l' = some o' →
      μ a + 8 * o.wosize ≤ μ a' - 8 ∨ μ a' + 8 * o'.wosize ≤ μ a - 8) :
    HeapRepr c' (reloc μ pl) cp P s := by
  rw [heapRepr_iff] at h ⊢
  refine (heapEqv cp P s).transport μ pl 0 0 c c' h ⟨fun l hl a ha o ho => ⟨ho.1, ?_⟩, ?_⟩
  · exact objImg (by rw [objAt_eq]; exact ho.2) (hmv l a o hl ha ho.1)
  · intro l l' x x' o o' hl hl' hne hx hx' ho ho'
    simp only [reloc, Option.map_eq_some_iff] at hx hx'
    obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨a', ha', rfl⟩ := hx'
    exact hsep l l' a a' o o' hl hl' hne ha ha' ho ho'

/-- The next component, measured: `VmReprAt.globals` (a value at a fixed symbol). -/
theorem globals_reloc {c c' : Config} {pl : Place} {μ : Nat → Nat} {g : Val}
    (h : valWord pl g = some (word c Layout.sym_caml_global_data))
    (hi : word c' Layout.sym_caml_global_data = relocWord μ pl g (word c Layout.sym_caml_global_data)) :
    valWord (reloc μ pl) g = some (word c' Layout.sym_caml_global_data) :=
  (Eqv.val g fun _ => Layout.sym_caml_global_data).transport μ pl 0 0 c c' h hi


end OCaml.Pilot.Reloc
