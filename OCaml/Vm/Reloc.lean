import OCaml.Vm.Repr

/-!
# Relocation equivariance by combinators (the moving-GC representation, C3)

Adopted in abstraction-discovery round 1 (`abstractions/ROUND-1.md`, bake-off
entrant `Reloc`). Every representation component that must survive a minor
collection is written as an `Eqv` combinator term and gets `Eqv.transport`;
never prove a component's relocation invariance by hand (discipline rule O6).

A relocation `μ` acts on placements (`reloc μ pl`), on words (a pointer word
into a placed block moves block-affinely, every other word is fixed:
`relocWord`), and on memory (a configuration `c'` is the image of `c` on an
assertion's footprint: `Eqv.Img`). A representation component is built from
the combinators of `Eqv` and inherits `Eqv.transport` for free.

The laws behind it and their checked premises: `abstractions/ROUND-1.md` §2
(L3, L3′). `ScanCoherent` is the bridge to the real collector.
-/

namespace OCaml.Vm.Reloc

open OCaml.Bytecode OCaml.Vm Vsa.Machine

/-- A relocation `μ` of block addresses: every placed block moves to `μ a`. -/
def reloc (μ : Nat → Nat) (pl : Place) : Place := { pl with φ := fun l => (pl.φ l).map μ }

/-! ## 1. The combinators -/

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
    -- discipline: allow(O6-hand-relocation) the combinator layer's own atom and binder lemmas
    | some a => simp_all [valWord, reloc, relocWord]
  -- discipline: allow(O6-hand-relocation) the combinator layer's own atom and binder lemmas
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
     -- discipline: allow(O6-hand-relocation) the combinator layer's own atom and binder lemmas
     ⟨μ a, by simp [reloc, ha], E.transport μ pl a (μ a) c c' h (i a ha)⟩⟩

/-- A list-indexed family: `∀ i x, xs[i]? = some x → E i x`. -/
def list {α : Type} (xs : List α) (E : Nat → α → Eqv) : Eqv :=
  all fun i => all fun x => guard (xs[i]? = some x) (E i x)

/-- Value points-to at `f b`: the image word is the typed action's image. -/
def val (v : Val) (f : Nat → Nat) : Eqv :=
  ⟨fun pl b c => valWord pl v = some (word c (f b)),
   fun μ pl b b' c c' => word c' (f b') = relocWord μ pl v (word c (f b)),
   fun _ _ _ _ _ _ h i => by rw [i]; exact valWord_reloc h⟩

/-- A word observation may ignore bits that the runtime is allowed to change,
for example the major collector's color bits in an object header. -/
def wordView {α : Type} (f : Nat → Nat) (view : BitVec 64 → α) (R : α → Prop) : Eqv :=
  ⟨fun _ b c => R (view (word c (f b))),
   fun _ _ b b' c c' => view (word c' (f b')) = view (word c (f b)),
   fun _ _ _ _ _ _ h hi => by rw [hi]; exact h⟩

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

/-! ## 2. Values, objects, the stack -/

theorem valWord_relocates :
  ∀ (pl : Place) (μ : Nat → Nat),
    (∀ l k a, pl.φ l = some a →
      valWord (reloc μ pl) (.ptr l k) = some (BitVec.ofNat 64 (μ a + 8 * k))) ∧
    (∀ v, v.loc? = none → valWord (reloc μ pl) v = valWord pl v) := fun pl μ =>
  ⟨fun l k a h => by
    simpa [relocWord, h] using valWord_reloc (μ := μ) (w := BitVec.ofNat 64 (a + 8 * k))
      (show valWord pl (.ptr l k) = _ by simp [valWord, h]),
   fun v hv => by
    cases h : valWord pl v with
    | none => cases v <;> simp [valWord, Val.loc?] at h hv
    | some w => rw [valWord_reloc h, relocWord_fix w hv]⟩

/-- Both ordinary and partially initialized byte payloads use the same
byte-range framing law. The predicate decides which cell values are known. -/
def bytePayload {α : Type} (b : List α) (p : α → BitVec 8 → Prop) : Eqv :=
  Eqv.and (Eqv.list b fun i x => Eqv.rawB (· + i) (p x))
    (Eqv.rawB (fun a => a + 8 * (b.length / 8 + 1) - 1)
      fun y => y.toNat = 8 * (b.length / 8 + 1) - 1 - b.length)

theorem bytePayload_copyIn {α : Type} (b : List α) (p : α → BitVec 8 → Prop) :
    (bytePayload b p).CopyIn (8 * (b.length / 8 + 1)) := by
  refine Eqv.and_copyIn (Eqv.list_copyIn fun i x hx => ?_)
    (Eqv.rawB_copyIn (8 * (b.length / 8 + 1) - 1) (fun _ => by omega) (by omega))
  have := (List.getElem?_eq_some_iff.1 hx).1
  exact Eqv.rawB_copyIn i (fun _ => rfl) (by omega)

/-- An object's payload as a combinator term (mirrors `ObjAt`'s match). -/
def payload (cp : ChanPlace) : Obj → Eqv
  | .block _ fs => Eqv.list fs fun i v => Eqv.val v (· + 8 * i)
  | .bytes b => bytePayload b fun x y => y = BitVec.ofNat 8 x.toNat
  | .partialBytes b => bytePayload b fun x y => ∀ v, x = some v → y = BitVec.ofNat 8 v.toNat
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

/-- Header observations used by ObjAt; the color bits are deliberately absent. -/
def headerView (w : BitVec 64) : Nat × Nat := (w.toNat % 256, w.toNat / 1024)

/-- Allocation may choose any color without changing tag or payload size,
provided the header fits in a machine word. -/
theorem headerView_color (size tag color : Nat) (ht : tag < 256) (hc : color < 4)
    (fits : 1024 * size + 256 * color + tag < 2^64) :
    headerView (BitVec.ofNat 64 (1024 * size + 256 * color + tag)) = (tag, size) := by
  simp only [headerView, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  apply Prod.ext <;> dsimp <;> omega

def objEqv (cp : ChanPlace) (o : Obj) : Eqv :=
  Eqv.and (Eqv.wordView (· - 8) headerView fun h => h.1 = o.tag ∧ h.2 = o.wosize) (payload cp o)

theorem objAt_eq (c : Config) (pl : Place) (cp : ChanPlace) (a : Nat) (o : Obj) :
    ObjAt c pl cp a o = (objEqv cp o).P pl a c := by cases o <;> rfl

theorem payload_copyIn (cp : ChanPlace) (o : Obj) (hnb : ∀ t fs, o ≠ .block t fs) :
    (payload cp o).CopyIn (8 * o.wosize) := by
  cases o with
  | block t fs => exact absurd rfl (hnb t fs)
  | bytes b => exact bytePayload_copyIn b _
  | partialBytes b => exact bytePayload_copyIn b _
  | double d =>
    show (Eqv.rawW (fun a => a) (· = d)).CopyIn (8 * 1)
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

/-- H6's premises: header shape preserved (recoloring allowed), fields
relocated, and exactly the raw payload copied. -/
structure ObjMoved (c c' : Config) (pl : Place) (μ : Nat → Nat) (a : Nat) (o : Obj) : Prop where
  header : headerView (word c' (μ a - 8)) = headerView (word c (a - 8))
  fields : ∀ t fs, o = .block t fs → ∀ i v, fs[i]? = some v →
    valWord (reloc μ pl) v = some (word c' (μ a + 8 * i))
  raw : (∀ t fs, o ≠ .block t fs) → Copied c c' a (μ a) (8 * o.wosize)

theorem objImg {c c' pl cp μ a o} (h : ObjAt c pl cp a o) (m : ObjMoved c c' pl μ a o) :
    (objEqv cp o).Img μ pl a (μ a) c c' := by
  rw [objAt_eq] at h
  refine ⟨m.header, ?_⟩
  by_cases hb : ∃ t fs, o = .block t fs
  · obtain ⟨t, fs, rfl⟩ := hb; exact Eqv.list_val_img h.2 (m.fields t fs rfl)
  · have hnb : ∀ t fs, o ≠ .block t fs := fun t fs e => hb ⟨t, fs, e⟩
    exact payload_copyIn cp o hnb μ pl a (μ a) c c' h.2 (m.raw hnb)

theorem objAt_reloc :
  ∀ (c c' : Vsa.Machine.Config) (pl : Place) (cp : ChanPlace) (μ : Nat → Nat) (a : Nat) (o : Obj),
    ObjAt c pl cp a o →
    8 ≤ μ a →
    headerView (word c' (μ a - 8)) = headerView (word c (a - 8)) →
    (∀ t fs, o = .block t fs → ∀ i v, fs[i]? = some v →
      valWord (reloc μ pl) v = some (word c' (μ a + 8 * i))) →
    ((∀ t fs, o ≠ .block t fs) → ∀ j, j < 8 * o.wosize → byte c' (μ a + j) = byte c (a + j)) →
    ObjAt c' (reloc μ pl) cp (μ a) o := by
  intro c c' pl cp μ a o h _ hhdr hf hraw
  have m : ObjMoved c c' pl μ a o := ⟨hhdr, hf, fun hnb j hj => hraw hnb j hj⟩
  have := (objEqv cp o).transport μ pl a (μ a) c c' (by rw [← objAt_eq]; exact h) (objImg h m)
  rwa [← objAt_eq] at this

def stackEqv (high : Nat) (stk : List Val) : Eqv :=
  Eqv.and (Eqv.pure fun sp => sp + 8 * stk.length = high) (Eqv.list stk fun i v => Eqv.val v (· + 8 * i))

theorem stackRepr_reloc :
  ∀ (c c' : Vsa.Machine.Config) (pl : Place) (μ : Nat → Nat) (sp high : Nat) (stk : List Val),
    StackRepr c pl sp high stk →
    (∀ i v, stk[i]? = some v → valWord (reloc μ pl) v = some (word c' (sp + 8 * i))) →
    StackRepr c' (reloc μ pl) sp high stk := fun c c' pl μ sp high stk h hv =>
  (stackEqv high stk).transport μ pl sp sp c c' h ⟨h.1, Eqv.list_val_img h.2 hv⟩

/-! ## 3. The heap and the globals -/

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
    -- discipline: allow(O6-hand-relocation) the combinator layer's own atom and binder lemmas
    simp only [reloc, Option.map_eq_some_iff] at hx hx'
    obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨a', ha', rfl⟩ := hx'
    exact hsep l l' a a' o o' hl hl' hne ha ha' ho ho'

/-- The next component, measured: `VmReprAt.globals` (a value at a fixed symbol). -/
theorem globals_reloc {c c' : Config} {pl : Place} {μ : Nat → Nat} {g : Val}
    (h : valWord pl g = some (word c Layout.sym_caml_global_data))
    (hi : word c' Layout.sym_caml_global_data = relocWord μ pl g (word c Layout.sym_caml_global_data)) :
    valWord (reloc μ pl) g = some (word c' Layout.sym_caml_global_data) :=
  (Eqv.val g fun _ => Layout.sym_caml_global_data).transport μ pl 0 0 c c' h hi


/-! ## 4. Remaining loop-head components

`observe` frames machine facts that do not depend on placement. `atCode`
uses the fixed code base; neither asks for the post-representation as its
image. Registers holding values use the same typed word action as memory.
-/

namespace Eqv

def observe {α : Type} (read : Config → α) (R : α → Prop) : Eqv :=
  ⟨fun _ _ c => R (read c), fun _ _ _ _ c c' => read c' = read c,
   fun _ _ _ _ _ _ h hi => by rw [hi]; exact h⟩

def atCode (E : Eqv) : Eqv :=
  ⟨fun pl _ c => E.P pl pl.codeBase c,
   fun μ pl _ _ c c' => E.Img μ pl pl.codeBase pl.codeBase c c',
   fun μ pl _ _ c c' h hi => E.transport μ pl pl.codeBase pl.codeBase c c' h hi⟩

/-- The atom-table allocation is static across heap relocation. -/
def atAtoms (E : Eqv) : Eqv :=
  ⟨fun pl _ c => E.P pl pl.atomBase c,
   fun μ pl _ _ c c' => E.Img μ pl pl.atomBase pl.atomBase c c',
   fun μ pl _ _ c c' h hi => E.transport μ pl pl.atomBase pl.atomBase c c' h hi⟩

/-- An optional value observation, shared by all value registers. -/
def valRead (v : Val) (read : Config → Option (BitVec 64)) : Eqv :=
  ⟨fun pl _ c => ∃ w, read c = some w ∧ valWord pl v = some w,
   fun μ pl _ _ c c' => read c' = (read c).map (relocWord μ pl v),
   fun _ _ _ _ _ _ ⟨w, hr, hw⟩ hi =>
     ⟨_, by rw [hi, hr]; rfl, valWord_reloc hw⟩⟩

end Eqv

/-- Channels are malloc'd structures, not moving OCaml heap blocks. -/
def chanEqv (a : Nat) (ch : Chan) : Eqv :=
  Eqv.and (Eqv.rawW32 (fun _ => a + chanOffFd) (·.toInt = ch.fd)) <|
  Eqv.and (Eqv.rawW (fun _ => a + chanOffOffset) (·.toInt = ch.offset)) <|
  Eqv.and (Eqv.rawW (fun _ => a + chanOffCurr)
    (·.toNat = a + chanOffBuff + ch.cursor)) <|
  Eqv.and (Eqv.rawW (fun _ => a + chanOffMax)
    (·.toNat = (if ch.fd = -1 then a + chanOffBuff + ioBufferSize else if ch.isOut then 0 else a + chanOffBuff + ch.inBuf.length))) <|
  Eqv.and (Eqv.rawW (fun _ => a + chanOffEnd) (·.toNat = a + chanOffBuff + ioBufferSize)) <|
  Eqv.and (Eqv.rawW32 (fun _ => a + chanOffFlags) (· &&& chanFlagUnbuffered = 0#32)) <|
  Eqv.and (Eqv.list ch.buffer fun i b => Eqv.rawB (fun _ => a + chanOffBuff + i)
    (· = BitVec.ofNat 8 b.toNat)) (Eqv.pure fun _ => ch.cursor ≤ ioBufferSize ∧ ch.buffer.length ≤ ioBufferSize ∧ a % 8 = 0)

def worldEqv (cp : ChanPlace) (w : World) : Eqv :=
  Eqv.and (Eqv.observe (fun c => output c.σ) (· = bytesToString w.console)) <|
  Eqv.and (Eqv.all fun id => Eqv.all fun ch => Eqv.guard (w.chans[id]? = some ch) <|
    Eqv.ex fun a => Eqv.and (Eqv.pure fun _ => cp id = some a) (chanEqv a ch)) <|
  Eqv.rawW (fun _ => Layout.sym_oo_last_id) (· = tag64 (BitVec.ofNat 63 w.ooId))

def pcEqv (pc : Nat) : Eqv :=
  Eqv.atCode <| Eqv.ex fun base =>
    Eqv.and (Eqv.pure (· = base))
      (Eqv.observe (fun c => gpr c Layout.reg_pc)
        (· = some (BitVec.ofNat 64 (base + 4 * pc))))

def codeBaseEqv : Eqv :=
  Eqv.atCode <| Eqv.ex fun base =>
    Eqv.and (Eqv.pure (· = base))
      (Eqv.rawW (fun _ => Layout.sym_caml_start_code) (·.toNat = base))

def atomBaseEqv : Eqv :=
  Eqv.atAtoms <| Eqv.ex fun base =>
    Eqv.and (Eqv.pure (· = base))
      (Eqv.rawW (fun _ => Layout.sym_caml_atom_table) (·.toNat = base))

def codeEqv (P : Prog) : Eqv :=
  Eqv.atCode <| Eqv.all fun i => Eqv.all fun w => Eqv.guard (P.code[i]? = some w) <|
    Eqv.rawW32 (· + 4 * i) (· = w)

/-- Caml_state is fixed during a minor collection; the observation includes
both the pointer load and its selected field. -/
def domainFieldEqv (off value : Nat) : Eqv :=
  Eqv.observe (fun c => (word c ((word c Layout.sym_Caml_state).toNat + off)).toNat)
    (· = value)

/-- Primitive targets are observations of fixed runtime metadata and code
pointers. Relocation renames no abstract location in this component. -/
def primitiveBindingsEqv (P : Prog) : Eqv :=
  Eqv.all fun i => Eqv.all fun name => Eqv.guard (P.prims[i]? = some name) <|
    Eqv.observe (fun c => primitiveTarget c i)
      (fun target => ∃ entry, PrimitiveEntries.lookup name = some entry ∧ target = BitVec.ofNat 64 entry)

/-- Images the machine collector must establish at its return to dispatch.
This is a conditional transport interface, not a collector execution proof. -/
structure VmImage (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) (μ : Nat → Nat) (c c' : Config) : Prop where
  atHead : (Eqv.observe pcOf (· = some (BitVec.ofNat 64 Layout.loopHead))).Img μ pl 0 0 c c'
  pc : (pcEqv s.pc).Img μ pl 0 0 c c'
  spReg : (Eqv.observe (fun c => gpr c Layout.reg_sp) (· = some (BitVec.ofNat 64 sp))).Img μ pl 0 0 c c'
  accu : (Eqv.valRead s.accu (fun c => gpr c Layout.reg_accu)).Img μ pl 0 0 c c'
  env : (Eqv.valRead s.env (fun c => gpr c Layout.reg_env)).Img μ pl 0 0 c c'
  extra : (Eqv.observe (fun c => gpr c Layout.reg_extra) (· = some (BitVec.ofNat 64 s.extra))).Img μ pl 0 0 c c'
  stackHigh : (domainFieldEqv Layout.off_stack_high high).Img μ pl 0 0 c c'
  trapsp : (domainFieldEqv Layout.off_trapsp (high - 8 * s.trap)).Img μ pl 0 0 c c'
  codeBase : codeBaseEqv.Img μ pl 0 0 c c'
  code : (codeEqv P).Img μ pl 0 0 c c'
  globals : (Eqv.val P.globals (fun _ => Layout.sym_caml_global_data)).Img μ pl 0 0 c c'
  stack : (stackEqv high s.stack).Img μ pl sp sp c c'
  heap : (heapEqv cp P s).Img μ pl 0 0 c c'
  world : (worldEqv cp s.world).Img μ pl 0 0 c c'
  primitives : (primitiveBindingsEqv P).Img μ pl 0 0 c c'
  atomBase : atomBaseEqv.Img μ pl 0 0 c c'

/-- All loop-head fields transport via Eqv, including code, registers,
trap-stack metadata, channels, and console output. -/
theorem vmReprAt_reloc {P s c c' pl cp sp high μ}
    (h : VmReprAt P s c pl cp sp high) (hi : VmImage P s pl cp sp high μ c c') :
    VmReprAt P s c' (reloc μ pl) cp sp high := by
  have pcPre : (pcEqv s.pc).P pl 0 c := ⟨pl.codeBase, rfl, h.pc⟩
  have basePre : codeBaseEqv.P pl 0 c := ⟨pl.codeBase, rfl, h.codeBase⟩
  obtain ⟨base, hb, hp⟩ := (pcEqv s.pc).transport μ pl 0 0 c c' pcPre hi.pc
  obtain ⟨base', hb', hp'⟩ := codeBaseEqv.transport μ pl 0 0 c c' basePre hi.codeBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Eqv.observe pcOf (· = some (BitVec.ofNat 64 Layout.loopHead))).transport μ pl 0 0 c c' h.atHead hi.atHead
  · change (reloc μ pl).codeBase = base at hb
    change gpr c' Layout.reg_pc = some (BitVec.ofNat 64 (base + 4 * s.pc)) at hp
    rw [hb]; exact hp
  · exact (Eqv.observe (fun c => gpr c Layout.reg_sp) (· = some (BitVec.ofNat 64 sp))).transport μ pl 0 0 c c' h.spReg hi.spReg
  · exact (Eqv.valRead s.accu (fun c => gpr c Layout.reg_accu)).transport μ pl 0 0 c c' h.accu hi.accu
  · exact (Eqv.valRead s.env (fun c => gpr c Layout.reg_env)).transport μ pl 0 0 c c' h.env hi.env
  · exact (Eqv.observe (fun c => gpr c Layout.reg_extra) (· = some (BitVec.ofNat 64 s.extra))).transport μ pl 0 0 c c' h.extra hi.extra
  · exact (domainFieldEqv Layout.off_stack_high high).transport μ pl 0 0 c c' h.stackHigh hi.stackHigh
  · exact (domainFieldEqv Layout.off_trapsp (high - 8 * s.trap)).transport μ pl 0 0 c c' h.trapsp hi.trapsp
  · change (reloc μ pl).codeBase = base' at hb'
    change (word c' Layout.sym_caml_start_code).toNat = base' at hp'
    rw [hb']; exact hp'
  · exact (codeEqv P).transport μ pl 0 0 c c' h.code hi.code
  · exact (Eqv.val P.globals (fun _ => Layout.sym_caml_global_data)).transport μ pl 0 0 c c' h.globals hi.globals
  · exact (stackEqv high s.stack).transport μ pl sp sp c c' h.stack hi.stack
  · exact (heapRepr_iff _ _ _ _ _).2 <|
      (heapEqv cp P s).transport μ pl 0 0 c c' ((heapRepr_iff _ _ _ _ _).1 h.heap) hi.heap
  · exact (worldEqv cp s.world).transport μ pl 0 0 c c' h.world hi.world
  · exact ⟨(primitiveBindingsEqv P).transport μ pl 0 0 c c' h.primitives.targets hi.primitives⟩
  · have pre : atomBaseEqv.P pl 0 c := ⟨pl.atomBase, rfl, h.atomBase⟩
    obtain ⟨base, hb, hp⟩ := atomBaseEqv.transport μ pl 0 0 c c' pre hi.atomBase
    change (reloc μ pl).atomBase = base at hb
    change (word c' Layout.sym_caml_atom_table).toNat = base at hp
    rw [hb]; exact hp

end OCaml.Vm.Reloc
