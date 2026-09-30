/-!
# The run kernel: one run algebra for every deterministic step function

Adopted in abstraction-discovery round 1 (`abstractions/ROUND-1.md`, bake-off
entrant `RunKernel`). A deterministic system is a step function
`f : C → Except O C`: `.ok c'` continues at `c'`, `.error o` stops with
outcome `o` (halted, stuck, unsupported, wrong, …). `iter f n` is the fuel
iterate, absorbing on a stop. Every run law (shift, absorb, unique outcome,
prefix, halts-or-diverges, the `Bad`-filtered trichotomy, closure) is proved
ONCE here, about `iter`.

An existing run relation enters by a *presentation*, never by re-proving
its algebra:

* `Graph f S`: the one-step relation `S` is the graph of `f`'s continue case;
* `ConsPres S R`: `R : ℕ → C → C → Prop` is cons-style (`StepsN`, `ReachesN`);
* `SnocPres S R`: snoc-style;
* `ClosPres S R`: an unindexed closure (`Steps`, `Reaches`), via its induction.

`ConsPres.iff`, `SnocPres.iff` and `ClosPres.iff` turn the relation into
`iter`. Lossy lockstep squares between systems (`bcModel` collapses
`unsupported`/`wrong` to `stuck`) transport by `iter_transport`.

The system adapters live beside each system: `OCaml.Bytecode.bcK`
(`Semantics.lean`), `OCaml.Run.vsaK` (`OCaml/Run/Machine.lean`), and
`OCaml.Run.mmK` for any `VsaIris.MachineModel` (`OCaml/Run/Model.lean`).
-/

namespace OCaml.Run


section Kernel
variable {C O : Type} (f : C → Except O C)

/-- Fuel iterate, cons style: step first, then `n` more. -/
def iter : Nat → C → Except O C
  | 0, c => .ok c
  | n + 1, c => f c >>= iter n

/-- Reachable in some number of steps. -/
def Reach (c d : C) : Prop := ∃ n, iter f n c = .ok d
/-- Runs to a state whose step is `done o`. -/
def HaltsK (c : C) (o : O) : Prop := ∃ d, Reach f c d ∧ f d = .error o
/-- Every fuel still continues. -/
def DivK (c : C) : Prop := ∀ n, ∃ d, iter f n c = .ok d

variable {f}

theorem bind_assoc' {α β γ : Type} (x : Except O α) (g : α → Except O β) (h : β → Except O γ) :
    (x >>= g) >>= h = x >>= fun a => g a >>= h := by cases x <;> rfl

/-- Shift: `iter (m+n) = iter m ≫= iter n`. -/
theorem iter_add (m n : Nat) (c : C) : iter f (m + n) c = iter f m c >>= iter f n := by
  induction m generalizing c with
  | zero => simp only [Nat.zero_add, iter]; rfl
  | succ m ih =>
    rw [Nat.succ_add]; simp only [iter]; rw [bind_assoc']; congr; funext d; exact ih d

theorem iter_one (c : C) : iter f 1 c = f c := by
  show f c >>= _ = _; cases f c <;> rfl

/-- Snoc form of the iterate. -/
theorem iter_succ' (n : Nat) (c : C) : iter f (n + 1) c = iter f n c >>= f := by
  rw [iter_add]; congr; funext d; exact iter_one d

/-- Absorb: done at `m` stays done. -/
theorem iter_absorb {m : Nat} {c : C} {o : O} (h : iter f m c = .error o) (k : Nat) :
    iter f (m + k) c = .error o := by rw [iter_add, h]; rfl

theorem iter_absorb_le {m n : Nat} {c : C} {o : O} (h : iter f m c = .error o) (hle : m ≤ n) :
    iter f n c = .error o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle; exact iter_absorb h k

/-- Unique outcome (via `max`). -/
theorem iter_error_unique {m n : Nat} {c : C} {o o' : O}
    (h : iter f m c = .error o) (h' : iter f n c = .error o') : o = o' := by
  have a := iter_absorb_le h (Nat.le_max_left m n)
  rw [iter_absorb_le h' (Nat.le_max_right m n)] at a; cases a; rfl

/-- A continuing fuel is below every done fuel. -/
theorem iter_ok_lt {m n : Nat} {c d : C} {o : O}
    (h : iter f m c = .error o) (h' : iter f n c = .ok d) : n < m :=
  Nat.lt_of_not_le fun hle => by rw [iter_absorb_le h hle] at h'; cases h'

/-- Prefix: a continuing run passes through every earlier fuel. -/
theorem iter_prefix {m k : Nat} {c e : C} (h : iter f (m + k) c = .ok e) :
    ∃ d, iter f m c = .ok d := by
  rw [iter_add] at h
  cases hm : iter f m c with
  | ok d => exact ⟨d, rfl⟩
  | error o => rw [hm] at h; cases h

/-- Stop: a stopped state has no continuation one step later. -/
theorem iter_stop {n : Nat} {a b : C} (h : iter f n a = .ok b) (hs : ∀ x, f b ≠ .ok x) (d : C) :
    iter f (n + 1) a ≠ .ok d := by
  rw [iter_succ', h]; exact hs d

theorem haltsK_iff {c : C} {o : O} : HaltsK f c o ↔ ∃ n, iter f n c = .error o := by
  constructor
  · rintro ⟨d, ⟨n, hn⟩, hd⟩; exact ⟨n + 1, by rw [iter_succ', hn]; exact hd⟩
  · rintro ⟨n, hn⟩
    induction n with
    | zero => cases hn
    | succ n ih =>
      rw [iter_succ'] at hn
      cases hm : iter f n c with
      | ok d => rw [hm] at hn; exact ⟨d, ⟨n, hm⟩, hn⟩
      | error o' => rw [hm] at hn; cases hn; exact ih hm

theorem HaltsK.unique {c : C} {o o' : O} (h : HaltsK f c o) (h' : HaltsK f c o') : o = o' := by
  obtain ⟨m, hm⟩ := haltsK_iff.1 h; obtain ⟨n, hn⟩ := haltsK_iff.1 h'
  exact iter_error_unique hm hn

theorem HaltsK.not_div {c : C} {o : O} (h : HaltsK f c o) : ¬ DivK f c := fun hd => by
  obtain ⟨m, hm⟩ := haltsK_iff.1 h; obtain ⟨d, hd⟩ := hd m; rw [hm] at hd; cases hd

theorem halts_or_div (c : C) : (∃ o, HaltsK f c o) ∨ DivK f c := by
  refine (Classical.em (DivK f c)).elim .inr fun hd => .inl ?_
  obtain ⟨n, hn⟩ := Classical.not_forall.1 hd
  cases h : iter f n c with
  | ok d => exact (hn ⟨d, h⟩).elim
  | error o => exact ⟨o, haltsK_iff.2 ⟨n, h⟩⟩

theorem Reach.trans {a b c : C} : Reach f a b → Reach f b c → Reach f a c :=
  fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, by rw [iter_add, hm]; exact hn⟩

theorem HaltsK.of_reach {a b : C} {o : O} (h : Reach f a b) : HaltsK f b o → HaltsK f a o :=
  fun ⟨d, hr, hd⟩ => ⟨d, h.trans hr, hd⟩

/-- Trichotomy, parametrised by the `Bad` outcomes: if the run never ends
Bad, it diverges iff it does not end Good. -/
theorem div_iff_not_halts (Bad : O → Prop) {c : C} (hb : ∀ o, HaltsK f c o → ¬ Bad o) :
    DivK f c ↔ ¬ ∃ o, ¬ Bad o ∧ HaltsK f c o :=
  ⟨fun hd ⟨_, _, h⟩ => h.not_div hd, fun hn => (halts_or_div c).elim
    (fun ⟨o, h⟩ => (hn ⟨o, hb o h, h⟩).elim) id⟩

end Kernel

/-! ### Presentations -/

section Pres
variable {C O : Type}

/-- The one-step relation `S` is the graph of `f`'s continue case. -/
structure Graph (f : C → Except O C) (S : C → C → Prop) : Prop where
  iff : ∀ {a b}, S a b ↔ f a = .ok b

/-- `R` is a cons-style `n`-step relation over `S`. -/
structure ConsPres (S : C → C → Prop) (R : Nat → C → C → Prop) : Prop where
  nil : ∀ c, R 0 c c
  cons : ∀ {n a b c}, S a b → R n b c → R (n + 1) a c
  inv : ∀ {n a c}, R n a c → (n = 0 ∧ a = c) ∨ ∃ m b, n = m + 1 ∧ S a b ∧ R m b c

/-- `R` is a snoc-style `n`-step relation over `S`. -/
structure SnocPres (S : C → C → Prop) (R : Nat → C → C → Prop) : Prop where
  nil : ∀ c, R 0 c c
  snoc : ∀ {n a b c}, R n a b → S b c → R (n + 1) a c
  inv : ∀ {n a c}, R n a c → (n = 0 ∧ a = c) ∨ ∃ m b, n = m + 1 ∧ R m a b ∧ S b c

/-- `R` is the reflexive-transitive closure of `S` (with its induction). -/
structure ClosPres (S : C → C → Prop) (R : C → C → Prop) : Prop where
  refl : ∀ c, R c c
  head : ∀ {a b c}, S a b → R b c → R a c
  ind : ∀ (Q : C → C → Prop), (∀ c, Q c c) → (∀ {a b c}, S a b → R b c → Q b c → Q a c) →
    ∀ {a c}, R a c → Q a c

variable {f : C → Except O C} {S : C → C → Prop}

theorem ConsPres.iff {R : Nat → C → C → Prop} (g : Graph f S) (p : ConsPres S R) {n : Nat} {a c : C} :
    R n a c ↔ iter f n a = .ok c := by
  induction n generalizing a with
  | zero =>
    refine ⟨fun h => ?_, fun h => by cases h; exact p.nil _⟩
    rcases p.inv h with ⟨-, rfl⟩ | ⟨_, _, h, -⟩
    · rfl
    · cases h
  | succ n ih =>
    constructor
    · intro h
      rcases p.inv h with ⟨h, -⟩ | ⟨m, b, hm, hs, hr⟩
      · cases h
      · cases hm; show f a >>= _ = _; rw [g.iff.1 hs]; exact ih.1 hr
    · intro h
      change f a >>= _ = _ at h
      cases hf : f a with
      | ok b => rw [hf] at h; exact p.cons (g.iff.2 hf) (ih.2 h)
      | error o => rw [hf] at h; cases h

theorem SnocPres.iff {R : Nat → C → C → Prop} (g : Graph f S) (p : SnocPres S R) {n : Nat} {a c : C} :
    R n a c ↔ iter f n a = .ok c := by
  induction n generalizing c with
  | zero =>
    refine ⟨fun h => ?_, fun h => by cases h; exact p.nil _⟩
    rcases p.inv h with ⟨-, rfl⟩ | ⟨_, _, h, -⟩
    · rfl
    · cases h
  | succ n ih =>
    rw [iter_succ']
    constructor
    · intro h
      rcases p.inv h with ⟨h, -⟩ | ⟨m, b, hm, hr, hs⟩
      · cases h
      · cases hm; rw [ih.1 hr]; exact g.iff.1 hs
    · intro h
      cases hi : iter f n a with
      | ok b => rw [hi] at h; exact p.snoc (ih.2 hi) (g.iff.2 h)
      | error o => rw [hi] at h; cases h

theorem ClosPres.iff {R : C → C → Prop} (g : Graph f S) (p : ClosPres S R) {a c : C} :
    R a c ↔ Reach f a c := by
  constructor
  · exact p.ind (fun a c => Reach f a c) (fun c => ⟨0, rfl⟩) fun {a _ _} s _ ⟨n, hn⟩ =>
      ⟨n + 1, by show f a >>= _ = _; rw [g.iff.1 s]; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero => cases hn; exact p.refl _
    | succ n ih =>
      change f a >>= _ = _ at hn
      cases hf : f a with
      | ok b => rw [hf] at hn; exact p.head (g.iff.2 hf) (ih hn)
      | error o => rw [hf] at hn; cases hn

end Pres

/-! ### Lossy lockstep transport -/

/-- Map the continue side by `e` and the outcome side by `g`. -/
def mapOut {C₁ C₂ O₁ O₂ : Type} (e : C₁ → C₂) (g : O₁ → O₂) : Except O₁ C₁ → Except O₂ C₂
  | .ok c => .ok (e c)
  | .error o => .error (g o)

theorem iter_transport {C₁ C₂ O₁ O₂ : Type} {f₁ : C₁ → Except O₁ C₁} {f₂ : C₂ → Except O₂ C₂}
    (e : C₁ → C₂) (g : O₁ → O₂) (sq : ∀ c, f₂ (e c) = mapOut e g (f₁ c)) (n : Nat) (c : C₁) :
    iter f₂ n (e c) = mapOut e g (iter f₁ n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    show f₂ (e c) >>= _ = mapOut e g (f₁ c >>= _)
    rw [sq]; cases f₁ c <;> first | rfl | exact ih _

theorem mapOut_ok {C₁ C₂ O₁ O₂ : Type} {e : C₁ → C₂} {g : O₁ → O₂} {x : Except O₁ C₁} {d : C₂}
    (h : mapOut e g x = .ok d) : ∃ c, x = .ok c ∧ e c = d := by
  cases x with
  | ok c => cases h; exact ⟨c, rfl, rfl⟩
  | error o => cases h

theorem mapOut_error {C₁ C₂ O₁ O₂ : Type} {e : C₁ → C₂} {g : O₁ → O₂} {x : Except O₁ C₁} {o : O₂}
    (h : mapOut e g x = .error o) : ∃ o₁, x = .error o₁ ∧ g o₁ = o := by
  cases x with
  | ok c => cases h
  | error o₁ => cases h; exact ⟨o₁, rfl, rfl⟩

end OCaml.Run
