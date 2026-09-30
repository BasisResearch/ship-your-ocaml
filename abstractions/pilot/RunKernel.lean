import Pilot

/-!
# RunKernel: one run algebra for every deterministic step function

Bake-off entrant `RunKernel` (abstraction discovery round 1).

A deterministic system is a step function `f : C → Except O C`: `.ok c'` is
"continue at `c'`", `.error o` is "done with outcome `o`" (halted, stuck,
unsupported, …). `Except` is used as the two-constructor sum because core
already gives it `bind`. `iter f n` is the fuel iterate (absorbing on done).
All run laws are proved ONCE here about `iter`. Each existing run relation
enters by a *presentation*:

* `Graph f S` — the one-step relation `S` is the graph of `f`'s continue case;
* `ConsPres S R` — `R : ℕ → C → C → Prop` is cons-style (`StepsN`, `ReachesN`);
* `SnocPres S R` — snoc style;
* `ClosPres S R` — unindexed closure (`Steps`, `Reaches`), via its induction.

`ConsPres.iff` / `SnocPres.iff` / `ClosPres.iff` turn each relation into
`iter`, where all the algebra lives. Each system supplies a kernel adapter
(`mmK` for any `VsaIris.MachineModel`, `bcK` for `BcSem`, `vsaK` for the
RISC-V machine) plus its presentations; that is the per-system cost.
-/

namespace RunKernel

/-! ## Section 1: the abstraction (SETUP) -/

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

/-! ### Adapters (one per system) -/

/-- Any `VsaIris.MachineModel` as a kernel; outcome `none` is `stuck`. -/
def mmK (M : VsaIris.MachineModel) (σ : M.State) : Except (Option (Nat × String)) M.State :=
  match M.step σ with
  | .next σ' => .ok σ'
  | .halt e out => .error (some (e, out))
  | .stuck => .error none

theorem mmK_graph (M : VsaIris.MachineModel) : Graph (mmK M) (fun a b => M.step a = .next b) :=
  ⟨fun {a _} => by unfold mmK; split <;> simp_all⟩

theorem mmK_halt {M : VsaIris.MachineModel} {σ : M.State} {e : Nat} {out : String} :
    M.step σ = .halt e out ↔ mmK M σ = .error (some (e, out)) := by unfold mmK; split <;> simp_all

theorem reachesN_pres (M : VsaIris.MachineModel) :
    ConsPres (fun a b => M.step a = .next b) (VsaIris.ReachesN M) :=
  ⟨.zero, .succ, fun h => by cases h <;> simp_all⟩

theorem reaches_pres (M : VsaIris.MachineModel) :
    ClosPres (fun a b => M.step a = .next b) (VsaIris.Reaches M) :=
  ⟨.refl, .step, fun _ h0 h1 _ _ h => by induction h with
    | refl => exact h0 _
    | step s r ih => exact h1 s r ih⟩

theorem mm_halts_iff {M : VsaIris.MachineModel} {σ : M.State} {e : Nat} {out : String} :
    VsaIris.Halts M σ e out ↔ HaltsK (mmK M) σ (some (e, out)) := by
  simp only [VsaIris.Halts, HaltsK, (reaches_pres M).iff (mmK_graph M), mmK_halt]

open OCaml.Bytecode in
/-- `BcSem` of `P` as a kernel; the outcome is the whole non-`next` result. -/
def bcK (P : Prog) (s : St) : Except Res St :=
  match step P s with
  | .next s' => .ok s'
  | r => .error r

open OCaml.Bytecode in
theorem bcK_graph (P : Prog) : Graph (bcK P) (Step P) :=
  ⟨fun {a _} => ⟨fun ⟨h⟩ => by simp [bcK, h], fun h => ⟨by unfold bcK at h; split at h <;> simp_all⟩⟩⟩

open OCaml.Bytecode in
theorem bcK_error {P : Prog} {s : St} {o : Res} (h : bcK P s = .error o) : step P s = o := by
  unfold bcK at h; split at h <;> simp_all

open OCaml.Bytecode in
theorem bcK_halt {P : Prog} {s : St} {e : Nat} {w : World} (h : step P s = .halt e w) :
    bcK P s = .error (.halt e w) := by simp [bcK, h]

open OCaml.Bytecode in
theorem stepsN_pres (P : Prog) : ConsPres (Step P) (StepsN P) :=
  ⟨.zero, .succ, fun h => by cases h with | zero => exact .inl ⟨rfl, rfl⟩ | succ s r => exact .inr ⟨_, _, rfl, s, r⟩⟩

open Vsa.Machine in
/-- The RISC-V machine as a kernel; outcome `some (e, σ)` is an HTIF exit,
`none` anything else (Sail error, exit without code). -/
def vsaK (c : Config) : Except (Option (Nat × MState)) Config :=
  match (Vsa.stepOnce c.tick c.steps).run c.σ with
  | .ok (.inr (i', u')) σ' => .ok ⟨σ', i', u'⟩
  | .ok (.inl (some e, _)) σ' => .error (some (e, σ'))
  | _ => .error none

open Vsa.Machine in
theorem vsaK_graph : Graph vsaK Step :=
  ⟨fun {a _} => ⟨fun ⟨h⟩ => by simp [vsaK, h], fun h => by
    obtain ⟨σ, i, u⟩ := a; unfold vsaK at h; split at h <;> (try cases h) <;> exact .mk ‹_›⟩⟩

open Vsa.Machine in
theorem vsaK_halted {c : Config} {e : Nat} {σ : MState} :
    Halted c e σ ↔ vsaK c = .error (some (e, σ)) :=
  ⟨fun ⟨h⟩ => by simp [vsaK, h], fun h => by
    obtain ⟨σ, i, u⟩ := c; unfold vsaK at h; split at h <;> (try cases h) <;> exact .mk ‹_›⟩

theorem vsaStepsN_pres : ConsPres Vsa.Machine.Step Vsa.Machine.StepsN :=
  ⟨.zero, .succ, fun h => by cases h with | zero => exact .inl ⟨rfl, rfl⟩ | succ s r => exact .inr ⟨_, _, rfl, s, r⟩⟩

theorem vsaSteps_pres : ClosPres Vsa.Machine.Step Vsa.Machine.Steps :=
  ⟨.refl, .head, fun _ h0 h1 _ _ h => by induction h with
    | refl => exact h0 _
    | head s r ih => exact h1 s r ih⟩

/-! ### Per-system bridges (behaviours as kernel predicates) -/

open OCaml.Bytecode in
theorem bc_iff {P : Prog} {n : Nat} {a b : St} : StepsN P n a b ↔ iter (bcK P) n a = .ok b :=
  (stepsN_pres P).iff (bcK_graph P)

open OCaml.Bytecode in
theorem bcK_not_next {P : Prog} {s s' : St} : bcK P s ≠ .error (.next s') := by
  unfold bcK; split <;> simp_all

open OCaml.Bytecode in
theorem bcDiv_iff {P : Prog} : BcDiverges P ↔ DivK (bcK P) P.init :=
  forall_congr' fun _ => exists_congr fun _ => bc_iff

open OCaml.Bytecode in
theorem bcHalts_iff {P : Prog} {out : String} {e : Nat} :
    BcHalts P out e ↔ ∃ w, HaltsK (bcK P) P.init (.halt e w) ∧ bytesToString w.console = out :=
  ⟨fun ⟨s, w, ⟨n, hn⟩, hst, ho⟩ => ⟨w, ⟨s, ⟨n, bc_iff.1 hn⟩, bcK_halt hst⟩, ho⟩,
   fun ⟨w, ⟨s, ⟨n, hn⟩, hs⟩, ho⟩ => ⟨s, w, ⟨n, bc_iff.2 hn⟩, bcK_error hs, ho⟩⟩

open OCaml.Bytecode in
/-- `Good` excludes the bad outcomes of the `BcSem` kernel. -/
theorem good_halt {P : Prog} (hg : Good P) {o : Res} (h : HaltsK (bcK P) P.init o) :
    ∃ e w, o = .halt e w := by
  obtain ⟨s, ⟨n, hn⟩, hs⟩ := h
  obtain ⟨hu, hw⟩ := hg s ⟨n, bc_iff.2 hn⟩
  have hst := bcK_error hs
  cases o with
  | next s' => exact (bcK_not_next hs).elim
  | halt e w => exact ⟨e, w, rfl⟩
  | unsupported => exact (hu hst).elim
  | wrong => exact (hw hst).elim

open OCaml.Bytecode in
/-- `bcModel`'s lossy outcome map (unsupported/wrong collapse to stuck). -/
def gBc : Res → Option (Nat × String)
  | .halt e w => some (e, bytesToString w.console)
  | _ => none

open OCaml.Bytecode OCaml.Logic in
theorem bcModel_square (P : Prog) (s : St) : mmK (bcModel P) s = mapOut id gBc (bcK P s) := by
  unfold mmK bcK bcModel; dsimp only; cases step P s <;> rfl

theorem vsa_iffN {n : Nat} {a b : Vsa.Machine.Config} :
    Vsa.Machine.StepsN n a b ↔ iter vsaK n a = .ok b := vsaStepsN_pres.iff vsaK_graph

theorem vsa_iffS {a b : Vsa.Machine.Config} : Vsa.Machine.Steps a b ↔ Reach vsaK a b :=
  vsaSteps_pres.iff vsaK_graph

theorem vsaDiv_iff {c : Vsa.Machine.Config} : Vsa.Machine.Diverges c ↔ DivK vsaK c :=
  forall_congr' fun _ => exists_congr fun _ => vsa_iffN

open Vsa.Machine in
theorem vsaHalts_iff {c : Config} {out : String} {e : Nat} :
    Halts c out e ↔ ∃ σ, HaltsK vsaK c (some (e, σ)) ∧ output σ = out :=
  ⟨fun ⟨c', σ, hs, hh, ho⟩ => ⟨σ, ⟨c', vsa_iffS.1 hs, vsaK_halted.1 hh⟩, ho⟩,
   fun ⟨σ, ⟨c', hr, hh⟩, ho⟩ => ⟨c', σ, vsa_iffS.2 hr, vsaK_halted.2 hh, ho⟩⟩

/-! ## Section 2: held-out cases -/

theorem h1 : OCaml.Pilot.H1 := fun _ _ _ _ _ _ h h' => by
  cases (mm_halts_iff.1 h).unique (mm_halts_iff.1 h'); exact ⟨rfl, rfl⟩

theorem h2 : OCaml.Pilot.H2 := fun M _ _ =>
  ((reaches_pres M).iff (mmK_graph M)).trans (exists_congr fun _ => ((reachesN_pres M).iff (mmK_graph M)).symm)

theorem h3 : OCaml.Pilot.H3 := fun P hg => by
  have nb : ∀ o, HaltsK (bcK P) P.init o → ¬ ¬ ∃ e w, o = .halt e w := fun o h hb => hb (good_halt hg h)
  rw [bcDiv_iff, div_iff_not_halts _ nb]
  refine not_congr ⟨fun ⟨o, hb, h⟩ => ?_, fun ⟨out, e, h⟩ => ?_⟩
  · obtain ⟨e, w, rfl⟩ := Classical.not_not.1 hb; exact ⟨_, e, bcHalts_iff.2 ⟨w, h, rfl⟩⟩
  · obtain ⟨w, h, -⟩ := bcHalts_iff.1 h; exact ⟨_, fun hb => hb ⟨e, w, rfl⟩, h⟩

theorem h4 : OCaml.Pilot.H4 := fun c hns => by
  have nb : ∀ o, HaltsK vsaK c o → ¬ o = none := by
    rintro o ⟨d, hr, hd⟩ rfl
    rcases hns d (vsa_iffS.2 hr) with ⟨d', hs⟩ | ⟨e, σ, hh⟩
    · rw [vsaK_graph.iff.1 hs] at hd; cases hd
    · rw [vsaK_halted.1 hh] at hd; cases hd
  rw [vsaDiv_iff, div_iff_not_halts _ nb]
  refine not_congr ⟨fun ⟨o, hb, h⟩ => ?_, fun ⟨out, e, h⟩ => ?_⟩
  · rcases o with _ | ⟨e, σ⟩
    · exact (hb rfl).elim
    · exact ⟨_, e, vsaHalts_iff.2 ⟨σ, h, rfl⟩⟩
  · obtain ⟨σ, h, -⟩ := vsaHalts_iff.1 h; exact ⟨some (e, σ), nofun, h⟩

/-! ## Section 3: refactors (identical statements, new names) -/

section R1
open OCaml.Bytecode

theorem StepsN.det_k {P : Prog} {n : Nat} {a b b' : St}
    (h : StepsN P n a b) (h' : StepsN P n a b') : b = b' := by
  have := bc_iff.1 h; rw [bc_iff.1 h'] at this; cases this; rfl

theorem StepsN.snoc_k {P : Prog} {n : Nat} {a b c : St}
    (h : StepsN P n a b) (s : Step P b c) : StepsN P (n + 1) a c :=
  bc_iff.2 (by rw [iter_succ', bc_iff.1 h]; exact (bcK_graph P).iff.1 s)

theorem StepsN.stop_k {P : Prog} {n : Nat} {a b c : St} (h : StepsN P n a b)
    (hs : ∀ x, ¬ step P b = .next x) (h' : StepsN P (n + 1) a c) : False :=
  iter_stop (bc_iff.1 h) (fun x hx => by obtain ⟨h⟩ := (bcK_graph P).iff.2 hx; exact hs x h) c (bc_iff.1 h')

theorem halts_or_diverges_k (P : Prog) (hg : Good P) :
    (∃ out e, BcHalts P out e) ∨ BcDiverges P := by
  rw [bcDiv_iff]
  refine (halts_or_div (f := bcK P) P.init).imp (fun ⟨o, h⟩ => ?_) id
  obtain ⟨e, w, rfl⟩ := good_halt hg h
  exact ⟨_, e, bcHalts_iff.2 ⟨w, h, rfl⟩⟩

theorem BcHalts.not_diverges_k {P : Prog} {out : String} {e : Nat}
    (h : BcHalts P out e) : ¬ BcDiverges P := fun hd => by
  obtain ⟨w, h, -⟩ := bcHalts_iff.1 h; exact h.not_div (bcDiv_iff.1 hd)

theorem StepsN.prefix_k {P : Prog} {m : Nat} :
    ∀ {k : Nat} {a c : St}, StepsN P (m + k) a c → ∃ b, StepsN P m a b := fun h =>
  let ⟨b, hb⟩ := iter_prefix (bc_iff.1 h); ⟨b, bc_iff.2 hb⟩

theorem BcHalts.det_k {P : Prog} {out out' : String} {e e' : Nat}
    (h : BcHalts P out e) (h' : BcHalts P out' e') : out = out' ∧ e = e' := by
  obtain ⟨w, hk, rfl⟩ := bcHalts_iff.1 h; obtain ⟨w', hk', rfl⟩ := bcHalts_iff.1 h'
  cases hk.unique hk'; exact ⟨rfl, rfl⟩

end R1

section R2
open Vsa.Machine

theorem StepsN.append_k {n m : Nat} {a b c : Config} (h1 : StepsN n a b) (h2 : StepsN m b c) :
    StepsN (n + m) a c :=
  vsa_iffN.2 (by rw [iter_add, vsa_iffN.1 h1]; exact vsa_iffN.1 h2)

theorem Steps.trans'_k {a b c : Config} (h1 : Steps a b) (h2 : Steps b c) : Steps a c :=
  vsa_iffS.2 ((vsa_iffS.1 h1).trans (vsa_iffS.1 h2))

theorem Halts.of_steps_k {c c' : Config} {out : String} {e : Nat} (h : Steps c c')
    (h' : Halts c' out e) : Halts c out e :=
  let ⟨σ, hh, ho⟩ := vsaHalts_iff.1 h'; vsaHalts_iff.2 ⟨σ, hh.of_reach (vsa_iffS.1 h), ho⟩

theorem StepsN.prefix'_k : ∀ {m k : Nat} {a c : Config}, StepsN (m + k) a c → ∃ b, StepsN m a b :=
  fun h => let ⟨b, hb⟩ := iter_prefix (vsa_iffN.1 h); ⟨b, vsa_iffN.2 hb⟩

end R2

end RunKernel

namespace OCaml.Logic
open OCaml.Bytecode RunKernel

theorem reaches_stepsN_k {P : Prog} {a b : (bcModel P).State}
    (h : VsaIris.Reaches (bcModel P) a b) : ∃ n, Bytecode.StepsN P n a b := by
  obtain ⟨n, hn⟩ := ((reaches_pres _).iff (mmK_graph _)).1 h
  obtain ⟨c, hc, rfl⟩ := mapOut_ok ((iter_transport id gBc (bcModel_square P) n a).symm.trans hn)
  exact ⟨n, bc_iff.2 hc⟩

theorem halts_bcHalts_k {P : Prog} {e : Nat} {out : String}
    (h : VsaIris.Halts (bcModel P) P.init e out) : BcHalts P out e := by
  obtain ⟨n, hn⟩ := haltsK_iff.1 (mm_halts_iff.1 h)
  obtain ⟨o, ho, hg⟩ := mapOut_error ((iter_transport id gBc (bcModel_square P) n P.init).symm.trans hn)
  cases o <;> cases hg
  exact bcHalts_iff.2 ⟨_, haltsK_iff.2 ⟨n, ho⟩, rfl⟩

end OCaml.Logic
