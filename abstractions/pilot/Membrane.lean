import Pilot

/-!
# Membrane: symbolic stepping of the real `step` + one ranked loop rule

Bake-off entrant (abstraction-discovery round 1, cluster C4).

* **Symbolic stepping.** A straight-line segment is ONE equation
  `runN P k ⟨pc, a, stk, e, x, t, h, w⟩ = some ⟨pc', …⟩` over a template
  state whose accumulator, stack tail, env, heap and world are free
  variables, closed by `rfl`: it is kernel/elaborator reduction of the real
  `OCaml.Bytecode.step` (no per-instruction lemma, no second semantics).
  Reduction stops only at data-dependent control (`brOp`'s `if` on a symbolic
  word); there `step_br_{fall,taken}` resolve the branch from one Boolean fact.
* **Loop rule** (`loop_rule`): a loop-head section `Inv` with a rank `μ`, a
  body obligation (one symbolic body run that re-enters `Inv` with smaller
  `μ`) and an exit obligation give the post from every `Inv` state
  (well-founded induction on `μ`, proved once).
* **Word normalisation** (`longVal_toNat`, `offsetInt_ofNat`, `sle_ofNat`):
  the tagged-word arithmetic on `BitVec.ofNat 63 n`, `n < 2^62`, as `Nat`
  facts closed by `omega` (no `bv_decide`).

Built with `import Pilot` after compiling `abstractions/pilot/Pilot.lean` to
`.lake/build/lib/lean/Pilot.olean` (`lake env lean -o …`).
-/

namespace OCaml.Pilot.Membrane

open OCaml.Bytecode

/-! ## 1. The abstraction (SETUP) -/

/-- `k` steps of the real `step`, `none` if a step does not continue. -/
def runN (P : Prog) : Nat → St → Option St
  | 0, s => some s
  | n + 1, s => match step P s with
    | .next s' => runN P n s'
    | _ => none

theorem runN_step {P : Prog} {n : Nat} {s s' : St} (h : step P s = .next s') :
    runN P (n + 1) s = runN P n s' := by
  simp [runN, h]

/-- Composition law. -/
theorem runN_add (P : Prog) (a b : Nat) (s : St) :
    runN P (a + b) s = (runN P a s).bind (runN P b) := by
  induction a generalizing s with
  | zero => simp [runN]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [runN]
    split <;> simp [ih]

theorem runN_seq {P : Prog} {a b : Nat} {s s' s'' : St}
    (h : runN P a s = some s') (h' : runN P b s' = some s'') : runN P (a + b) s = some s'' := by
  rw [runN_add, h]; exact h'

/-- Soundness to the `BcSem` relation. -/
theorem runN_sound {P : Prog} : ∀ {n : Nat} {s s' : St}, runN P n s = some s' → StepsN P n s s'
  | 0, s, s', h => by cases h; exact .zero s
  | n + 1, s, s', h => by
    simp only [runN] at h
    split at h
    · next s1 hs => exact .succ (.mk hs) (runN_sound h)
    · cases h

/-- A conditional branch not taken. -/
theorem step_br_fall {P : Prog} {s : St} {n o : Int} {f : BitVec 64 → BitVec 64 → Bool} {a : BitVec 63}
    (hd : step P s = brOp s n o f) (ha : s.accu = .int a) (hf : f (BitVec.ofInt 64 n) (longVal a) = false) :
    step P s = .next (s.adv 3) := by
  rw [hd]; unfold brOp; rw [ha]; simp [hf]

/-- A conditional branch taken. -/
theorem step_br_taken {P : Prog} {s : St} {n o : Int} {f : BitVec 64 → BitVec 64 → Bool} {a : BitVec 63}
    {t : Nat} (hd : step P s = brOp s n o f) (ha : s.accu = .int a)
    (hf : f (BitVec.ofInt 64 n) (longVal a) = true) (ht : target s.pc 1 o = some t) :
    step P s = .next { s with pc := t } := by
  rw [hd]; unfold brOp; rw [ha]; simp [hf, ht, opt]

/-- **The loop rule**: ranked section transport. -/
theorem loop_rule {P : Prog} (Inv Post : St → Prop) (μ : St → Nat) (exit : St → Prop)
    (body : ∀ s, Inv s → ¬ exit s → ∃ k s', runN P k s = some s' ∧ Inv s' ∧ μ s' < μ s)
    (done : ∀ s, Inv s → exit s → ∃ k s', runN P k s = some s' ∧ Post s') :
    ∀ s, Inv s → ∃ k s', runN P k s = some s' ∧ Post s' := by
  intro s
  generalize h : μ s = m
  induction m using Nat.strongRecOn generalizing s with
  | ind m ih =>
    intro hs
    by_cases he : exit s
    · exact done s hs he
    · obtain ⟨k, s', hr, hs', hlt⟩ := body s hs he
      obtain ⟨k', s'', hr', hp⟩ := ih (μ s') (h ▸ hlt) s' rfl hs'
      exact ⟨k + k', s'', runN_seq hr hr', hp⟩

/-! Word normalisation for small non-negative integers. -/

theorem ofNat_msb (n : Nat) (h : n < 2^62) : (BitVec.ofNat 63 n).msb = false := by
  simp [BitVec.msb_eq_decide]; omega

theorem longVal_toNat (n : Nat) (h : n < 2^62) : (longVal (BitVec.ofNat 63 n)).toNat = n := by
  unfold longVal
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (ofNat_msb n h)]
  simp; omega

theorem tag64_toNat (n : Nat) (h : n < 2^62) : (tag64 (BitVec.ofNat 63 n)).toNat = 2 * n + 1 := by
  have e : ∀ y : BitVec 64, y <<< (1:Nat) ||| (1 : BitVec 64) = y <<< (1:Nat) + 1 := by
    intro y
    have := @BitVec.shiftLeft_add_eq_shiftLeft_or 64 1#64 y
    rw [BitVec.shiftLeft_eq'] at this
    exact this.symm
  unfold tag64
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (ofNat_msb n h), e]
  simp [Nat.shiftLeft_eq]; omega

theorem untag_ofNat (m : Nat) (h : m < 2^63) (hodd : m % 2 = 1) :
    untag (BitVec.ofNat 64 m) = BitVec.ofNat 63 (m / 2) := by
  unfold untag
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.ofNat 64 m).msb = false := by simp [BitVec.msb_eq_decide]; omega
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sshiftRight_of_msb_false hm]
  simp [Nat.shiftRight_eq_div_pow]; omega

/-- `OFFSETINT 1` on a small integer. -/
theorem offsetInt_ofNat (n : Nat) (h : n + 1 < 2^62) :
    untag (tag64 (BitVec.ofNat 63 n) + (BitVec.ofInt 64 1 <<< 1)) = BitVec.ofNat 63 (n+1) := by
  have : tag64 (BitVec.ofNat 63 n) + (BitVec.ofInt 64 1 <<< 1) = BitVec.ofNat 64 (2 * n + 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tag64_toNat n (by omega)]
    simp
  rw [this, untag_ofNat _ (by omega) (by omega)]
  congr 1; omega

/-- `BLEINT m` on a small integer. -/
theorem sle_ofNat (n m : Nat) (h : n < 2^62) (hm : m < 2^62) :
    (BitVec.ofInt 64 m).sle (longVal (BitVec.ofNat 63 n)) = decide (m ≤ n) := by
  have hl := longVal_toNat n h
  rw [BitVec.sle]
  simp [BitVec.toInt_eq_toNat_cond, hl]
  split <;> split <;> omega

/-- The integer on the stack top (the loop counter's projection). -/
def headNat (s : St) : Nat :=
  match s.stack with
  | .int v :: _ => v.toNat
  | _ => 0

/-! ## 2. Held-out cases -/

theorem h8 : OCaml.Pilot.H8 := by
  intro s hpc
  obtain ⟨pc, a, stk, e, x, t, h, w⟩ := s
  cases hpc
  have hr : runN segP 4 ⟨0, a, stk, e, x, t, h, w⟩ =
      some ⟨5, .int (untag (tag64 2 + tag64 (BitVec.ofInt 63 40) - 1)), stk, e, x, t, h, w⟩ := rfl
  have hv : untag (tag64 2 + tag64 (BitVec.ofInt 63 40) - 1) = 42 := by decide
  rw [hv] at hr
  exact ⟨_, runN_sound hr, rfl, rfl, rfl⟩

/-- The counting loop of `H9` with bound `N` (`BLEINT N`). -/
def loopN (N : Nat) : Prog :=
  ⟨enc [(.ACC0, []), (.BLEINT, [(N : Int), 8]), (.ACC0, []), (.OFFSETINT, [1]), (.ASSIGN, [0]),
        (.BRANCH, [-10]), (.ACC0, []), (.STOP, [])],
   #[], ⟨[]⟩, .atom 0, [], .atom 0, []⟩

/-- A code operand read back (`Code.arg` of `BitVec.ofInt 32 N`). -/
theorem arg_natCast (N : Nat) (hN : N < 2^31) : (BitVec.ofInt 32 (N : Int)).toInt = N := by
  rw [BitVec.ofInt_natCast, BitVec.toInt_eq_toNat_cond]
  simp; split <;> omega

/-- The `BLEINT N` test on counter `i`, normalised. -/
theorem bleint_loop (N i : Nat) (hN : N < 2^31) (hi : i < 2^62) :
    (BitVec.ofInt 64 (BitVec.ofInt 32 (N : Int)).toInt).sle (longVal (BitVec.ofNat 63 i)) = decide (N ≤ i) := by
  rw [arg_natCast N hN, sle_ofNat i N hi (by omega)]

/-- The loop body: one symbolic run `pc 0 → pc 0`, `i ↦ i + 1`. -/
theorem loopN_body (N : Nat) (hN : N < 2^31) (i : Nat) (hi : i < N) (a e : Val) (x t : Nat) (h : Heap)
    (w : World) (rest : List Val) :
    runN (loopN N) 6 ⟨0, a, .int (BitVec.ofNat 63 i) :: rest, e, x, t, h, w⟩ =
      some ⟨0, .unit, .int (BitVec.ofNat 63 (i + 1)) :: rest, e, x, t, h, w⟩ := by
  have hb := bleint_loop N i hN (by omega)
  rw [runN_step rfl, runN_step (step_br_fall (n := (BitVec.ofInt 32 (N : Int)).toInt) (o := 8) (f := fun a b => a.sle b)
    (a := BitVec.ofNat 63 i) rfl rfl (by rw [hb]; simp; omega)), ← offsetInt_ofNat i (by omega)]
  rfl

/-- The loop exit: `i = N` branches to `11`, `ACC0`, stops at `12`. -/
theorem loopN_exit (N : Nat) (hN : N < 2^31) (a e : Val) (x t : Nat) (h : Heap) (w : World) (rest : List Val) :
    runN (loopN N) 3 ⟨0, a, .int (BitVec.ofNat 63 N) :: rest, e, x, t, h, w⟩ =
      some ⟨12, .int (BitVec.ofNat 63 N), .int (BitVec.ofNat 63 N) :: rest, e, x, t, h, w⟩ := by
  have hb := bleint_loop N N hN (by omega)
  rw [runN_step rfl, runN_step (step_br_taken (n := (BitVec.ofInt 32 (N : Int)).toInt) (o := 8) (f := fun a b => a.sle b)
    (a := BitVec.ofNat 63 N) (t := 11) rfl rfl (by rw [hb]; simp) rfl)]
  rfl

/-- The counting loop for any bound `N < 2^31`: `loop_rule` on the section
"`pc = 0`, counter `i ≤ N` on the stack top", rank `N - i`. -/
theorem loopN_reaches (N : Nat) (hN : N < 2^31) :
    ∀ (n : Nat) (rest : List Val) (s : St), n ≤ N → s.pc = 0 → s.stack = .int (BitVec.ofNat 63 n) :: rest →
      ∃ k s', StepsN (loopN N) k s s' ∧ s'.pc = 12 ∧ s'.accu = .int (BitVec.ofNat 63 N) := by
  intro n rest s hn hpc hstk
  have := loop_rule (P := loopN N)
    (fun s => s.pc = 0 ∧ ∃ i, i ≤ N ∧ s.stack = .int (BitVec.ofNat 63 i) :: rest)
    (fun s => s.pc = 12 ∧ s.accu = .int (BitVec.ofNat 63 N)) (fun s => N - headNat s) (fun s => headNat s = N)
    (by
      rintro ⟨pc, a, stk, e, x, t, h, w⟩ ⟨hpc, i, hi, hs⟩ hne
      cases hpc; cases hs
      simp only [headNat, BitVec.toNat_ofNat] at hne
      refine ⟨6, _, loopN_body N hN i (by omega) a e x t h w rest, ⟨rfl, i + 1, by omega, rfl⟩, ?_⟩
      simp only [headNat, BitVec.toNat_ofNat]; omega)
    (by
      rintro ⟨pc, a, stk, e, x, t, h, w⟩ ⟨hpc, i, hi, hs⟩ hex
      cases hpc; cases hs
      simp only [headNat, BitVec.toNat_ofNat] at hex
      obtain rfl : i = N := by omega
      exact ⟨3, _, loopN_exit i hN a e x t h w rest, rfl, rfl⟩)
    s ⟨hpc, n, hn, hstk⟩
  obtain ⟨k, s', hr, hp⟩ := this
  exact ⟨k, s', runN_sound hr, hp⟩

theorem h9 : OCaml.Pilot.H9 := loopN_reaches 10 (by decide)

/-! ## Scaling probe (not part of the decision): H9 with bound 1000 -/

/-- `loopP` with `BLEINT 1000`. -/
def loopP1000 : Prog :=
  ⟨enc [(.ACC0, []), (.BLEINT, [1000, 8]), (.ACC0, []), (.OFFSETINT, [1]), (.ASSIGN, [0]),
        (.BRANCH, [-10]), (.ACC0, []), (.STOP, [])],
   #[], ⟨[]⟩, .atom 0, [], .atom 0, []⟩

def H9_1000 : Prop :=
  ∀ (n : Nat) (rest : List Val) (s : St), n ≤ 1000 → s.pc = 0 → s.stack = .int (BitVec.ofNat 63 n) :: rest →
    ∃ k s', StepsN loopP1000 k s s' ∧ s'.pc = 12 ∧ s'.accu = .int 1000

theorem h9_1000 : H9_1000 := loopN_reaches 1000 (by decide)


end OCaml.Pilot.Membrane
