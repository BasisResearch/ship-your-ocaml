import OCaml.Bytecode.Semantics

/-!
# Symbolic stepping and the loop rule (Layer B′ bytecode specifications, C4)

Adopted in abstraction-discovery round 1 (`abstractions/ROUND-1.md`, bake-off
entrant `Membrane`). A straight-line bytecode segment is specified from ANY
state by reducing the real `step` on a template state. Only the pc (and the
values the segment reads) are concrete; the stack tail, env, extra, trap,
heap and world are free variables. The kernel iterate
`Run.iter (bcK P) k template = .ok template'` then closes by `rfl`. There is no
per-instruction lemma and no second semantics.

Reduction stops at a branch on a symbolic word; `step_br_fall` and
`step_br_taken` resolve it with one Boolean fact. It also stops at tagged
arithmetic on symbolic integers; the `*_ofNat` normalisation lemmas close
that by `omega`, never `bv_decide`. A loop is `loop_rule`: a section
invariant, a rank, one symbolic body run and one symbolic exit run.

Model: `OCaml/Programs/CountLoop.lean`, a counting loop for ANY bound in
48 lines. The pilot's per-value enumeration grows with the bound.
-/

namespace OCaml.Bytecode

theorem sym_step {P : Prog} {n : Nat} {s s' : St} (h : step P s = .next s') :
    Run.iter (bcK P) (n + 1) s = Run.iter (bcK P) n s' := by
  simp [Run.iter, bcK, h]; rfl

theorem sym_seq {P : Prog} {a b : Nat} {s s' s'' : St}
    (h : Run.iter (bcK P) a s = .ok s') (h' : Run.iter (bcK P) b s' = .ok s'') :
    Run.iter (bcK P) (a + b) s = .ok s'' := by
  rw [Run.iter_add, h]; exact h'

theorem sym_sound {P : Prog} {n : Nat} {s s' : St} (h : Run.iter (bcK P) n s = .ok s') : StepsN P n s s' :=
  stepsN_iff.2 h

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
    (body : ∀ s, Inv s → ¬ exit s → ∃ k s', Run.iter (bcK P) k s = .ok s' ∧ Inv s' ∧ μ s' < μ s)
    (done : ∀ s, Inv s → exit s → ∃ k s', Run.iter (bcK P) k s = .ok s' ∧ Post s') :
    ∀ s, Inv s → ∃ k s', Run.iter (bcK P) k s = .ok s' ∧ Post s' := by
  intro s
  generalize h : μ s = m
  induction m using Nat.strongRecOn generalizing s with
  | ind m ih =>
    intro hs
    by_cases he : exit s
    · exact done s hs he
    · obtain ⟨k, s', hr, hs', hlt⟩ := body s hs he
      obtain ⟨k', s'', hr', hp⟩ := ih (μ s') (h ▸ hlt) s' rfl hs'
      exact ⟨k + k', s'', sym_seq hr hr', hp⟩

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

end OCaml.Bytecode
