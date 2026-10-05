import OCaml.Run.Machine

/-!
# The platform clock counter stays below `plat_insns_per_tick`

`stepOnce` either resets the tick counter to `0` (when `i + 1` reaches
`plat_insns_per_tick = 2`) or returns `i + 1 ≠ 2`. Hence `tick < 2` is an
invariant of every machine run. Arm proofs therefore never thread it: the
loop-head invariant recovers it from the run (`OCaml/Refinement.lean`).
-/

namespace Vsa.Machine
open LeanRV64DExecutable

private theorem bind_ok {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s s' : σ} {b : β} (h : EStateM.bind x f s = .ok b s') :
    ∃ a s1, x s = .ok a s1 ∧ f a s1 = .ok b s' := by
  simp only [EStateM.bind] at h
  split at h
  · exact ⟨_, _, by assumption, h⟩
  · cases h

/-- The common continuation after `try_step`: an HTIF exit or a counter update. -/
private theorem tail_tick {i u i' u' : Nat} {s σ' : MState}
    (h : (EStateM.bind (readReg Register.htif_done) fun d =>
        if d = true then
          EStateM.bind (readReg Register.htif_exit_code) fun x =>
            EStateM.pure (Sum.inl (some (BitVec.toNat x), u))
        else if (i + 1 == Int.toNat Functions.plat_insns_per_tick) = true then
          EStateM.bind (Functions.tick_clock ()) fun _ => EStateM.pure (Sum.inr (0, u))
        else EStateM.pure (Sum.inr (i + 1, u))) s = .ok (.inr (i', u')) σ') :
    i' = 0 ∨ (i' = i + 1 ∧ i + 1 ≠ 2) := by
  obtain ⟨d, s1, -, h⟩ := bind_ok h
  cases d
  · by_cases hn : (i + 1 == Int.toNat Functions.plat_insns_per_tick) = true
    · simp only [Bool.false_eq_true, ↓reduceIte, hn, ↓reduceIte] at h
      obtain ⟨_, _, -, h⟩ := bind_ok h
      simp only [EStateM.pure, EStateM.Result.ok.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
      exact Or.inl h.1.1.symm
    · simp only [Bool.false_eq_true, ↓reduceIte, hn] at h
      simp only [EStateM.pure, EStateM.Result.ok.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
      refine Or.inr ⟨h.1.1.symm, fun e => hn ?_⟩
      simp only [Functions.plat_insns_per_tick, e]; rfl
  · simp only [↓reduceIte] at h
    obtain ⟨_, _, -, h⟩ := bind_ok h
    simp only [EStateM.pure, EStateM.Result.ok.injEq, reduceCtorEq, false_and] at h

/-- The counter returned by one continuing loop iteration. -/
theorem stepOnce_tick {i u i' u' : Nat} {σ σ' : MState}
    (h : (stepOnce i u).run σ = .ok (.inr (i', u')) σ') : i' = 0 ∨ (i' = i + 1 ∧ i + 1 ≠ 2) := by
  unfold stepOnce at h
  simp only [bind, EStateM.run, pure] at h
  obtain ⟨d, s1, -, h⟩ := bind_ok h
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨stepped, s2, -, h⟩ := bind_ok h
    cases stepped
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact tail_tick h
    · simp only [↓reduceIte] at h
      obtain ⟨_, _, -, h⟩ := bind_ok h
      exact tail_tick h
  · simp only [↓reduceIte] at h
    obtain ⟨_, _, -, h⟩ := bind_ok h
    simp only [EStateM.pure, EStateM.Result.ok.injEq, reduceCtorEq, false_and] at h

/-- One machine step keeps the counter below two. -/
theorem Step.tick_lt {c c' : Config} (h : Step c c') (lt : c.tick < 2) : c'.tick < 2 := by
  cases h with
  | mk e =>
    simp only at lt ⊢
    rcases stepOnce_tick e with h | ⟨h, ne⟩ <;> omega

/-- Every exact run keeps the counter below two (`Run.iter_inv` on `vsaK`). -/
theorem StepsN.tick_lt {n : Nat} {c c' : Config} (h : StepsN n c c') (lt : c.tick < 2) :
    c'.tick < 2 :=
  OCaml.Run.iter_inv (fun c : Config => c.tick < 2)
    (fun e lt => Step.tick_lt (OCaml.Run.vsaK_graph.iff.2 e) lt) (OCaml.Run.vsa_stepsN_iff.1 h) lt

end Vsa.Machine
