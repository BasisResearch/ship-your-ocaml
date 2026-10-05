import OCaml.RefinementF1
import OCaml.Programs.WhileMin
import OCaml.Programs.WhileMinChecks
import OCaml.Programs.Validation

/-!
# `GoodF1` of a concrete program from one checked run

`runToF1` is `runTo` that also checks, at every visited state, that the PC
decodes to an `InF1` instruction. A deterministic run that halts visits
every reachable state, so one successful check gives `GoodF1`
(`GoodF1.of_runToF1`): the domain premise of the F1 headline for a concrete
program is a single `decide +kernel`.
-/

namespace OCaml

open OCaml.Bytecode

/-- A halting run that stays at F1 instructions, as a checkable function. -/
def runToF1 (P : Prog) : Nat → St → Option (Nat × World)
  | 0, _ => none
  | k + 1, s => match decodeAt P.code s.pc with
    | none => none
    | some i =>
      if InF1 P i ∧ stopOrdinary i s.accu = true then
        match stepI P s i with
        | .next s' => runToF1 P k s'
        | .halt e w => some (e, w)
        | _ => none
      else none

/-- Every state reachable from a checked state is at an F1 instruction and
steps normally or halts. -/
theorem runToF1_reach {P : Prog} :
    ∀ k s, (runToF1 P k s).isSome → ∀ n s', StepsN P n s s' →
      (∃ i, decodeAt P.code s'.pc = some i ∧ InF1 P i ∧ stopOrdinary i s'.accu = true) ∧
        step P s' ≠ .unsupported ∧ step P s' ≠ .wrong := by
  intro k
  induction k with
  | zero => intro s h; simp [runToF1] at h
  | succ k ih =>
    intro s h n s' hs
    simp only [runToF1] at h
    split at h
    · simp at h
    · rename_i i hd
      have hstep : step P s = stepI P s i := by simp only [step, hd]
      split at h
      · rename_i hi
        cases hs with
        | zero =>
          refine ⟨⟨i, hd, hi.1, hi.2⟩, ?_, ?_⟩ <;> rw [hstep] <;> split at h <;> simp_all
        | succ st rest =>
          obtain ⟨e⟩ := st
          rw [hstep] at e
          rw [e] at h
          exact ih _ h _ _ rest
      · simp at h

/-- **`GoodF1` from one checked halting run.** -/
theorem GoodF1.of_runToF1 {P : Prog} {k : Nat} (h : (runToF1 P k P.init).isSome) : GoodF1 P where
  good s hr := let ⟨n, hn⟩ := hr; (runToF1_reach k _ h n s hn).2
  inF1 s hr := let ⟨n, hn⟩ := hr
    let ⟨i, hd, hi, _⟩ := (runToF1_reach k _ h n s hn).1
    ⟨i, hd, hi⟩
  stopAccu s i hr hd := by
    obtain ⟨n, hn⟩ := hr
    obtain ⟨i', hd', _, ho⟩ := (runToF1_reach k _ h n s hn).1
    rw [hd] at hd'
    cases hd'
    exact ho

namespace Programs

set_option maxRecDepth 100000 in
theorem whileMin_runToF1 : (runToF1 whileMin 2200 whileMin.init).isSome := by
  decide +kernel

/-- **`while_min.byte` stays in F1** along its whole run. -/
theorem whileMin_goodF1 : GoodF1 whileMin := GoodF1.of_runToF1 whileMin_runToF1

/-- **The `whileMin` machine instance**, from the F1 arm tables: the machine
loaded with `while_min.byte` halts printing `55`, `2500`, `36` with exit 0.
The domain premises are proved (`whileMin_goodF1`, `whileMin_fits`,
`whileMin_gcSafe`); what remains is `Loaded` (a0-boot) and the tables. -/
theorem whileMin_halts_of_arms {L : Layout} {c : Vsa.Machine.Config}
    (A : ∀ P c, Loaded L P c → GoodF1 P → Fits Vm.Gc.g1Budget P → GcSafe P → ∃ R, F1Arms P c R)
    (hL : Loaded L whileMin c) : Vsa.Machine.Halts c "55\n2500\n36\n" 0 :=
  ((ocamlrun_refinementF1_of_arms A) whileMin c hL whileMin_goodF1 whileMin_fits whileMin_gcSafe).1
    _ _ |>.1 whileMin_bcSem

end Programs

end OCaml
