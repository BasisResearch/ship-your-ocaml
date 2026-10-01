import OCaml.Refinement
import OCaml.Bytecode.Load
import OCaml.Vm.Sim.PrimitiveBindingData

namespace OCaml.Vm.Sim.PrimitiveBinding
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- The current loaded relation forgets the primitive-name table. -/
theorem loaded_prims {L : OCaml.Layout} {P : Prog} {c : Config}
    (h : Loaded L P c) (prims : Array String) : Loaded L {P with prims := prims} c := by
  obtain ⟨pl, cp, high, h⟩ := h
  exact ⟨pl, cp, high, h.atEntry, h.argCode, h.argSize, h.codeBase, h.code,
    h.globals, h.stackHigh, h.externSp, h.trapsp, h.heap, h.world, h.platform⟩

private theorem good_of_halts {P : Prog} {out : String} {e : Nat}
    (h : BcHalts P out e) : Good P := by
  obtain ⟨w, hh, _⟩ := bcHalts_iff.1 h
  intro s hs
  obtain ⟨k, hk⟩ := hs
  have unique (r : Res) (hr : bcK P s = .error r) : r = .halt e w :=
    (show Run.HaltsK (bcK P) P.init r from ⟨s, ⟨k, stepsN_iff.1 hk⟩, hr⟩).unique hh
  constructor
  · intro bad
    have impossible := unique .unsupported (by simp only [bcK, bad])
    cases impossible
  · intro bad
    have impossible := unique .wrong (by simp only [bcK, bad])
    cases impossible

private theorem halts_of_check {P : Prog} {fuel e : Nat}
    (h : (runTo P fuel P.init).map (fun r => (r.1, bytesToString r.2.console)) = some (e, "")) :
    BcHalts P "" e := by
  match hr : runTo P fuel P.init, h with
  | some (e', w), h =>
    simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hw⟩ := h
    exact hw ▸ bcHalts_of_runTo hr

private theorem word_halts : BcHalts wordProbe "" 64 :=
  halts_of_check (fuel := 3) (by decide +kernel)
private theorem swapped_halts : BcHalts swappedProbe "" 63 :=
  halts_of_check (fuel := 3) (by decide +kernel)

private def probeBudget : Budget := ⟨0, wordProbe.heap0.words⟩

private theorem fits_of_checked {P : Prog}
    (stop : (match Run.iter (bcK P) 3 P.init with | .ok _ => false | .error _ => true) = true)
    (check : ∀ k : Fin 3, (match Run.iter (bcK P) k P.init with
      | .ok s => decide (s.stack.length ≤ probeBudget.stackWords ∧ s.heap.words ≤ probeBudget.heapWords)
      | .error _ => true) = true) : Fits probeBudget P := by
  have done : ∃ o, Run.iter (bcK P) 3 P.init = .error o := by
    cases hx : Run.iter (bcK P) 3 P.init with
    | ok s =>
      simp only [hx] at stop
      cases stop
    | error o => exact ⟨o, rfl⟩
  obtain ⟨o, ho⟩ := done
  intro s hs
  obtain ⟨k, hk⟩ := hs
  have hi := stepsN_iff.1 hk
  have hb := Run.iter_ok_lt ho hi
  have hc := check ⟨k, hb⟩
  simp only [hi] at hc
  exact of_decide_eq_true hc

private theorem word_fits : Fits probeBudget wordProbe :=
  fits_of_checked (by decide +kernel) (by decide +kernel)
private theorem swapped_fits : Fits probeBudget swappedProbe :=
  fits_of_checked (by decide +kernel) (by decide +kernel)

/-- Identical code/heap/world with different primitive names produce different
observable exits. Determinism rules out the unchanged headline for the current
primitive-unbound Loaded contract whenever this tiny program is loaded. -/
theorem primitive_binding_obstruction {L : OCaml.Layout} {B : Budget} {c : Config}
    (capacity : wordProbe.heap0.words ≤ B.heapWords)
    (loaded : Loaded L wordProbe c) : ¬ OcamlrunRefinement L B := by
  intro H
  have fits {P : Prog} (h : Fits probeBudget P) : Fits B P := by
    intro s hs
    obtain ⟨stack, heap⟩ := h s hs
    exact ⟨Nat.le_trans stack (Nat.zero_le _), Nat.le_trans heap capacity⟩
  have other : Loaded L swappedProbe c := loaded_prims loaded swappedProbe.prims
  have first := (H wordProbe c loaded (good_of_halts word_halts) (fits word_fits)).1 "" 64
  have second := (H swappedProbe c other (good_of_halts swapped_halts) (fits swapped_fits)).1 "" 63
  have impossible := (first.1 word_halts).deterministic (second.1 swapped_halts)
  omega

end OCaml.Vm.Sim.PrimitiveBinding
