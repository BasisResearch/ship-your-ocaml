import OCaml.Vm.Sim.ClosurePrefixInput
import OCaml.Vm.Sim.ClosureCopy

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The temporary accumulator push establishes the complete native capture snapshot. -/
theorem closure_push_snapshot {before after : Config} {sp count i : Nat} {accu w : BitVec 64}
    (room : 0 < count → 8 ≤ sp)
    (memory : after.σ.mem = writeLog before.σ.mem (closurePushLog sp count accu))
    (selected : (closureWords before sp count accu)[i]? = some w) :
    word after (closureSource sp count + 8 * i) = w := by
  by_cases positive : 0 < count
  · simp only [closureWords, positive, ite_true] at selected
    have pushed : after.σ.mem = writeLog before.σ.mem [(sp - 8, 8, accu)] := by
      simpa only [closurePushLog, positive, ite_true] using memory
    have stackRoom := room positive
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst w
      simp only [closureSource, positive, ite_true, Nat.mul_zero, Nat.add_zero]
      exact word_after_writeLog_at pushed 0 (sp - 8) accu rfl trivial
    | succ i =>
      simp only [List.getElem?_cons_succ] at selected
      have bound : i < count - 1 := by
        have b := (List.getElem?_eq_some_iff.mp selected).1
        simpa only [stackWords, List.length_map, List.length_range] using b
      have address : closureSource sp count + 8 * (i + 1) = sp + 8 * i := by
        simp only [closureSource, positive, ite_true]
        omega
      have outside : OutLRange [(sp - 8, 8, accu)] (sp + 8 * i) 8 :=
        ⟨Or.inr (by dsimp only; omega), trivial⟩
      rw [address, word, pushed, bytesT_writeLog_out _ outside]
      simpa only [word, stackWords, List.getElem?_map, List.getElem?_range, bound, ite_true,
        Option.map_some, Option.some.injEq] using selected
  · simp only [closureWords, positive, ite_false, List.getElem?_nil] at selected
    cases selected

/-- Nursery/header setup disjoint from captures preserves the established snapshot. -/
theorem closure_setup_snapshot {before after : Config} {sp count i : Nat} {accu w : BitVec 64}
    {tail : List WEntry} (room : 0 < count → 8 ≤ sp)
    (memory : after.σ.mem = writeLog before.σ.mem (closurePushLog sp count accu ++ tail))
    (outside : OutLRange tail (closureSource sp count) (8 * count))
    (selected : (closureWords before sp count accu)[i]? = some w) :
    word after (closureSource sp count + 8 * i) = w := by
  have bound : i < count := by
    have b := (List.getElem?_eq_some_iff.mp selected).1
    simpa only [closure_words_length] using b
  have slot := outLRange_subrange outside (show closureSource sp count ≤ closureSource sp count + 8 * i by omega)
    (show closureSource sp count + 8 * i + 8 ≤ closureSource sp count + 8 * count by omega)
  let pushed : Config := {before with σ := {before.σ with mem := writeLog before.σ.mem (closurePushLog sp count accu)}}
  have snapshot := closure_push_snapshot (after := pushed) room rfl selected
  rw [word, memory, writeLog_append, bytesT_writeLog_out _ slot]
  exact snapshot

end OCaml.Vm.Sim
