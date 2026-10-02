import Vsa.Sim.StrcmpSpecCond

/-! Equality observations for primitive-name lookup, derived from the landed
strcmp sign specification. No individual string comparisons are replayed. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Sim Vsa.MemRepr

structure FirstDifference (a b : List Char) (n : Nat) : Prop where
  bound : firstDiff a b n ≤ n
  agree : ∀ i, i < firstDiff a b n → byteVal a i = byteVal b i
  mismatch : firstDiff a b n < n → byteVal a (firstDiff a b n) ≠ byteVal b (firstDiff a b n)

theorem first_difference (a b : List Char) (n : Nat) : FirstDifference a b n := by
  induction n with
  | zero => exact ⟨Nat.le_refl _, by intro i h; change i < 0 at h; omega, by intro h; change 0 < 0 at h; omega⟩
  | succ n ih =>
    by_cases hlt : firstDiff a b n < n
    · have index : firstDiff a b (n + 1) = firstDiff a b n := by simp only [firstDiff, if_pos hlt]
      refine ⟨by rw [index]; omega, ?_, ?_⟩
      · rw [index]; exact ih.agree
      · rw [index]; intro _; exact ih.mismatch hlt
    · have index : firstDiff a b n = n := by have := ih.bound; omega
      by_cases same : byteVal a n = byteVal b n
      · have next : firstDiff a b (n + 1) = n + 1 := by simp [firstDiff, index, same]
        refine ⟨by rw [next]; omega, ?_, ?_⟩
        · rw [next]
          intro i hi
          by_cases hin : i < n
          · exact ih.agree i (by rw [index]; exact hin)
          · have : i = n := by omega
            simpa only [this] using same
        · rw [next]; intro h; omega
      · have next : firstDiff a b (n + 1) = n := by simp [firstDiff, index, same]
        refine ⟨by rw [next]; omega, ?_, ?_⟩
        · rw [next]; intro i hi; exact ih.agree i (by rw [index]; exact hi)
        · rw [next]; intro _; exact same

theorem isign_zero_iff (a b : Nat) : isign a b = 0 ↔ a = b := by
  by_cases lt : a < b
  · have ne : a ≠ b := Nat.ne_of_lt lt
    simp [isign, lt, ne]
  · by_cases eq : a = b <;> simp [isign, lt, eq]

theorem strcmpSign_zero_iff (x : BitVec 64) : strcmpSign x = 0 ↔ x = 0 := by
  unfold strcmpSign
  split <;> simp_all
  split <;> simp_all

theorem spec_zero_streams {a b : List Char} (h : strcmpSpecSign a b = 0) :
    ∀ i, byteVal a i = byteVal b i := by
  have d := first_difference a b (max a.length b.length + 1)
  have same := (isign_zero_iff _ _).mp h
  have index : firstDiff a b (max a.length b.length + 1) = max a.length b.length + 1 := by
    have bound := d.bound
    have no : ¬ firstDiff a b (max a.length b.length + 1) < max a.length b.length + 1 :=
      fun lt => d.mismatch lt same
    omega
  intro i
  by_cases hi : i < max a.length b.length + 1
  · exact d.agree i (by rw [index]; exact hi)
  · have ha : a[i]? = none := List.getElem?_eq_none (by omega)
    have hb : b[i]? = none := List.getElem?_eq_none (by omega)
    simp only [byteVal, ha, hb]

theorem cstr_eq_of_streams {ma mb : Mem} {pa pb : Nat} {a b : List Char}
    (ha : CStr ma pa a) (hb : CStr mb pb b)
    (same : ∀ i, byteVal a i = byteVal b i) : a = b := by
  have lengths : a.length = b.length := by
    by_cases le : a.length ≤ b.length
    · apply cstr_byteVal_zero mb pb b hb a.length le
      rw [← same]; simp [byteVal]
    · have le' : b.length ≤ a.length := by omega
      exact (cstr_byteVal_zero ma pa a ha b.length le' (by rw [same]; simp [byteVal])).symm
  apply List.ext_getElem lengths
  intro i hia hib
  apply Char.toNat_inj.mp
  simpa [byteVal, hia, hib] using same i

theorem strcmpSpecSign_zero_iff {ma mb : Mem} {pa pb : Nat} {a b : List Char}
    (ha : CStr ma pa a) (hb : CStr mb pb b) : strcmpSpecSign a b = 0 ↔ a = b := by
  constructor
  · intro h; exact cstr_eq_of_streams ha hb (spec_zero_streams h)
  · rintro rfl
    simp [strcmpSpecSign, isign]

end OCaml.Vm.Boot.Startup
