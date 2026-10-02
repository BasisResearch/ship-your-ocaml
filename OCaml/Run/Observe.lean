import OCaml.Run.Kernel

/-! Continuation observations after a finite successful prefix. These are run
kernel laws, independent of bytecode and GC. No induction on a run relation. -/
namespace OCaml.Run
variable {C O : Type} {f : C → Except O C} {a b : C} {n : Nat}

/-- A successful finite prefix neither creates nor loses a terminal outcome. -/
theorem halts_after_iter (pre : iter f n a = .ok b) (o : O) :
    HaltsK f a o ↔ HaltsK f b o := by
  rw [haltsK_iff, haltsK_iff]
  constructor
  · rintro ⟨m, hm⟩
    have lt := iter_ok_lt hm pre
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt lt)
    rw [iter_add, pre] at hm
    exact ⟨k, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨n + m, by rw [iter_add, pre]; exact hm⟩

/-- A finite successful prefix preserves divergence, without a Good premise. -/
theorem div_after_iter (pre : iter f n a = .ok b) : DivK f a ↔ DivK f b := by
  constructor
  · intro hd k
    obtain ⟨d, h⟩ := hd (n + k)
    rw [iter_add, pre] at h
    exact ⟨d, h⟩
  · intro hd k
    obtain ⟨d, h⟩ := hd k
    have full : iter f (n + k) a = .ok d := by rw [iter_add, pre]; exact h
    exact iter_prefix (m := k) (k := n) (by simpa [Nat.add_comm] using full)

end OCaml.Run
