import OCaml.Bytecode.Data

/-! Input facts for the native integer formatter, separated from executable semantics. -/
namespace OCaml.Bytecode

/-- The input facts established before integer rendering begins. Width and
precision replication never needs evaluation to recover these guards. -/
structure IntegerFormatConditions (fmt : List UInt8) : Prop where
  percent : (fmt.map fun b => Char.ofNat b.toNat).head? = some '%'
  long : 2 ≤ fmt.length
  fits : fmt.length + 2 < 32
  conversion : ∀ conv, (fmt.map fun b => Char.ofNat b.toNat).getLast? = some conv →
    conv ∈ ['d', 'i', 'u', 'x', 'X', 'o']

/-- Successful semantic formatting supplies the native parser's length and
conversion domain without inspecting the potentially large rendered result. -/
theorem formatInteger_conditions {fmt : List UInt8} {n : BitVec 63} {bytes : List UInt8}
    (success : formatInteger fmt n = some bytes) : IntegerFormatConditions fmt := by
  unfold formatInteger at success
  change (if ((fmt.map fun b => Char.ofNat b.toNat).head? != some '%' ||
      decide ((fmt.map fun b => Char.ofNat b.toNat).length < 2) ||
      decide ((fmt.map fun b => Char.ofNat b.toNat).length + 2 ≥ 32)) = true
    then none else _) = some bytes at success
  split at success
  · cases success
  · rename_i guard
    have guards : (fmt.map fun b => Char.ofNat b.toNat).head? = some '%' ∧
        2 ≤ fmt.length ∧ fmt.length + 2 < 32 := by
      simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, List.length_map,
        not_or, Nat.not_lt, Nat.not_le] at guard
      exact ⟨Classical.byContradiction guard.1.1, guard.1.2, guard.2⟩
    refine ⟨guards.1, guards.2.1, guards.2.2, ?_⟩
    intro conv last
    rw [last] at success
    change (if (!['d', 'i', 'u', 'x', 'X', 'o'].contains conv) = true then none else _) =
      some bytes at success
    split at success
    · cases success
    · rename_i supported
      have yes : ['d', 'i', 'u', 'x', 'X', 'o'].contains conv = true := by
        cases h : ['d', 'i', 'u', 'x', 'X', 'o'].contains conv
        · rw [h] at supported; exact False.elim (supported rfl)
        · rfl
      exact List.mem_of_elem_eq_true yes

end OCaml.Bytecode
