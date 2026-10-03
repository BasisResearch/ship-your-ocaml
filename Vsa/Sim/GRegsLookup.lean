import Vsa.Sim.BlockMem

namespace Vsa.Sim

/-- Erasing another register preserves the first matching binding. This
lets generated transfer certificates normalize symbolic register tails. -/
theorem lookupG_eraseG_ne {n m : Nat} (different : n ≠ m) (L : GRegs) :
    lookupG n (eraseG m L) = lookupG n L := by
  induction L with
  | nil => rfl
  | cons cell rest ih =>
      rcases cell with ⟨k,v⟩
      by_cases erase : k = m
      · subst k
        simp [eraseG, lookupG, Ne.symm different, ih]
      · simp only [eraseG, if_neg erase, lookupG]
        split <;> simp_all

/-- The source-value view inherits lookup preservation, including x0. -/
theorem srcVal_eraseG_ne {n m : Nat} (different : n ≠ m) (L : GRegs) :
    srcVal n (eraseG m L) = srcVal n L := by
  cases n <;> simp only [srcVal, lookupG_eraseG_ne different]

end Vsa.Sim
