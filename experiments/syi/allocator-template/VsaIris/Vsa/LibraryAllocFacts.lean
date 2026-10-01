import VsaIris.Vsa.SymRun

namespace VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def stackBase (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) : Mem :=
  (List.range len).foldl (fun m k => m.insert (lo + k) (f (lo + k))) m

theorem stackBase_get (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) (a : Nat) :
    (stackBase m lo len f)[a]? = if lo ≤ a ∧ a < lo + len then some (f a) else m[a]? := by
  unfold stackBase
  induction len generalizing a with
  | zero => simp only [List.range_zero, List.foldl_nil]; rw [ite_eq_right (by omega)]
  | succ len ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.ExtHashMap.getElem?_insert]
    by_cases h : lo + len = a
    · subst h; simp
    · rw [ite_eq_right (by simpa using h), ih]
      by_cases h2 : lo ≤ a ∧ a < lo + len
      · rw [ite_eq_left h2, ite_eq_left ⟨h2.1, by omega⟩]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem or_one_even (x : BitVec 64) (h : x.toNat % 2 = 0) :
    x ||| sign_extend (m := 64) (0x001#12) = x + 1#64 := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 by decide]
  refine (BitVec.add_eq_or_of_and_eq_zero x 1#64 ?_).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

theorem and_high_toNat (a : BitVec 64) (k : Nat) (hk : k < 64) :
    (a &&& (BitVec.allOnes 64 <<< k)).toNat = a.toNat / 2 ^ k * 2 ^ k := by
  have hshift : (a &&& (BitVec.allOnes 64 <<< k)) = (a >>> k) <<< k := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < k
    · simp [hi]
    · by_cases hlt : i < 64
      · have h3 : k + (i - k) = i := by omega
        have h2 : i - k < 64 := by omega
        simp [hi, hlt, h2, h3]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp [hi, hlt, hge]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc a.toNat / 2 ^ k * 2 ^ k ≤ a.toNat := Nat.div_mul_le_self _ _
    _ < 2 ^ 64 := a.isLt

end VsaIris.MallocFast
