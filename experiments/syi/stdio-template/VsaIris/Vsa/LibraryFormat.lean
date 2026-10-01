import VsaIris.Vsa.LibraryByteFacts
namespace Vsa.While
def natDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [Nat.digitChar n]
    else natDigits fuel (n / 10) ++ [Nat.digitChar (n % 10)]

def natToString (n : Nat) : String := (natDigits (n + 1) n).foldl .push ""

def intToString : Int → String
  | .ofNat m => natToString m
  | .negSucc m => "-" ++ natToString (m + 1)
end Vsa.While
open Vsa.While
namespace Vsa.Sim
theorem toInt_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt = (x.toNat : Int) - 2^64 := by
  rw [BitVec.toInt_eq_toNat_cond]; have hx := x.isLt; rw [if_neg (by omega)]; simp

theorem toInt_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; rw [if_pos (by omega)]

theorem neg_toNat_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    ((0#64) - x).toNat = 2^64 - x.toNat := by
  rw [BitVec.toNat_sub]; have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega

theorem digitChar_eq (d : Nat) (h : d < 10) : Nat.digitChar d = Char.ofNat (48 + d) := by
  match d, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

theorem natDigits_fuel (f1 f2 n : Nat) (h1 : n + 1 ≤ f1) (h2 : n + 1 ≤ f2) :
    natDigits f1 n = natDigits f2 n := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold natDigits
      by_cases hlt : n < 10
      · simp [hlt]
      · simp only [hlt, if_false]
        rw [ih f2 (n/10) (by omega) (by omega)]

theorem natDigits_step (n : Nat) (h : 10 ≤ n) :
    natDigits (n + 1) n = natDigits (n / 10 + 1) (n / 10) ++ [Nat.digitChar (n % 10)] := by
  unfold natDigits
  have hlt : ¬ n < 10 := by omega
  simp only [hlt, if_false]
  congr 1
  exact natDigits_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)

theorem neg_magnitude (v : BitVec 64) (hneg : 2 ^ 63 ≤ v.toNat) :
    (- v).toNat = (- v.toInt).toNat := by
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have hn : (- v) = (0#64) - v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_sub]; simp
  rw [hn, neg_toNat_of_top v hneg, toInt_of_top v hneg]
  omega

theorem intToString_nonneg (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    intToString v.toInt = natToString v.toNat := by
  rw [toInt_of_notop v h]; rfl

theorem intToString_neg (v : BitVec 64) (h : 2 ^ 63 ≤ v.toNat) :
    intToString v.toInt = "-" ++ natToString (- v).toNat := by
  rw [neg_magnitude v h]
  have hlt : v.toInt < 0 := by rw [toInt_of_top v h]; have := v.isLt; omega
  rcases hi : v.toInt with m | m
  · exact absurd (hi ▸ hlt) (by simp)
  · rfl

theorem intToString_of_bv (v : BitVec 64) :
    intToString v.toInt =
      (if 2 ^ 63 ≤ v.toNat then "-" ++ natToString (- v).toNat
       else natToString v.toNat) := by
  by_cases h : 2 ^ 63 ≤ v.toNat
  · rw [if_pos h, intToString_neg v h]
  · rw [if_neg h, intToString_nonneg v (by omega)]

theorem digitChar_toNat_39 (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat = 48 + d := by
  match d, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

theorem digitChar_ascii_39 (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat ≤ 127 := by
  rw [digitChar_toNat_39 d h]; omega

theorem natDigits_ascii_39 (f n : Nat) : ∀ c ∈ natDigits f n, c.toNat ≤ 127 := by
  induction f generalizing n with
  | zero => intro c hc; simp [natDigits] at hc
  | succ f ih =>
    intro c hc
    unfold natDigits at hc
    by_cases h : n < 10
    · rw [if_pos h] at hc
      rw [List.mem_singleton.mp hc]
      exact digitChar_ascii_39 n h
    · rw [if_neg h] at hc
      rcases List.mem_append.mp hc with h1 | h1
      · exact ih (n / 10) c h1
      · rw [List.mem_singleton.mp h1]
        exact digitChar_ascii_39 (n % 10) (Nat.mod_lt _ (by omega))

theorem foldl_push_toList_39 (l : List Char) (s : String) :
    (l.foldl String.push s).toList = s.toList ++ l := by
  induction l generalizing s with
  | nil => simp
  | cons c t ih => rw [List.foldl_cons, ih, String.toList_push]; simp

theorem natToString_toList_39 (n : Nat) :
    (natToString n).toList = natDigits (n + 1) n := by
  unfold Vsa.While.natToString
  rw [foldl_push_toList_39]
  rfl

theorem digitList_eq_natDigits_39 (n2 : Nat) : ∀ (mag : Nat), 1 ≤ n2 →
    mag / 10 ^ (n2 - 1) ≤ 9 → (n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) →
    (List.range n2).map (fun k => Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10))
      = natDigits (mag + 1) mag := by
  induction n2 with
  | zero => intro mag h1 _ _; omega
  | succ m ih =>
    intro mag h1 hub hlb
    cases m with
    | zero =>

      have hm9 : mag ≤ 9 := by
        have h := hub
        rwa [show 0 + 1 - 1 = 0 from rfl, Nat.pow_zero, Nat.div_one] at h
      rw [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
      unfold natDigits
      rw [if_pos (show mag < 10 by omega)]
      rw [show 0 + 1 - 1 - 0 = 0 from rfl, Nat.pow_zero, Nat.div_one,
        Nat.mod_eq_of_lt (by omega)]
    | succ j =>

      have hgt : 9 < mag / 10 ^ j := by
        rcases hlb with h | h
        · omega
        · rwa [show j + 1 + 1 - 2 = j from by omega] at h
      have hmag10 : 10 ≤ mag := by
        have hle : mag / 10 ^ j ≤ mag := Nat.div_le_self _ _
        omega

      rw [natDigits_step mag hmag10, List.range_succ, List.map_append]

      have hub' : (mag / 10) / 10 ^ (j + 1 - 1) ≤ 9 := by
        rw [show j + 1 - 1 = j from rfl, Nat.div_div_eq_div_mul,
          show 10 * 10 ^ j = 10 ^ (j + 1) from by rw [Nat.pow_succ']]
        exact hub
      have hlb' : j + 1 = 1 ∨ 9 < (mag / 10) / 10 ^ (j + 1 - 2) := by
        cases j with
        | zero => exact Or.inl rfl
        | succ i =>
          refine Or.inr ?_
          rw [show i + 1 + 1 - 2 = i from by omega, Nat.div_div_eq_div_mul,
            show 10 * 10 ^ i = 10 ^ (i + 1) from by rw [Nat.pow_succ']]
          exact hgt
      congr 1
      ·
        rw [← ih (mag / 10) (by omega) hub' hlb']
        apply List.map_congr_left
        intro k hk
        have hklt : k < j + 1 := List.mem_range.mp hk
        have hexp : mag / 10 ^ (j + 1 + 1 - 1 - k) = (mag / 10) / 10 ^ (j + 1 - 1 - k) := by
          rw [show j + 1 + 1 - 1 - k = (j - k) + 1 from by omega,
            show j + 1 - 1 - k = j - k from by omega,
            Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        rw [hexp]
      ·
        simp only [List.map_cons, List.map_nil]
        rw [show j + 1 + 1 - 1 - (j + 1) = 0 from by omega, Nat.pow_zero, Nat.div_one]

theorem digits_eq_natToString (mag n2 : Nat) (bs : Nat → BitVec 8)
    (h1 : 1 ≤ n2)
    (hbs : ∀ k, k < n2 → bs k = BitVec.ofNat 8 (48 + mag / 10 ^ (n2 - 1 - k) % 10))
    (hub : mag / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) :
    (List.range n2).map bs
      = (natToString mag).toList.map (fun ch => BitVec.ofNat 8 ch.toNat) := by
  rw [natToString_toList_39, ← digitList_eq_natDigits_39 n2 mag h1 hub hlb, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hklt : k < n2 := List.mem_range.mp hk
  rw [hbs k hklt]
  show BitVec.ofNat 8 (48 + mag / 10 ^ (n2 - 1 - k) % 10)
      = BitVec.ofNat 8 (Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10)).toNat
  rw [digitChar_toNat_39 _ (Nat.mod_lt _ (by omega))]

end Vsa.Sim
namespace VsaIris.Newlib
inductive Conv where
  | str
  | int
  deriving DecidableEq

def parseFmt : List (BitVec 8) → Option (List Conv)
  | [] => some []
  | b :: rest =>
    if b = 0x25#8 then
      match rest with
      | c :: r =>
        if c = 0x73#8 then (Conv.str :: ·) <$> parseFmt r
        else if c = 0x64#8 then (Conv.int :: ·) <$> parseFmt r
        else none
      | [] => none
    else parseFmt rest

end VsaIris.Newlib
