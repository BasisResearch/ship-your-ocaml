import Vsa.Sim.LibraryFacts
import Vsa.MemRepr

namespace Vsa.Sim
open Vsa.MemRepr LeanRV64DExecutable Sail

theorem getElem_writeMap2_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a2 k : Nat)
    (d : BitVec (8 * 2)) (hk : k < a2 ∨ a2 + 2 ≤ k) :
    ((mem.insert a2 (d.extractLsb' 0 8)).insert (a2 + 1) (d.extractLsb' 8 8))[k]? = mem[k]? := by
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

theorem read64_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read64 (writeMap8 mem a d) a = some d.toNat := by
  have e0 := getElem_writeMap8_0 mem a d
  have e1 := getElem_writeMap8_1 mem a d
  have e2 := getElem_writeMap8_2 mem a d
  have e3 := getElem_writeMap8_3 mem a d
  have e4 := getElem_writeMap8_4 mem a d
  have e5 := getElem_writeMap8_5 mem a d
  have e6 := getElem_writeMap8_6 mem a d
  have e7 := getElem_writeMap8_7 mem a d
  simp only [read64, readLE, e0, e1, e2, e3, e4, e5, e6, e7, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 64 := by have := d.isLt; simpa using this
  omega

def AgreeP (P : Nat → Prop) (m m' : Mem) : Prop :=
  ∀ a, P a → m[a]? = m'[a]?

theorem AgreeP.trans {P : Nat → Prop} {m m' m'' : Mem}
    (h1 : AgreeP P m m') (h2 : AgreeP P m' m'') : AgreeP P m m'' :=
  fun a ha => (h1 a ha).trans (h2 a ha)

theorem AgreeP.mono {P Q : Nat → Prop} {m m' : Mem}
    (hsub : ∀ a, Q a → P a) (h : AgreeP P m m') : AgreeP Q m m' :=
  fun a ha => h a (hsub a ha)

theorem readLE_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m') :
    ∀ (n a : Nat), (∀ k, k < n → P (a + k)) → readLE m a n = readLE m' a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a hP
    have hhead : m[a]? = m'[a]? := by
      have := h a (by simpa using hP 0 (Nat.succ_pos n)); simpa using this
    have htail : readLE m (a + 1) n = readLE m' (a + 1) n := by
      apply ih
      intro k hk
      have := hP (k + 1) (by omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    simp only [readLE, hhead, htail]

theorem read64_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 8 → P (a + k)) : read64 m a = read64 m' a :=
  readLE_agreeP h 8 a hP

end Vsa.Sim
