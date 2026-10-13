import Vsa.Sim.BlockMem
namespace OCaml.Vm.Boot.Startup
open Vsa.Sim LeanRV64DExecutable

/-! Straight-line `slli`/`add`/`sub` chains are linear in one input `y`: each
register they touch holds `k * y` for a constant `k`. `linRun` computes the
constants by evaluation; `linRun_sound` lifts them to the block evaluator, so
a multiply-by-constant chain is never unfolded symbolically. -/

/-- A register's coefficient; `x0` is `0 * y`. -/
def linCoef (n : Nat) (C : List (Nat × BitVec 64)) : Option (BitVec 64) :=
  if n = 0 then some 0#64 else lookupG n C

/-- One instruction over coefficients, if it is linear. -/
def linStep (a : MInstr) (C : List (Nat × BitVec 64)) : Option (List (Nat × BitVec 64)) :=
  match a.kind with
  | .slli => (linCoef a.rs1 C).map fun k =>
      (a.rd, Sail.shift_bits_left k (Sail.BitVec.extractLsb (shamtOf a) 5 0)) :: eraseG a.rd C
  | .add => match linCoef a.rs1 C, linCoef a.rs2 C with
    | some k1, some k2 => some ((a.rd, k1 + k2) :: eraseG a.rd C)
    | _, _ => none
  | .sub => match linCoef a.rs1 C, linCoef a.rs2 C with
    | some k1, some k2 => some ((a.rd, k1 - k2) :: eraseG a.rd C)
    | _, _ => none
  | _ => none

def linRun : List MInstr → List (Nat × BitVec 64) → Option (List (Nat × BitVec 64))
  | [], C => some C
  | a :: r, C => (linStep a C).bind (linRun r)

/-- The registers `L` hold the coefficients `C` times `y`. -/
def LinHolds (y : BitVec 64) (C : List (Nat × BitVec 64)) (L : GRegs) : Prop :=
  ∀ n k, lookupG n C = some k → lookupG n L = some (k * y)

theorem lookupG_erase (n m : Nat) (L : GRegs) : lookupG n (eraseG m L) = if n = m then none else lookupG n L := by
  induction L with
  | nil => simp [lookupG, eraseG]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases km : k = m
    · subst km
      by_cases nk : n = k
      · subst nk; simp only [eraseG, ite_true, ih]
      · simp only [eraseG, ite_true, ih, nk, ite_false, lookupG, show ¬ k = n from fun e => nk e.symm]
    · by_cases kn : k = n
      · subst kn; simp only [eraseG, km, ite_false, lookupG, ite_true, show ¬ k = m from km]
      · simp only [eraseG, km, ite_false, lookupG, kn, ih]

theorem linCoef_src {y : BitVec 64} {C : List (Nat × BitVec 64)} {L : GRegs} (h : LinHolds y C L) {n : Nat}
    {k : BitVec 64} (coef : linCoef n C = some k) : srcVal n L = k * y := by
  unfold linCoef at coef
  cases n with
  | zero => simp at coef; subst coef; simp [srcVal]
  | succ m =>
    simp only [Nat.add_one_ne_zero, ite_false] at coef
    simp [srcVal, h _ _ coef]

theorem LinHolds.write {y : BitVec 64} {C : List (Nat × BitVec 64)} {L : GRegs} (h : LinHolds y C L) (rd : Nat)
    (k : BitVec 64) : LinHolds y ((rd, k) :: eraseG rd C) ((rd, k * y) :: eraseG rd L) := by
  intro n k' hn
  simp only [lookupG] at hn ⊢
  split at hn
  · subst_vars; simp_all
  · rename_i ne
    have ne' : ¬ n = rd := fun e => ne (e ▸ rfl)
    rw [lookupG_erase, if_neg ne'] at hn
    rw [if_neg ne, lookupG_erase, if_neg ne']
    exact h n k' hn

theorem shift_mul (k y : BitVec 64) (s : BitVec 6) :
    Sail.shift_bits_left (k * y) s = Sail.shift_bits_left k s * y := by
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
  rw [BitVec.mul_assoc, BitVec.mul_comm y, ← BitVec.mul_assoc]

theorem linStep_sound {y : BitVec 64} {a : MInstr} {C C' : List (Nat × BitVec 64)} {L : GRegs}
    (bs : List (BitVec 8)) (h : LinHolds y C L) (step : linStep a C = some C') : LinHolds y C' (stepGM a L bs) := by
  unfold linStep at step
  unfold stepGM wvalM
  split at step
  · rename_i kind
    simp only [kind]
    cases coef : linCoef a.rs1 C with
    | none => simp [coef] at step
    | some k =>
      simp only [coef, Option.map_some, Option.some.injEq] at step
      subst step
      rw [linCoef_src h coef, shift_mul]
      exact h.write a.rd _
  · rename_i kind
    simp only [kind]
    split at step
    · rename_i k1 k2 c1 c2
      simp only [Option.some.injEq] at step
      subst step
      rw [linCoef_src h c1, linCoef_src h c2, ← BitVec.add_mul]
      exact h.write a.rd _
    · simp at step
  · rename_i kind
    simp only [kind]
    split at step
    · rename_i k1 k2 c1 c2
      simp only [Option.some.injEq] at step
      subst step
      have e : k1 * y - k2 * y = (k1 - k2) * y := by
        rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_mul, BitVec.neg_mul]
      rw [linCoef_src h c1, linCoef_src h c2, e]
      exact h.write a.rd _
    · simp at step
  · simp at step

theorem linRun_sound {y : BitVec 64} : ∀ {body : List MInstr} {C C' : List (Nat × BitVec 64)} {L : GRegs}
    (lds : List (List (BitVec 8))), LinHolds y C L → linRun body C = some C' → LinHolds y C' (runGM body L lds)
  | [], _, _, _, _, h, run => by simp only [linRun, Option.some.injEq] at run; subst run; exact h
  | a :: r, C, C', L, lds, h, run => by
    simp only [linRun] at run
    cases step : linStep a C with
    | none => simp [step] at run
    | some C1 =>
      simp only [step, Option.bind_some] at run
      show LinHolds y C' (runGM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds))
      exact linRun_sound (stepLdsM a.kind lds) (linStep_sound (lds.headD []) h step) run
end OCaml.Vm.Boot.Startup
