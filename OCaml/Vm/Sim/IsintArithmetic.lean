import OCaml.Vm.Sim.ImmediateArithmetic
import OCaml.Vm.Repr

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

/-- The arithmetic performed by the generated ISINT body. -/
def isintWord (w : BitVec 64) : BitVec 64 := ((w <<< (1 : Nat)) &&& 2#64) + 1#64

theorem isintWord_eq (w : BitVec 64) :
    isintWord w = tag64 (if w.toNat % 2 = 1 then 1#63 else 0#63) := by
  have hmask : w &&& 1#64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod,
      BitVec.toNat_ofNat]
    omega
  have htwo : (1#64 <<< (1 : Nat)) = 2#64 := by decide
  unfold isintWord
  rw [← htwo, ← BitVec.shiftLeft_and_distrib, hmask]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> decide

theorem ofBool_int (b : Bool) : Val.ofBool b = .int (if b then 1#63 else 0#63) := by
  cases b <;> rfl

/-- Only alignment, not a heap graph property: necessary for ISINT to
classify represented pointers and bytecode addresses as non-integers. -/
structure EvenPlace (pl : Place) : Prop where
  code : pl.codeBase % 2 = 0
  heap : ∀ l a, pl.φ l = some a → a % 2 = 0
  atoms : pl.atomBase % 2 = 0

theorem valWord_parity {pl : Place} (aligned : EvenPlace pl) {v : Val} {w : BitVec 64}
    (repr : valWord pl v = some w) (notRaw : ∀ x, v ≠ .raw x) :
    w.toNat % 2 = if v.isInt then 1 else 0 := by
  cases v with
  | int n =>
    cases repr
    simp only [Val.isInt, ↓reduceIte, tag_toNat]
    omega
  | ptr l k =>
    cases hp : pl.φ l with
    | none => simp [valWord, hp] at repr
    | some a =>
      simp only [valWord, hp, Option.map_some, Option.some.injEq] at repr
      subst w
      have he := aligned.heap l a hp
      change ((a + 8 * k) % 2^64) % 2 = 0
      omega
  | code pc =>
    cases repr
    have he := aligned.code
    change ((pl.codeBase + 4 * pc) % 2^64) % 2 = 0
    omega
  | atom tag =>
    cases repr
    have he := aligned.atoms
    change ((pl.atomBase + 8 * tag + 8) % 2^64) % 2 = 0
    omega
  | raw x => exact (notRaw x rfl).elim

theorem isintWord_repr {pl : Place} (aligned : EvenPlace pl) {v : Val} {w : BitVec 64}
    (repr : valWord pl v = some w) (notRaw : ∀ x, v ≠ .raw x) :
    isintWord w = tag64 (if v.isInt then 1#63 else 0#63) := by
  rw [isintWord_eq, valWord_parity aligned repr notRaw]
  cases v.isInt <;> rfl

/-- Tagged integer zero is exactly the runtime's false word. -/
theorem tag_eq_false (n : BitVec 63) : tag64 n = 1#64 ↔ n = 0 := by
  constructor
  · intro h
    have value := congrArg BitVec.toNat h
    rw [tag_toNat] at value
    change 2 * n.toNat + 1 = 1 at value
    apply BitVec.eq_of_toNat_eq
    change n.toNat = 0
    omega
  · rintro rfl
    rfl

/-- Even placements distinguish false from every non-integer, non-raw value. -/
theorem false_word_iff {pl : Place} (aligned : EvenPlace pl) {v : Val} {w : BitVec 64}
    (repr : valWord pl v = some w) (notRaw : ∀ x, v ≠ .raw x) :
    w = 1#64 ↔ v = .int 0 := by
  constructor
  · intro hw
    have parity := valWord_parity aligned repr notRaw
    rw [hw] at parity
    have integer : v.isInt = true := by
      cases hv : v.isInt <;> simp_all
    cases v <;> simp only [Val.isInt, Bool.false_eq_true] at integer
    case int n =>
      have tag : tag64 n = 1#64 := (Option.some.inj repr).trans hw
      rw [(tag_eq_false n).mp tag]
    all_goals contradiction
  · intro hv
    rw [hv] at repr
    exact (Option.some.inj repr).symm

/-- Value representation alone does not exclude odd pointer addresses. This
checked alias explains the explicit alignment premise in the ISINT bridge. -/
theorem isint_not_valWord : ¬ (∀ (pl : Place) (v : Val) (w : BitVec 64),
    valWord pl v = some w → isintWord w = tag64 (if v.isInt then 1#63 else 0#63)) := by
  intro h
  have bad := h ⟨fun _ => some 1, 0, 0⟩ (.ptr 0 0) 1#64 rfl
  exact (by decide : isintWord 1#64 ≠ tag64 0#63) bad

end OCaml.Vm.Sim
