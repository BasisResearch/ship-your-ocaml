import Vsa.Densify

/-!
# Keys only grow: no step removes a register or a memory byte

The lean-sail primitives change the register map and the memory only by
`insert` (`writeReg`, `writeByte`); nothing erases. `keysRel KR KM` relates
a state to itself when it holds every register in `KR` and every byte in
`KM`, and it is a `StateRelB`, so `stepOnce`'s generated respectfulness
proof (`Gen.stepOnce_resp`) instantiated at it says: every key present
before a step is present after it (`stepOnce_covers`).
-/

namespace Vsa.Densify

open Sail ConcurrencyInterfaceV1 LeanRV64DExecutable
open Vsa.Machine (MState)

/-- The state holds every register in `KR` and every byte in `KM`. -/
structure Covers (KR : Register → Prop) (KM : Nat → Prop) (σ : MState) : Prop where
  regs : ∀ r, KR r → (σ.regs.get? r).isSome
  mem : ∀ a, KM a → (σ.mem[a]?).isSome

/-- The same state, holding the keys `KR`, `KM`. -/
def keysRel (KR : Register → Prop) (KM : Nat → Prop) : StateRelB where
  R σ σ' := σ = σ' ∧ Covers KR KM σ
  regs h := by rw [h.1]
  mem h := by rw [h.1]; exact MemEqv.refl _
  cycle h := by rw [h.1]
  writeReg r v h := by
    obtain ⟨rfl, c⟩ := h
    refine ⟨rfl, fun A hA => ?_, c.mem⟩
    show ((_ : Std.ExtDHashMap Register RegisterType).insert r v).get? A |>.isSome
    rw [Std.ExtDHashMap.get?_insert]
    by_cases hc : (r == A) = true
    · simp only [hc, dif_pos, Option.isSome_some]
    · simp only [hc, dif_neg, Bool.not_eq_true]; exact c.regs A hA
  writeByte a v h := by
    obtain ⟨rfl, c⟩ := h
    refine ⟨rfl, c.regs, fun b hb => ?_⟩
    show ((_ : Std.ExtHashMap Nat (BitVec 8)).insert a v)[b]?.isSome
    rw [Std.ExtHashMap.getElem?_insert]
    split
    · rfl
    · exact c.mem b hb
  tick h := by obtain ⟨rfl, c⟩ := h; exact ⟨rfl, c.regs, c.mem⟩
  print _ h := by obtain ⟨rfl, c⟩ := h; exact ⟨rfl, c.regs, c.mem⟩

/-- **One step keeps every key.** -/
theorem stepOnce_covers {KR : Register → Prop} {KM : Nat → Prop} {i u : Nat} {σ σ' : MState}
    {r : Sum (Option Nat × Nat) (Nat × Nat)} (h : (Vsa.stepOnce i u).run σ = .ok r σ')
    (c : Covers KR KM σ) : Covers KR KM σ' := by
  have hr := (Gen.stepOnce_resp (Rel := keysRel KR KM) i u).run σ σ ⟨rfl, c⟩
  change Vsa.stepOnce i u σ = .ok r σ' at h
  rw [h] at hr
  exact hr.2.2

end Vsa.Densify
