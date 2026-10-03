import Vsa.Densify.Resp

namespace Vsa.Sim
open Vsa.Machine LeanRV64DExecutable Sail ConcurrencyInterfaceV1

/-- Successful Sail execution that leaves its input state unchanged. -/
def Stays (I : MState → Prop) {α : Type} (action : SailM α) : Prop :=
  ∀ s, I s → ∃ v, action.run s = .ok v s

theorem Stays.pure (I : MState → Prop) {α : Type} (v : α) : Stays I (pure v) :=
  fun _ _ => ⟨v, rfl⟩

theorem Stays.bind {I : MState → Prop} {α β : Type} {action : SailM α} {next : α → SailM β}
    (first : Stays I action) (rest : ∀ v, Stays I (next v)) : Stays I (action >>= next) := by
  intro s hs
  obtain ⟨v, front⟩ := first s hs
  obtain ⟨w, back⟩ := rest v s hs
  refine ⟨w, ?_⟩
  simp only [Bind.bind, EStateM.instMonad, EStateM.bind, EStateM.run]
  rw [show action s = .ok v s from front]
  exact back

/-- Reuse the model's existing IntRange fold law; no concrete iteration replay. -/
theorem Stays.forIn {I : MState → Prop} {β : Type} (range : IntRange) (init : β)
    (body : Int → β → SailM (ForInStep β)) (h : ∀ i b, Stays I (body i b)) :
    Stays I (forIn range init body) :=
  Vsa.Densify.forIn_range_of (m := SailM) (fun a => Stays I a)
    (fun v => Stays.pure I v) (fun _ _ first rest => Stays.bind first rest) range init body h

theorem Stays.unit {I : MState → Prop} {action : SailM Unit} (h : Stays I action)
    (s : MState) (hs : I s) : action.run s = .ok () s := by
  obtain ⟨v, run⟩ := h s hs
  cases v
  exact run

theorem insert_present {rs : Std.ExtDHashMap Register RegisterType} {r : Register}
    {v : RegisterType r} (present : rs.get? r = some v) : rs.insert r v = rs := by
  apply Std.ExtDHashMap.ext_get?
  intro q
  by_cases eq : r = q
  · subst q; simp [present]
  · simp [Std.ExtDHashMap.get?_insert, eq]

theorem writeReg_present (s : MState) (r : Register) (v : RegisterType r)
    (present : s.regs.get? r = some v) : (writeReg r v).run s = .ok () s := by
  have equal := insert_present present
  simp only [EStateM.run, writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, equal]

end Vsa.Sim
