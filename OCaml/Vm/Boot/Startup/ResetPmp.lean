import Vsa.Sim.SailUnchanged
import Vsa.Sim.InitValues
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
theorem pmp_get (i : Int) : (initPmpcfg[i]!) = 0#8 := by
  change (Vector.replicate 64 (0#8))[i.toNat]! = _
  by_cases h : i.toNat < 64
  · simp [h]
  · simp [h]; rfl
theorem pmp_set (i : Nat) : vectorUpdate initPmpcfg i (0#8) = initPmpcfg := by
  apply Vector.ext
  intro j hj
  simp [vectorUpdate, Vector.getElem_set!, initPmpcfg]
/-- The architectural PMP loop preserves a zero-initialized configuration.
The IntRange fold proof handles every iteration without concrete replay. -/
theorem reset_pmp_run (s : MState) (h : s.regs.get? .pmpcfg_n = some initPmpcfg) :
    (reset_pmp ()).run s = .ok () s := by
  apply Stays.unit (I := fun t => t.regs.get? .pmpcfg_n = some initPmpcfg) _ s h
  unfold reset_pmp
  apply Stays.bind
  · apply Stays.forIn
    intro i b
    intro t ht
    refine ⟨.yield (), ?_⟩
    simp only [EStateM.run, Bind.bind, EStateM.bind,
      readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe,
      MonadStateOf.get, EStateM.get, pure, EStateM.pure, ht, pmp_get]
    change (match (writeReg .pmpcfg_n (vectorUpdate initPmpcfg i.toNat (0#8))).run t with
      | .ok v u => EStateM.Result.ok (ForInStep.yield v) u
      | .error e u => EStateM.Result.error e u) = .ok (ForInStep.yield ()) t
    rw [pmp_set, writeReg_present t _ _ ht]
  · intro v; exact Stays.pure _ _
end OCaml.Vm.Boot.Startup
