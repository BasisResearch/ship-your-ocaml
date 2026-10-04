import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Boot.Startup.NativeSave
namespace OCaml.Vm.Boot.Startup
open Vsa.Sim

/-- A store log confined to one window is also confined to any enclosing window. -/
theorem log_in_larger_window {small big : W} {log : List WEntry}
    (h : LogInW [small] log) (lower : big.lo ≤ small.lo) (upper : small.hi ≤ big.hi) :
    LogInW [big] log := by
  induction log with
  | nil => trivial
  | cons entry rest ih =>
    have bounds : small.lo ≤ entry.1 ∧ entry.1 + entry.2.1 ≤ small.hi := by
      exact h.1.resolve_right id
    refine ⟨Or.inl ⟨?_, ?_⟩, ih h.2⟩ <;> omega

/-- Concatenating two confined store logs retains their common window certificate. -/
theorem log_in_append {windows : List W} {first second : List WEntry}
    (left : LogInW windows first) (right : LogInW windows second) :
    LogInW windows (first ++ second) := by
  induction first with
  | nil => exact right
  | cons entry rest ih => exact ⟨left.1, ih left.2⟩
end OCaml.Vm.Boot.Startup
