import OCaml.Vm.Primitives.GprsKeptCore
import Vsa.Densify.Keys
import OCaml.Run.Machine

/-!
# Register presence persists along any run (named statement)

The Sail model's register writes insert into the register map and nothing
removes a register, so a general-purpose register present before a run is
present after it. Library summaries whose posts frame only the registers they
do not write (`strcmp_post`: x5–x7 and x10–x15 are unconstrained) lose this
fact; `GprsPersist_Statement` restores it.

Both are proved (`gprsPersist`, `memPersist`): one step keeps every key
(`Vsa.Densify.stepOnce_covers`, `stepOnce`'s generated respectfulness proof at
the key-covering relation), and `Steps.covers` lifts it through the run
kernel (`iter_inv`).
-/

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- **Named statement**: every general-purpose register present at `c` is
present after any run from `c`. -/
def GprsPersist_Statement : Prop :=
  ∀ c d : Config, Steps c d → ∀ n, (gprGet c.σ n).isSome → (gprGet d.σ n).isSome

/-- A run keeps register presence and, when `gp` is framed, `GprsKept`. -/
theorem GprsKept.of_steps (persist : GprsPersist_Statement) {c d : Config} (run : Steps c d)
    (gp : gpr d 3 = gpr c 3) : GprsKept c d :=
  ⟨fun n _ _ p => persist c d run n p, gp⟩

/-- **Named statement**: every memory byte present at `c` is present after
any run from `c` (stores insert; nothing removes a byte). Library summaries
state memory as total reads (`getD 0`); the presence-based C-string facts
(`CStr`) need this to cross them. -/
def MemPersist_Statement : Prop :=
  ∀ c d : Config, Steps c d → ∀ a : Nat, (c.σ.mem[a]?).isSome → (d.σ.mem[a]?).isSome

/-- A run keeps every key it starts with. -/
theorem _root_.Vsa.Machine.Steps.covers {KR : LeanRV64DExecutable.Register → Prop} {KM : Nat → Prop} {c d : Config}
    (run : Steps c d) (h : Vsa.Densify.Covers KR KM c.σ) : Vsa.Densify.Covers KR KM d.σ := by
  obtain ⟨n, hn⟩ := OCaml.Run.vsa_steps_iff.1 run
  refine OCaml.Run.iter_inv (fun c : Config => Vsa.Densify.Covers KR KM c.σ) (fun hab ha => ?_) hn h
  cases OCaml.Run.vsaK_graph.iff.2 hab with
  | mk step => exact Vsa.Densify.stepOnce_covers step ha

/-- A run keeps every register present at its start. -/
theorem gprsPersist : GprsPersist_Statement := by
  intro c d run n present
  have cov := run.covers (KR := fun r => (c.σ.regs.get? r).isSome) (KM := fun _ => False)
    ⟨fun _ h => h, fun _ h => h.elim⟩
  revert present
  unfold gprGet
  split <;> intro present <;> first | exact cov.regs _ present | exact present

/-- A run keeps every memory byte present at its start. -/
theorem memPersist : MemPersist_Statement := fun c d run a present =>
  (run.covers (KR := fun _ => False) (KM := fun a => (c.σ.mem[a]?).isSome)
    ⟨fun _ h => h.elim, fun _ h => h⟩).mem a present

end OCaml.Vm.Primitives
