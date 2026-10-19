import OCaml.Vm.Primitives.GprsKeptCore

/-!
# Register presence persists along any run (named statement)

The Sail model's register writes insert into the register map and nothing
removes a register, so a general-purpose register present before a run is
present after it. Library summaries whose posts frame only the registers they
do not write (`strcmp_post`: x5–x7 and x10–x15 are unconstrained) lose this
fact; `GprsPersist_Statement` restores it.

Supplied by: a key-monotonicity lemma for the Sail register map across one
`Step` (every register write is an insert), lifted to `Steps` through the run
kernel. Open; listed in PHASES.md.
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

end OCaml.Vm.Primitives
