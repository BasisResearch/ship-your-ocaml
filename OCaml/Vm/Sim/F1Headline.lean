import OCaml.Vm.Sim.F1Table
import OCaml.Programs.F1Check
import OCaml.Theorems

/-!
# Layer A for F1 on the pinned layout

The F1 arm table (`f1_table`, generated) gives the F1 refinement statement for
the pinned layout `Gc.f1Layout` and the G1 budget, given the stack capacity
of the budget (`g1_capacity`), the remembered set's growth paths
(`BarrierGrowthPaths`, GC lane) and the program-level premises of the rows (`F1Premises`), and
its `whileMin` instance at the captured cut.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- **Layer A for F1, pinned layout**, from the rows' program-level premises. -/
theorem ocamlrun_refinement_F1_pinned (growth : BarrierGrowthPaths Gc.f1Layout)
    (pre : ∀ P, OCaml.GoodF1 P → OCaml.Fits Gc.g1Budget P → GcSafe P → F1Premises P) :
    OCaml.ocamlrun_refinement_F1_Statement Gc.f1Layout Gc.g1Budget :=
  OCaml.ocamlrun_refinement_F1_of_arms fun P c loaded good fits gc =>
    ⟨_, f1_table loaded good fits growth (pre P good fits gc)⟩

/-- **The `whileMin` machine run**: the captured cut of the pinned image
halts printing `55`, `2500`, `36` with exit code 0, given the premises of the
rows of the opcodes `whileMin` reaches (`whileMinOps`, checked in the one
shape run) and a0-boot's newlib heap at the cut
(`cut_heapReady_covers_Statement`); the other rows are vacuous. -/
theorem whileMin_halts_f1
    (heap : Boot.WhileMin.cut_heapReady_covers_Statement Gc.f1Covered [(Gc.refTable, 56)])
    (growth : BarrierGrowthPaths Gc.f1Layout)
    (pre : F1PremisesFor (fun op => OCaml.Programs.whileMinOps.contains op) OCaml.Programs.whileMin) :
    Halts Boot.WhileMin.cut "55\n2500\n36\n" 0 :=
  have table := f1_table_for (Gc.whileMin_loaded_f1 heap) OCaml.Programs.whileMin_goodF1
    OCaml.Programs.whileMin_fits OCaml.Programs.whileMin_ops growth pre
  ((table.simR OCaml.Programs.whileMin_goodF1).refines OCaml.Programs.whileMin_goodF1.good).1 _ _
    |>.1 OCaml.Programs.whileMin_bcSem

end OCaml.Vm.Sim
