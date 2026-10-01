import OCaml.Vm.Primitives.Control

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- Data-access obligations for a generated block. Code pins and decoding
are supplied separately by its generated certificate. These are finite
scalar read/write facts, not a premise about a machine execution. -/
def AccessPlan : Std.ExtHashMap Nat (BitVec 8) → GRegs →
    List (List (BitVec 8)) → List MInstr → Prop
  | _, _, _, [] => True
  | m, L, loads, a :: rest =>
    MemFacts m L (loads.headD []) a ∧
    AccessPlan (stepMemM m a L) (stepGM a L (loads.headD [])) (stepLdsM a.kind loads) rest

/-- Assemble code and scalar-access certificates through the block kernel's
own symbolic memory/register updates. -/
theorem accessPlan_facts {mc m L loads body} (code : CodeFacts mc body)
    (access : AccessPlan m L loads body) : ProgFactsM mc m L loads body := by
  induction body generalizing m L loads with
  | nil => trivial
  | cons a rest ih => exact ⟨code.1, code.2.1, access.1, ih code.2.2 access.2⟩

end OCaml.Vm.Primitives
