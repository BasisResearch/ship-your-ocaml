import OCaml.Bytecode.Semantics

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

/-- F1 primitive outcomes handled by the returning/terminal C_CALL adapters. -/
def PrimitiveF1Outcome : PRes → Prop
  | .ok _ _ _ | .exit _ _ | .unsupported => True
  | .raise _ _ _ | .callback _ _ _ _ => False

/-- The current F1 table cannot produce a raising or callback outcome. -/
theorem primF1_outcome (name : String) (args : List Val) (heap : Heap) (world : World) :
    PrimitiveF1Outcome (primF1Impl name args heap world) := by
  unfold primF1Impl
  split <;> dsimp only
  all_goals repeat first | exact True.intro | split

/-- A represented F1 C_CALL needs no raising-primitive premise. -/
theorem primF1_not_raise (name : String) (args : List Val) (heap : Heap) (world : World)
    (exception : Val) (heap' : Heap) (world' : World) :
    primF1Impl name args heap world ≠ .raise exception heap' world' := by
  intro eq
  have classified := primF1_outcome name args heap world
  rw [eq] at classified
  exact classified

end OCaml.Vm.Sim
