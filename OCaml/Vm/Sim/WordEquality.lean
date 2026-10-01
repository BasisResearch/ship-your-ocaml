import OCaml.Vm.Sim.StackAcc
import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

/-- Physical equality must reflect equality of represented machine words.
This static representation obligation is supplied by value typing and placement
injectivity, not by any assumption about execution of EQ/NEQ. -/
structure WordEquality (pl : Place) (a b : Val) : Prop where
  reflects : ∀ x y, valWord pl a = some x → valWord pl b = some y →
    physEq? a b = some (x == y)

/-- The native comparison reads the stack operand before the accumulator. -/
theorem WordEquality.guard {pl : Place} {a b : Val} {x y : BitVec 64} {e : Bool}
    (h : WordEquality pl a b) (left : valWord pl a = some x)
    (right : valWord pl b = some y) (test : physEq? a b = some e) :
    (y == x) = e := by
  have same := Option.some.inj ((h.reflects x y left right).symm.trans test)
  exact Bool.beq_comm.trans same

/-- Tagged integers are injective, so their equality obligation is discharged. -/
theorem WordEquality.ints (pl : Place) (a b : BitVec 63) :
    WordEquality pl (.int a) (.int b) := by
  constructor
  intro x y left right
  have hx : tag64 a = x := Option.some.inj left
  have hy : tag64 b = y := Option.some.inj right
  subst x
  subst y
  change some (decide (Val.int a = Val.int b)) = some (tag64 a == tag64 b)
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq, Val.int.injEq]
  constructor
  · intro h; rw [h]
  · intro h
    have same := congrArg untag h
    simpa only [untag_tag] using same

end OCaml.Vm.Sim
