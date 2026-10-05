import OCaml.Bytecode.Semantics

/-!
# The trap pointer stays inside the stack

`s.trap` counts the stack words at and below the innermost trap frame;
PUSHTRAP's saved link `len + 4 - trap` is the native `Trap_link` only when
`trap ≤ stack length`. A program that pops past its trap frame breaks this,
so `TrapBounded P` is a named premise; a concrete program discharges it by
one checked run (`OCaml/Programs/WhileMinExtra.lean`). A general invariant
(trap frames are never popped except by POPTRAP or a raise) is open (a2-sem).
-/

namespace OCaml.Bytecode

/-- The per-state check. -/
def St.trapOk (s : St) : Bool := decide (s.trap ≤ s.stack.length)

/-- **The trap pointer points into the stack.** -/
structure TrapBounded (P : Prog) : Prop where
  bounded : ∀ s, Reach P s → s.trap ≤ s.stack.length

theorem TrapBounded.of_check {P : Prog} (h : ∀ s, Reach P s → s.trapOk = true) :
    TrapBounded P where
  bounded s reach := of_decide_eq_true (h s reach)

end OCaml.Bytecode
