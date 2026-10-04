import OCaml.Vm.Sim.ClosurerecFirstInput
import OCaml.Vm.Sim.GroupedLog

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The final unused loop value may be negative; modular subtraction models it exactly. -/
def infixArityWord (functions index : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (6 * functions - 1) - BitVec.ofNat 64 (6 * index)

/-- Native order: infix header, stack pointer, arity, then code pointer. -/
def infixStores (pl : Place) (a stackStart functions index dest : Nat) : List WEntry :=
  [(a + 24 * index - 8, 8, blockHeader (3 * index) infixTag),
   (stackStart - 8 * index, 8, BitVec.ofNat 64 (a + 24 * index)),
   (a + 24 * index + 8, 8, infixArityWord functions index),
   (a + 24 * index, 8, BitVec.ofNat 64 (pl.codeBase + 4 * dest))]

/-- Targets exclude function zero, which the first-function span already installed. -/
def infixGroups (pl : Place) (a stackStart : Nat) (targets : List Nat) : List (List WEntry) :=
  (List.range targets.length).map fun i =>
    infixStores pl a stackStart (targets.length + 1) (i + 1) ((targets[i]?).getD 0)

theorem infix_groups_length (pl : Place) (a stackStart : Nat) (targets : List Nat) :
    (infixGroups pl a stackStart targets).length = targets.length := by simp [infixGroups]

theorem infix_group_at (pl : Place) (a stackStart : Nat) (targets : List Nat) (i : Nat) (bound : i < targets.length) :
    (infixGroups pl a stackStart targets)[i]'(by rw [infix_groups_length]; exact bound) =
      infixStores pl a stackStart (targets.length + 1) (i + 1) targets[i] := by
  simp [infixGroups, List.getElem?_eq_getElem bound]

end OCaml.Vm.Sim
