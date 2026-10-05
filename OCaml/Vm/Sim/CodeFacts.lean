import OCaml.Vm.Sim.ArmInput

/-!
# Code facts (a2-sem; docs/lanes/F1-split.md)

The code-side facts of the running invariant: what the represented code
region holds at the bytecode PC and at its operands, and that those
addresses are readable. `DispatchCode` (`ArmInput.lean`) is the opcode
word's interface; `OperandCode` is the same for the `k`-th word after the
PC. Rows consume these interfaces, so they are independent of how the
facts are derived from decoding (`decodeAt`) and code placement.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- The operand word `k` words after the PC is `w`, for every placement
that represents the state. -/
structure OperandCode (P : Prog) (s : St) (c : Config) (k : Nat) (w : BitVec 32) : Prop where
  at_ : ∀ pl cp sp high, VmReprAt P s c pl cp sp high → OperandAt P pl (s.pc + k) w

theorem OperandCode.of_input {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {op : Opcode}
    {pl : Place} {cp : ChanPlace} {sp high k : Nat} {w : BitVec 32}
    (h : OperandCode P s c k w) (input : ArmInput L P s op c pl cp sp high) :
    OperandAt P pl (s.pc + k) w :=
  h.at_ pl cp sp high input.toVmReprAt

end OCaml.Vm.Sim
