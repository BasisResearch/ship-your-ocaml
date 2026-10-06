import OCaml.Bytecode.Semantics

/-!
# Per-state facts read at an opcode

`Val.inRange` (in `Value.lean`) is what BcSem's EQ/NEQ and BEQ/BNEQ guards
check: a value's word lies in its own region, so physical equality reflects
word equality (`WordEquality.of_place`). `St.atOp` names the opcode at the
PC (the per-state C_CALL checks of `WhileMinShape`).
-/

namespace OCaml.Bytecode

/-- An in-range value is not a raw word. -/
theorem Val.inRange_notRaw {n : Nat} {h : Heap} {v : Val} (hb : v.inRange n h = true)
    (w : BitVec 64) : v ≠ .raw w := by
  rintro rfl; simp [Val.inRange] at hb

/-- The opcode word at the PC is `op`. -/
def St.atOp (P : Prog) (s : St) (op : Opcode) : Prop :=
  P.code[s.pc]? = some (BitVec.ofNat 32 op.toNat)

instance (P : Prog) (s : St) (op : Opcode) : Decidable (s.atOp P op) := by
  unfold St.atOp; infer_instance

end OCaml.Bytecode
