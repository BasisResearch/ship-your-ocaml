import OCaml.Bytecode.Semantics

/-!
# Per-state facts read at an opcode

`Val.inRange` (in `Value.lean`) is what BcSem's EQ/NEQ and BEQ/BNEQ guards
check: a value's word lies in its own region, so physical equality reflects
word equality (`WordEquality.of_place`). `St.atOp` names the opcode at the
PC; `DivisorsNonzero P` is a per-program fact (the zero-divisor raise row
discharges DIVINT/MODINT for programs that do divide by zero).
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

/-! ## Divisors are nonzero

`DIVINT`/`MODINT` by zero raise `Division_by_zero` through the C runtime
(`caml_raise_zero_divide`). `DivisorsNonzero P` states that a program never
divides by zero, so that path is unreachable. -/

/-- The per-state check: at a division, the divisor (stack top) is not zero. -/
def St.divisorsOk (P : Prog) (s : St) : Bool :=
  if s.atOp P .DIVINT ∨ s.atOp P .MODINT then s.stack.head? != some (.int 0) else true

/-- **No reachable division has a zero divisor.** -/
structure DivisorsNonzero (P : Prog) : Prop where
  nonzero : ∀ s, Reach P s → s.atOp P .DIVINT ∨ s.atOp P .MODINT → ∀ rest, s.stack ≠ .int 0 :: rest

theorem DivisorsNonzero.of_check {P : Prog} (h : ∀ s, Reach P s → s.divisorsOk P = true) :
    DivisorsNonzero P where
  nonzero s reach at_ rest stack := by
    have := h s reach
    simp [St.divisorsOk, if_pos at_, stack] at this

end OCaml.Bytecode
