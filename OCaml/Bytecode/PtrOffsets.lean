import OCaml.Bytecode.Semantics

/-!
# Live values stay in their regions

Physical equality (`EQ`, `NEQ`, `BEQ`, `BNEQ`) compares values, while the
machine compares their words. The two agree when every compared value's word
lies in its own region: a pointer at a field of its block (`k < wosize`), a
code value inside the code buffer (`pc < code size`), an atom inside the atom
table (`t < 256`), and no raw word (`CLOSUREREC`'s infix headers are block
fields, never loaded by compiled code; `ISINT`/`BRANCHIF` decide by the
represented word's parity, which a raw word does not have). The regions are
pairwise apart in the placement (`StackGeometry`), so distinct values have
distinct words (`WordEquality.of_place`).

`ValuesInRange P` states it for every reachable accumulator and stack value.
A concrete program discharges it by one checked run
(`OCaml/Programs/WhileMinShape.lean`); a general discharge (bounds checks in
`OFFSETCLOSURE`, `CLOSURE` targets and `ATOM` plus a preservation proof) is
open (a2-sem).
-/

namespace OCaml.Bytecode

/-- A value's word lies in its region (`n` is the code size). -/
def Val.inRange (n : Nat) (h : Heap) : Val → Bool
  | .ptr l k => match h.get? l with
    | some o => decide (k < o.wosize)
    | none => false
  | .code pc => decide (pc < n)
  | .atom t => decide (t < 256)
  | .raw _ => false
  | .int _ => true

/-- The accumulator and every stack value lie in their regions. -/
def St.valuesInRange (n : Nat) (s : St) : Bool :=
  s.accu.inRange n s.heap && s.stack.all (Val.inRange n s.heap)

/-- **Every reachable accumulator and stack value lies in its region.** -/
def ValuesInRange (P : Prog) : Prop := ∀ s, Reach P s → s.valuesInRange P.code.size = true

/-- Destructuring: the accumulator. -/
theorem ValuesInRange.accu {P : Prog} (h : ValuesInRange P) {s : St} (reach : Reach P s) :
    s.accu.inRange P.code.size s.heap = true := by
  have := h s reach
  simp only [St.valuesInRange, Bool.and_eq_true] at this
  exact this.1

/-- Destructuring: a stack value. -/
theorem ValuesInRange.stack {P : Prog} (h : ValuesInRange P) {s : St} (reach : Reach P s)
    {v : Val} (mem : v ∈ s.stack) : v.inRange P.code.size s.heap = true := by
  have := h s reach
  simp only [St.valuesInRange, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2 v mem

/-- An in-range value is not a raw word. -/
theorem Val.inRange_notRaw {n : Nat} {h : Heap} {v : Val} (hb : v.inRange n h = true)
    (w : BitVec 64) : v ≠ .raw w := by
  rintro rfl; simp [Val.inRange] at hb

/-- Destructuring: the accumulator is not a raw word. -/
theorem ValuesInRange.accu_notRaw {P : Prog} (h : ValuesInRange P) {s : St} (reach : Reach P s) :
    ∀ w, s.accu ≠ .raw w :=
  Val.inRange_notRaw (h.accu reach)

/-! ## Immediate branches see integers

`BEQ`/`BNEQ` compare an immediate with `Long_val(accu)`; on a pointer the
native comparison depends on its address (`beq_pointer_guard_obstruction`).
Compiled code emits them only on integers; `BranchInts P` states it. -/

/-- The opcode word at the PC is `op`. -/
def St.atOp (P : Prog) (s : St) (op : Opcode) : Prop :=
  P.code[s.pc]? = some (BitVec.ofNat 32 op.toNat)

instance (P : Prog) (s : St) (op : Opcode) : Decidable (s.atOp P op) := by
  unfold St.atOp; infer_instance

/-- The per-state check. -/
def St.branchIntsOk (P : Prog) (s : St) : Bool :=
  if s.atOp P .BEQ ∨ s.atOp P .BNEQ then s.accu.isInt else true

/-- **Every reachable `BEQ`/`BNEQ` sees an integer accumulator.** -/
structure BranchInts (P : Prog) : Prop where
  integer : ∀ s, Reach P s → s.atOp P .BEQ ∨ s.atOp P .BNEQ → s.accu.isInt = true

theorem BranchInts.of_check {P : Prog} (h : ∀ s, Reach P s → s.branchIntsOk P = true) :
    BranchInts P where
  integer s reach at_ := by
    have := h s reach
    simp only [St.branchIntsOk, if_pos at_] at this
    exact this

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
