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
(`OCaml/Programs/WhileMinOffsets.lean`); a general discharge (bounds checks in
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

end OCaml.Bytecode
