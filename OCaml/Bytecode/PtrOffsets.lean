import OCaml.Bytecode.Semantics

/-!
# Pointer offsets stay within their blocks

`.ptr l k` addresses field `k` of block `l`. Physical equality (`EQ`, `NEQ`,
`BEQ`, `BNEQ`) compares `(l, k)`, while the machine compares the words
`φ l + 8k`; the two agree when every compared pointer stays within its block
(`k ≤ wosize`, one past the end allowed), because the heap representation
separates distinct blocks by at least a header word. Infix pointers
(`CLOSUREREC`) satisfy this by construction; `OFFSETCLOSURE` adds a signed
operand, so in general it is a property of the program.

`PtrsInBlock P` states it for every reachable accumulator and stack value.
A concrete program discharges it by one checked run
(`OCaml/Programs/WhileMinOffsets.lean`); the general discharge (a bounds
check on `OFFSETCLOSURE` in `BcSem` plus a preservation proof) is open
(a2-sem).
-/

namespace OCaml.Bytecode

/-- A pointer addresses a field of an existing block, or one past its end;
other values are unconstrained. -/
def Val.inBlock (h : Heap) : Val → Bool
  | .ptr l k => match h.get? l with
    | some o => decide (k ≤ o.wosize)
    | none => false
  | _ => true

/-- The accumulator and every stack value point within their blocks. -/
def St.ptrsInBlock (s : St) : Bool :=
  s.accu.inBlock s.heap && s.stack.all (Val.inBlock s.heap)

/-- **Every reachable accumulator and stack pointer is within its block.** -/
def PtrsInBlock (P : Prog) : Prop := ∀ s, Reach P s → s.ptrsInBlock = true

/-- Destructuring: the accumulator. -/
theorem PtrsInBlock.accu {P : Prog} (h : PtrsInBlock P) {s : St} (reach : Reach P s) :
    s.accu.inBlock s.heap = true := by
  have := h s reach
  simp only [St.ptrsInBlock, Bool.and_eq_true] at this
  exact this.1

/-- Destructuring: a stack value. -/
theorem PtrsInBlock.stack {P : Prog} (h : PtrsInBlock P) {s : St} (reach : Reach P s)
    {v : Val} (mem : v ∈ s.stack) : v.inBlock s.heap = true := by
  have := h s reach
  simp only [St.ptrsInBlock, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2 v mem

/-- A within-block pointer: its block exists and the offset is at most its size. -/
theorem Val.inBlock_ptr {h : Heap} {l k : Nat} (hb : (Val.ptr l k).inBlock h = true) :
    ∃ o, h.get? l = some o ∧ k ≤ o.wosize := by
  simp only [Val.inBlock] at hb
  split at hb
  · rename_i o ho; exact ⟨o, ho, of_decide_eq_true hb⟩
  · cases hb

end OCaml.Bytecode
