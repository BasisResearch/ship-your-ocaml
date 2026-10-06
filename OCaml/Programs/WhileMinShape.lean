import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.PtrOffsets
import OCaml.Bytecode.ExtraBound
import OCaml.Bytecode.TrapBound
import OCaml.Vm.Sim.RaiseRows
import OCaml.RefinementF1
import OCaml.Programs.Validation

/-!
# The F1 shape facts of `whileMin`, kernel-checked by one run

One `decide +kernel` of `Run.checkAll` over the 2,161-step run checks, at
every state, the per-program reachability facts the F1 arms name: live values
in their regions (`ValuesInRange`), small extra counts (`ExtraBounded`), the
trap pointer inside the stack (`TrapBounded`), immediate branches on integers
(`BranchInts`), caught raises (`RaisesCaught`), and the decoded instruction is
F1, STOP returns no raw word, and its opcode is one of the program's
(`St.decodedOk`: `GoodF1` and the reached opcodes of the F1 table). One combined run, not one
per fact: each run of the kernel costs several GB.
-/

namespace OCaml.Vm.Sim
open OCaml.Bytecode

/-- The per-state raise check: at a raise opcode, a trap frame is installed. -/
def St.raisesOk (P : Prog) (s : St) : Bool :=
  if s.atOp P .RAISE ∨ s.atOp P .RERAISE ∨ s.atOp P .RAISE_NOTRACE then s.trap != 0 else true

theorem RaisesCaught.of_check {P : Prog} (h : ∀ s, Reach P s → St.raisesOk P s = true) :
    RaisesCaught P where
  caught s op reach member code := by
    have ok := h s reach
    have at_ : s.atOp P .RAISE ∨ s.atOp P .RERAISE ∨ s.atOp P .RAISE_NOTRACE := by
      simp only [raiseOps, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact .inl code.fetch
      · exact .inr (.inl code.fetch)
      · exact .inr (.inr code.fetch)
    simp only [St.raisesOk, if_pos at_, bne_iff_ne, ne_eq] at ok
    exact ok

/-- The decode check: an F1 instruction (`GoodF1.inF1`), STOP returns no raw word
(`GoodF1.stopAccu`), and its opcode is among `ops` (the rows the table needs). -/
def St.decodedOk (P : Prog) (ops : List Opcode) (s : St) : Bool :=
  match decodeAt P.code s.pc with
  | some i => decide (OCaml.InF1 P i) && OCaml.stopOrdinary i s.accu && ops.contains i.op
  | none => false

/-- All F1 shape checks at one state. -/
def St.shapeOk (P : Prog) (ops : List Opcode) (s : St) : Bool :=
  s.valuesInRange P.code.size && s.extraOk && s.trapOk && s.branchIntsOk P && St.raisesOk P s &&
    St.decodedOk P ops s && s.divisorsOk P

/-- The F1 shape checks of one state, by name. -/
structure ShapeFacts (P : Prog) (ops : List Opcode) (s : St) : Prop where
  values : s.valuesInRange P.code.size = true
  extra : s.extraOk = true
  trap : s.trapOk = true
  branches : s.branchIntsOk P = true
  raises : St.raisesOk P s = true
  decoded : St.decodedOk P ops s = true
  divisors : s.divisorsOk P = true

theorem ShapeFacts.of_ok {P : Prog} {ops : List Opcode} {s : St} (h : St.shapeOk P ops s = true) :
    ShapeFacts P ops s := by
  simp only [St.shapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨values, extra⟩, trap⟩, branches⟩, raises⟩, decoded⟩, divisors⟩ := h
  exact ⟨values, extra, trap, branches, raises, decoded, divisors⟩

/-- The decode check, by name. -/
theorem ShapeFacts.decode {P : Prog} {ops : List Opcode} {s : St} (h : ShapeFacts P ops s) :
    ∃ i, decodeAt P.code s.pc = some i ∧ OCaml.InF1 P i ∧ OCaml.stopOrdinary i s.accu = true ∧ i.op ∈ ops := by
  have d := h.decoded
  unfold St.decodedOk at d
  split at d
  · rename_i i hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at d
    exact ⟨i, hd, d.1.1, d.1.2, d.2⟩
  · simp at d

end OCaml.Vm.Sim

namespace OCaml.Programs
open OCaml.Bytecode OCaml.Vm.Sim

/-- The opcodes `while_min.byte` executes (checked in `whileMin_shapeChecked`). -/
def whileMinOps : List Opcode :=
  [.BRANCH, .CONST0, .C_CALL1, .PUSHGETGLOBAL, .MAKEBLOCK2, .PUSHCONST1, .PUSHACC0, .CLOSURE,
   .PUSHACC1, .PUSHCONST0, .PUSH, .ACC1, .BGTINT, .CHECK_SIGNALS, .OFFSETINT, .ASSIGN, .ADDINT,
   .ACC0, .PUSHACC4, .APPLY1, .C_CALL2, .PUSHACC2, .PUSHENVACC2, .C_CALL4, .RETURN, .PUSHACC3,
   .CONSTINT, .PUSHTRAP, .CONST1, .BRANCHIF, .ACC5, .PUSHCONSTINT, .LTINT, .BRANCHIFNOT, .CONST2,
   .PUSHACC6, .MODINT, .NEQ, .PUSHACC5, .ACC, .RAISE, .PUSHACC, .EQ, .POP, .BGEINT, .MULINT,
   .PUSHACC7, .MAKEBLOCK, .SETGLOBAL, .STOP]

set_option maxRecDepth 100000 in
theorem whileMin_shapeChecked :
    Run.checkAll (bcK whileMin) (St.shapeOk whileMin whileMinOps) 2200 whileMin.init = true := by
  decide +kernel

theorem whileMin_shapeOk {s : St} (reach : Reach whileMin s) : ShapeFacts whileMin whileMinOps s :=
  .of_ok (reach_of_checkAll whileMin_shapeChecked reach)

/-- **`whileMin`'s live values lie in their regions.** -/
theorem whileMin_valuesInRange : ValuesInRange whileMin := fun _ reach => (whileMin_shapeOk reach).values

/-- **`whileMin`'s extra-argument counts are bounded.** -/
theorem whileMin_extraBounded : ExtraBounded whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).extra

/-- **`whileMin`'s trap pointer stays inside the stack.** -/
theorem whileMin_trapBounded : TrapBounded whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).trap

/-- **`whileMin`'s immediate branches see integers.** -/
theorem whileMin_branchInts : BranchInts whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).branches

/-- **Every reachable raise in `whileMin` is caught.** -/
theorem whileMin_raisesCaught : RaisesCaught whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).raises

/-- **`while_min.byte` stays in F1**: `Good`, F1 instructions, STOP never raw. -/
theorem whileMin_goodF1 : OCaml.GoodF1 whileMin where
  good := whileMin_good
  inF1 s reach := let ⟨i, hd, hi, _⟩ := (whileMin_shapeOk reach).decode; ⟨i, hd, hi⟩
  stopAccu s i reach hd := by
    obtain ⟨j, hj, _, ho, _⟩ := (whileMin_shapeOk reach).decode
    rw [hd] at hj; cases hj; exact ho

/-- **`while_min.byte` only reaches `whileMinOps`.** -/
theorem whileMin_ops : ∀ s i, Reach whileMin s → decodeAt whileMin.code s.pc = some i →
    whileMinOps.contains i.op = true := by
  intro s i reach hd
  obtain ⟨j, hj, _, _, hm⟩ := (whileMin_shapeOk reach).decode
  rw [hd] at hj; cases hj
  exact List.contains_iff_mem.mpr hm

/-- **`whileMin` never divides by zero.** -/
theorem whileMin_divisorsNonzero : DivisorsNonzero whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).divisors

end OCaml.Programs
