import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.PtrOffsets
import OCaml.Vm.Sim.RaiseRows
import OCaml.Vm.Sim.ClosureAllocRows
import OCaml.Vm.Sim.MakeblockNRows
import OCaml.RefinementF1
import OCaml.Programs.Validation

/-!
# The F1 shape facts of `whileMin`, kernel-checked by one run

One `decide +kernel` of `Run.checkAll` over the 2,161-step run checks, at
every state, the per-program facts the F1 table still takes: the decoded
instruction is F1, STOP returns no raw word, and its opcode is one of the
program's (`St.decodedOk`: `GoodF1` and the reached opcodes of the table), no
zero divisor, the C_CALL results and names, `Fits` and `NoForward`. The
former shape facts (values in range, extra counts, the trap pointer, BEQ on
integers) are BcSem's use-site guards, read off each row's step. One combined run, not one
per fact: each run of the kernel costs several GB.
-/

namespace OCaml.Vm.Sim
open OCaml.Bytecode

/-- The decode check: an F1 instruction (`GoodF1.inF1`), STOP returns no raw word
(`GoodF1.stopAccu`), and its opcode is among `ops` (the rows the table needs). -/
def St.decodedOk (P : Prog) (ops : List Opcode) (s : St) : Bool :=
  match decodeAt P.code s.pc with
  | some i => decide (OCaml.InF1 P i) && OCaml.stopOrdinary i s.accu && ops.contains i.op
  | none => false

/-- The per-state operand check: at opcode `op`, the operand word after it
is at most `bound` (closure capture counts, block sizes). -/
def St.operandOk (P : Prog) (op : Opcode) (bound : Nat) (s : St) : Bool :=
  if s.atOp P op then
    match P.code[s.pc + 1]? with
    | some w => decide (w.toInt.toNat ≤ bound)
    | none => true
  else true

theorem St.operandOk_bound {P : Prog} {op : Opcode} {bound : Nat} {s : St} {w : BitVec 32}
    (ok : St.operandOk P op bound s = true) (code : DispatchCode P s op)
    (fetch : P.code[s.pc + 1]? = some w) : w.toInt.toNat ≤ bound := by
  have at_ : s.atOp P op := code.fetch
  simp only [St.operandOk, if_pos at_, fetch, decide_eq_true_eq] at ok
  exact ok

/-- A primitive result that returns normally. -/
def _root_.OCaml.Bytecode.PRes.isOk : PRes → Bool
  | .ok .. => true
  | _ => false

theorem _root_.OCaml.Bytecode.PRes.isOk_ok {r : PRes} (h : r.isOk = true) : ∃ v heap world, r = .ok v heap world := by
  cases r <;> simp_all [PRes.isOk]

/-- The per-state C_CALL check: at `op` (`C_CALLk`, `k` stack arguments)
naming an F1 primitive, the primitive returns normally on the actual
arguments. -/
def St.ccallOk (P : Prog) (op : Opcode) (k : Nat) (s : St) : Bool :=
  if s.atOp P op then
    match P.code[s.pc + 1]? with
    | some w =>
      if 0 ≤ w.toInt then
        match P.prims[w.toInt.toNat]? with
        | some name =>
          if name ∈ primsF1 then (primF1Impl name (s.accu :: s.stack.take k) s.heap s.world).isOk else true
        | none => true
      else true
    | none => true
  else true

theorem St.ccallOk_ok {P : Prog} {op : Opcode} {k : Nat} {s : St} {w : BitVec 32} {name : String}
    (ok : St.ccallOk P op k s = true) (code : DispatchCode P s op) (fetch : P.code[s.pc + 1]? = some w)
    (nonnegative : 0 ≤ w.toInt) (hp : P.prims[w.toInt.toNat]? = some name) (member : name ∈ primsF1) :
    ∃ v heap world, primF1Impl name (s.accu :: s.stack.take k) s.heap s.world = .ok v heap world := by
  have at_ : s.atOp P op := code.fetch
  simp only [St.ccallOk, if_pos at_, fetch, if_pos nonnegative, hp, if_pos member] at ok
  exact PRes.isOk_ok ok

/-- At a `C_CALL op` site the named primitive is one of `names`. -/
def St.namesOk (P : Prog) (names : List String) (op : Opcode) (s : St) : Bool :=
  if s.atOp P op then
    match P.code[s.pc + 1]? with
    | some w => match P.prims[w.toInt.toNat]? with
      | some name => names.contains name
      | none => true
    | none => true
  else true

/-- Every `C_CALLk` site names one of `names .C_CALLk` (`CcallReturns.of_names`). -/
def St.callNamesOk (P : Prog) (names : Opcode → List String) (s : St) : Bool :=
  St.namesOk P (names .C_CALL1) .C_CALL1 s && St.namesOk P (names .C_CALL2) .C_CALL2 s &&
    St.namesOk P (names .C_CALL3) .C_CALL3 s && St.namesOk P (names .C_CALL4) .C_CALL4 s &&
    St.namesOk P (names .C_CALL5) .C_CALL5 s

/-- All F1 shape checks at one state. -/
def St.shapeOk (P : Prog) (ops : List Opcode) (names : Opcode → List String) (s : St) : Bool :=
  St.decodedOk P ops s && s.divisorsOk P && St.operandOk P .CLOSURE 254 s &&
    St.operandOk P .MAKEBLOCK 256 s && St.ccallOk P .C_CALL1 0 s && St.ccallOk P .C_CALL2 1 s &&
    St.ccallOk P .C_CALL3 2 s && St.ccallOk P .C_CALL4 3 s && St.ccallOk P .C_CALL5 4 s &&
    s.heap.noForward &&
    decide (s.stack.length ≤ Vm.Gc.g1Budget.stackWords ∧ s.heap.words ≤ Vm.Gc.g1Budget.heapWords) &&
    St.callNamesOk P names s

/-- The F1 shape checks of one state, by name. -/
structure ShapeFacts (P : Prog) (ops : List Opcode) (names : Opcode → List String) (s : St) : Prop where
  decoded : St.decodedOk P ops s = true
  divisors : s.divisorsOk P = true
  closures : St.operandOk P .CLOSURE 254 s = true
  blocks : St.operandOk P .MAKEBLOCK 256 s = true
  ccall1 : St.ccallOk P .C_CALL1 0 s = true
  ccall2 : St.ccallOk P .C_CALL2 1 s = true
  ccall3 : St.ccallOk P .C_CALL3 2 s = true
  ccall4 : St.ccallOk P .C_CALL4 3 s = true
  ccall5 : St.ccallOk P .C_CALL5 4 s = true
  /-- no `Forward_tag` block (a6-gc: `gcSafe_of_noForward`) -/
  noForward : s.heap.noForward = true
  /-- within the F1 budget (a6-gc: `Fits g1Budget`) -/
  fits : s.stack.length ≤ Vm.Gc.g1Budget.stackWords ∧ s.heap.words ≤ Vm.Gc.g1Budget.heapWords
  callNames : St.callNamesOk P names s = true

theorem ShapeFacts.of_ok {P : Prog} {ops : List Opcode} {names : Opcode → List String} {s : St}
    (h : St.shapeOk P ops names s = true) : ShapeFacts P ops names s := by
  simp only [St.shapeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨decoded, divisors⟩, closures⟩, blocks⟩,
    c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, noForward⟩, fits⟩, callNames⟩ := h
  exact ⟨decoded, divisors, closures, blocks, c1, c2, c3, c4, c5, noForward, fits, callNames⟩

/-- The decode check, by name. -/
theorem ShapeFacts.decode {P : Prog} {ops : List Opcode} {names : Opcode → List String} {s : St}
    (h : ShapeFacts P ops names s) :
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

/-- The primitives `while_min.byte`'s calls name, per call opcode (checked in
`whileMin_shapeChecked`). -/
def whileMinCalls : Opcode → List String
  | .C_CALL1 => ["caml_fresh_oo_id", "caml_ml_open_descriptor_out", "caml_ml_string_length", "caml_ml_flush"]
  | .C_CALL2 => ["caml_format_int", "caml_ml_output_char"]
  | .C_CALL4 => ["caml_ml_output"]
  | _ => []

set_option maxRecDepth 100000 in
theorem whileMin_shapeChecked :
    Run.checkAll (bcK whileMin) (St.shapeOk whileMin whileMinOps whileMinCalls) 2200 whileMin.init = true := by
  decide +kernel

theorem whileMin_shapeOk {s : St} (reach : Reach whileMin s) : ShapeFacts whileMin whileMinOps whileMinCalls s :=
  .of_ok (reach_of_checkAll whileMin_shapeChecked reach)

/-- **`Fits g1Budget whileMin`** (peak 18 stack / 125 heap words). -/
theorem whileMin_fits : Fits Vm.Gc.g1Budget whileMin := fun _ reach => (whileMin_shapeOk reach).fits

/-- `whileMin` never creates a `Forward_tag` block. -/
theorem whileMin_noForward : NoForward whileMin := fun _ reach => (whileMin_shapeOk reach).noForward

/-- **`GcSafe whileMin`**. -/
theorem whileMin_gcSafe : GcSafe whileMin := gcSafe_of_noForward whileMin_noForward

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

/-- **`whileMin`'s C_CALL1 primitives return normally.** -/
theorem whileMin_ccall1Ok : ∀ s (w : BitVec 32) name, Reach whileMin s → DispatchCode whileMin s .C_CALL1 →
    whileMin.code[s.pc + 1]? = some w → 0 ≤ w.toInt → whileMin.prims[w.toInt.toNat]? = some name →
    name ∈ primsF1 →
    ∃ v heap world, primF1Impl name (s.accu :: s.stack.take 0) s.heap s.world = .ok v heap world :=
  fun _ _ _ reach code fetch nonnegative hp member =>
    St.ccallOk_ok (whileMin_shapeOk reach).ccall1 code fetch nonnegative hp member

/-- **`whileMin`'s C_CALL2 primitives return normally.** -/
theorem whileMin_ccall2Ok : ∀ s (w : BitVec 32) name, Reach whileMin s → DispatchCode whileMin s .C_CALL2 →
    whileMin.code[s.pc + 1]? = some w → 0 ≤ w.toInt → whileMin.prims[w.toInt.toNat]? = some name →
    name ∈ primsF1 →
    ∃ v heap world, primF1Impl name (s.accu :: s.stack.take 1) s.heap s.world = .ok v heap world :=
  fun _ _ _ reach code fetch nonnegative hp member =>
    St.ccallOk_ok (whileMin_shapeOk reach).ccall2 code fetch nonnegative hp member

/-- **`whileMin`'s C_CALL3 primitives return normally.** -/
theorem whileMin_ccall3Ok : ∀ s (w : BitVec 32) name, Reach whileMin s → DispatchCode whileMin s .C_CALL3 →
    whileMin.code[s.pc + 1]? = some w → 0 ≤ w.toInt → whileMin.prims[w.toInt.toNat]? = some name →
    name ∈ primsF1 →
    ∃ v heap world, primF1Impl name (s.accu :: s.stack.take 2) s.heap s.world = .ok v heap world :=
  fun _ _ _ reach code fetch nonnegative hp member =>
    St.ccallOk_ok (whileMin_shapeOk reach).ccall3 code fetch nonnegative hp member

/-- **`whileMin`'s C_CALL4 primitives return normally.** -/
theorem whileMin_ccall4Ok : ∀ s (w : BitVec 32) name, Reach whileMin s → DispatchCode whileMin s .C_CALL4 →
    whileMin.code[s.pc + 1]? = some w → 0 ≤ w.toInt → whileMin.prims[w.toInt.toNat]? = some name →
    name ∈ primsF1 →
    ∃ v heap world, primF1Impl name (s.accu :: s.stack.take 3) s.heap s.world = .ok v heap world :=
  fun _ _ _ reach code fetch nonnegative hp member =>
    St.ccallOk_ok (whileMin_shapeOk reach).ccall4 code fetch nonnegative hp member

/-- **`whileMin`'s C_CALL5 primitives return normally.** -/
theorem whileMin_ccall5Ok : ∀ s (w : BitVec 32) name, Reach whileMin s → DispatchCode whileMin s .C_CALL5 →
    whileMin.code[s.pc + 1]? = some w → 0 ≤ w.toInt → whileMin.prims[w.toInt.toNat]? = some name →
    name ∈ primsF1 →
    ∃ v heap world, primF1Impl name (s.accu :: s.stack.take 4) s.heap s.world = .ok v heap world :=
  fun _ _ _ reach code fetch nonnegative hp member =>
    St.ccallOk_ok (whileMin_shapeOk reach).ccall5 code fetch nonnegative hp member

end OCaml.Programs
