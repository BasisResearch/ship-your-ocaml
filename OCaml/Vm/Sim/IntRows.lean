import OCaml.Vm.Sim.InvariantUse
import OCaml.Vm.Sim.ComparisonArithmetic
import OCaml.Vm.Sim.Mulint
import OCaml.Vm.Sim.Division
import OCaml.Vm.Sim.Eq
import OCaml.Vm.Sim.Neq
import OCaml.Vm.Sim.WordPlace
import OCaml.Vm.Sim.Addint
import OCaml.Vm.Sim.Subint
import OCaml.Vm.Sim.Andint
import OCaml.Vm.Sim.Orint
import OCaml.Vm.Sim.Xorint
import OCaml.Vm.Sim.Lslint
import OCaml.Vm.Sim.Lsrint
import OCaml.Vm.Sim.Asrint
import OCaml.Vm.Sim.Ltint
import OCaml.Vm.Sim.Leint
import OCaml.Vm.Sim.Gtint
import OCaml.Vm.Sim.Geint
import OCaml.Vm.Sim.Ultint
import OCaml.Vm.Sim.Ugeint

/-!
# Unconditional rows: integer binary operations and comparisons

The fourteen opcodes whose arm consumes the top stack word
(`intOp`/`cmpOp`). One combinator, `top_read_row`, derives every premise of
their conditional bridges from the loop-head invariant: `ArmInput` by
`ArmInput.of_loop`, and the top-of-stack read window from
`StackGeometry.read` under the stack budget. Each row instantiates it with
the family's `*_step_arm`. `DispatchCode` (code geometry and fetch) is the
`CodeFacts` interface.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

theorem intOp_nonempty {s s' : St} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (step : intOp s f = .next s') : 0 < s.stack.length := by
  obtain ⟨_, _, _, _, stack, _⟩ := intOp_next step
  simp [stack]

theorem cmpOp_nonempty {s s' : St} {f : BitVec 64 → BitVec 64 → Bool}
    (step : cmpOp s f = .next s') : 0 < s.stack.length := by
  obtain ⟨_, _, _, _, stack, _⟩ := cmpOp_next step
  simp [stack]

theorem intOp_no_halt {s : St} {f : BitVec 64 → BitVec 64 → BitVec 64} {e : Nat} {w : World} :
    intOp s f ≠ .halt e w := by
  unfold intOp; split
  · cases ints? _ _ <;> simp [opt]
  · nofun

theorem cmpOp_no_halt {s : St} {f : BitVec 64 → BitVec 64 → Bool} {e : Nat} {w : World} :
    cmpOp s f ≠ .halt e w := by
  unfold cmpOp; split
  · cases ints? _ _ <;> simp [opt]
  · nofun

theorem brOp_no_halt {s : St} {n ofs : Int} {f : BitVec 64 → BitVec 64 → Bool} {e : Nat} {w : World} :
    brOp s n ofs f ≠ .halt e w := by
  unfold brOp; split
  · split
    · cases target s.pc 1 ofs <;> simp [opt]
    · nofun
  · nofun

theorem raiseTo_no_halt {P : Prog} {s : St} {x : Val} {e : Nat} {w : World} :
    raiseTo P s x ≠ .halt e w := by
  intro h; simp only [raiseTo] at h; repeat' split at h
  all_goals cases h

theorem division_no_halt (kind : DivisionKind) {P : Prog} {s : St} {e : Nat} {w : World} :
    stepI P s ⟨divisionOpcode kind, []⟩ ≠ .halt e w := by
  intro h
  cases kind <;> simp only [stepI, divisionOpcode, opt] at h <;> (repeat' split at h) <;>
    first | exact raiseTo_no_halt h | cases h

/-- **A top-of-stack-reading row.** From the loop head, the dispatch code
facts and the stack budget, an arm that needs only `ArmInput` and the read
window of the top stack word is simulated. -/
theorem top_read_row {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (nonempty : 0 < s.stack.length)
    (arm : ∀ {pl : Place} {cp : ChanPlace} {sp high : Nat}, ArmInput L P s op c pl cp sp high →
      ReadWindow (BitVec.ofNat 64 sp) 8 → ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨c', run, running⟩ :=
    arm input ((input.geometry.read input.stack (stack_space input.stack space) nonempty).window)
  exact ⟨c', run, h.of_plus run running⟩

/-- **ADDINT from the loop head.** -/
theorem addint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ADDINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.ADDINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => a + b - 1) step)
    fun input read => addint_step_arm stable input read step

/-- **SUBINT from the loop head.** -/
theorem subint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .SUBINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.SUBINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => a - b + 1) step)
    fun input read => subint_step_arm stable input read step

/-- **ANDINT from the loop head.** -/
theorem andint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ANDINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.ANDINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => a &&& b) step)
    fun input read => andint_step_arm stable input read step

/-- **ORINT from the loop head.** -/
theorem orint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ORINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.ORINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => a ||| b) step)
    fun input read => orint_step_arm stable input read step

/-- **XORINT from the loop head.** -/
theorem xorint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .XORINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.XORINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => (a ^^^ b) ||| 1) step)
    fun input read => xorint_step_arm stable input read step

/-- **LSLINT from the loop head.** -/
theorem lslint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .LSLINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.LSLINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => ((a - 1) <<< ((untag b).toNat % 64)) + 1) step)
    fun input read => lslint_step_arm stable input read step

/-- **LSRINT from the loop head.** -/
theorem lsrint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .LSRINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.LSRINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => (a >>> ((untag b).toNat % 64)) ||| 1) step)
    fun input read => lsrint_step_arm stable input read step

/-- **ASRINT from the loop head.** -/
theorem asrint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ASRINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.ASRINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => (a.sshiftRight ((untag b).toNat % 64)) ||| 1) step)
    fun input read => asrint_step_arm stable input read step

/-- **LTINT from the loop head.** -/
theorem ltint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .LTINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.LTINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (cmpOp_nonempty (f := fun a b => a.slt b) step)
    fun input read => ltint_step_arm stable input read step

/-- **LEINT from the loop head.** -/
theorem leint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .LEINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.LEINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (cmpOp_nonempty (f := fun a b => a.sle b) step)
    fun input read => leint_step_arm stable input read step

/-- **GTINT from the loop head.** -/
theorem gtint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .GTINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.GTINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (cmpOp_nonempty (f := fun a b => b.slt a) step)
    fun input read => gtint_step_arm stable input read step

/-- **GEINT from the loop head.** -/
theorem geint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .GEINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.GEINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (cmpOp_nonempty (f := fun a b => b.sle a) step)
    fun input read => geint_step_arm stable input read step

/-- **ULTINT from the loop head.** -/
theorem ultint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ULTINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.ULTINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (cmpOp_nonempty (f := fun a b => a.ult b) step)
    fun input read => ultint_step_arm stable input read step

/-- **UGEINT from the loop head.** -/
theorem ugeint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .UGEINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (step : stepI P s ⟨.UGEINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (cmpOp_nonempty (f := fun a b => b.ule a) step)
    fun input read => ugeint_step_arm stable input read step

/-- **MULINT from the loop head.** The libgcc call needs defined a2/a3
(`BinaryLibScratch`), which the loop-head invariant does not yet carry. -/
theorem mulint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .MULINT)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (scratch : BinaryLibScratch c)
    (step : stepI P s ⟨.MULINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (intOp_nonempty (f := fun a b => tag64 (untag a * untag b)) step)
    fun input read => mulint_step_arm stable input read scratch step

/-- A successful DIVINT/MODINT step has integer operands. -/
theorem division_operands (kind : DivisionKind) {P : Prog} {s s' : St}
    (step : stepI P s ⟨divisionOpcode kind, []⟩ = .next s') :
    ∃ x y rest, s.accu = .int x ∧ s.stack = .int y :: rest := by
  cases hs : s.stack with
  | nil => cases kind <;> simp [stepI, divisionOpcode, hs] at step
  | cons b rest =>
    cases ha : s.accu <;> cases b <;> cases kind <;>
      first
      | exact ⟨_, _, rest, rfl, rfl⟩
      | simp [stepI, divisionOpcode, hs, ha, ints?, opt] at step

/-- **DIVINT/MODINT from the loop head.** A nonzero divisor is the proved
libgcc arm (`division_step_arm`). A zero divisor raises `Division_by_zero`;
that row is the named premise `zero`, supplied by the zero-divisor arm
(caught: `division_zero_caught_step`, not yet in row form; uncaught: open). -/
theorem division_next (kind : DivisionKind) {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s (divisionOpcode kind))
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (scratch : BinaryLibScratch c)
    (zero : ∀ rest, s.stack = .int 0 :: rest → ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c')
    (step : stepI P s ⟨divisionOpcode kind, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨x, y, rest, accu, stack⟩ := division_operands kind step
  by_cases hy : y = 0
  · subst hy
    obtain ⟨c', run, running⟩ := zero rest stack
    exact ⟨c', run, h.of_plus run running⟩
  · exact top_read_row h code space (by simp [stack])
      fun input read => division_step_arm kind stable input accu stack hy read scratch step

/-- The EQ/NEQ operands: physical equality reflects word equality for the
accumulator and the top of stack, given that the state's live values lie in
their regions (`ValuesInRange`, per program). -/
theorem top_equality {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} (input : ArmInput L P s op c pl cp sp high)
    (ranged : s.valuesInRange P.code.size = true) :
    ∀ b, s.stack[0]? = some b → WordEquality pl s.accu b := by
  intro b top
  simp only [St.valuesInRange, Bool.and_eq_true, List.all_eq_true] at ranged
  have mem : b ∈ s.stack := List.mem_of_getElem? top
  exact WordEquality.of_place input.toVmReprAt input.geometry (by simp [roots])
    (by simp [roots, mem]) ranged.1 (ranged.2 b mem)

theorem physOp_nonempty {P : Prog} {s s' : St} {op : Opcode} (eqop : op = .EQ ∨ op = .NEQ)
    (step : stepI P s ⟨op, []⟩ = .next s') : 0 < s.stack.length := by
  cases hs : s.stack with
  | nil => rcases eqop with rfl | rfl <;> simp [stepI, hs] at step
  | cons => simp

/-- **EQ from the loop head.** -/
theorem eq_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .EQ)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (ranged : s.valuesInRange P.code.size = true)
    (step : stepI P s ⟨.EQ, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (physOp_nonempty (by simp) step)
    fun input read => eq_step_arm stable input read (top_equality input ranged) step

/-- **NEQ from the loop head.** -/
theorem neq_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .NEQ)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) (ranged : s.valuesInRange P.code.size = true)
    (step : stepI P s ⟨.NEQ, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  top_read_row h code space (physOp_nonempty (by simp) step)
    fun input read => neq_step_arm stable input read (top_equality input ranged) step

end OCaml.Vm.Sim
