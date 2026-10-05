import OCaml.Vm.Sim.Getglobal
import OCaml.Vm.Sim.Pushgetglobal
import OCaml.Vm.Sim.Getglobalfield
import OCaml.Vm.Sim.Pushgetglobalfield
import OCaml.Vm.Sim.StackRows

/-!
# Loop-head simulations of the global reads

GETGLOBAL, PUSHGETGLOBAL, GETGLOBALFIELD and PUSHGETGLOBALFIELD from
`LoopAt`: the global data block is a root, the second selection's source is
reachable from it, operands come from their fetches, read windows from the
object placement, pushes from the budget and the runtime-framing contract.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A successful field selection from a reachable value has a placement witness. -/
theorem field_selection_reachable {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i : Nat} {source v : Val} (h : VmReprAt P s c pl cp sp high)
    (reachable : ∀ loc, source.loc? = some loc → Live s.heap (roots P s) loc)
    (selected : field? s.heap source i = some v) :
    ∃ l a k, FieldSelection s.heap pl source i v l a k := by
  cases source with
  | ptr l k =>
    obtain ⟨a, o, placed, _, _⟩ := h.heap.1 l (reachable l rfl)
    exact ⟨l, a, k, rfl, placed, selected⟩
  | int n => simp [field?] at selected
  | atom t => simp [field?] at selected
  | code pc => simp [field?] at selected
  | raw w => simp [field?] at selected

/-- **GETGLOBAL n from the loop head.** -/
theorem getglobal_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .GETGLOBAL)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (step : stepI P s ⟨.GETGLOBAL, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (field? s.heap P.globals w.toInt.toNat)
    (fun v => .next { (s.adv 2) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt (by simp [roots]) selected
  obtain ⟨c', run, running⟩ := getglobal_arm stable input (OperandAt.of_fetch input.geometry fetch)
    nonnegative sel (input.geometry.field_read sel)
  exact ⟨c', run, h.of_plus run running⟩

/-- **PUSHGETGLOBAL n from the loop head.** -/
theorem pushgetglobal_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 : Nat} (rf : RuntimeFrame L high0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHGETGLOBAL)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHGETGLOBAL, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (field? s.heap P.globals w.toInt.toNat)
    (fun v => .next { (pushAccu (s.adv 2)) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨x, -, pushed⟩ := input.accu
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt (by simp [roots]) selected
  obtain ⟨c', run, running⟩ := pushgetglobal_arm (by simpa only [Nat.mul_one] using rf.push input space)
    input (PushWriteOk.of_geometry input.geometry input.stack space)
    (OperandAt.of_fetch input.geometry fetch) sel (input.geometry.field_read sel) nonnegative pushed
  exact ⟨c', run, h.of_plus run running⟩

/-- **GETGLOBALFIELD n k from the loop head.** -/
theorem getglobalfield_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {n m : BitVec 32} (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .GETGLOBALFIELD)
    (fetchN : P.code[s.pc + 1]? = some n) (fetchM : P.code[s.pc + 2]? = some m)
    (nonnegativeN : 0 ≤ n.toInt) (nonnegativeM : 0 ≤ m.toInt)
    (step : stepI P s ⟨.GETGLOBALFIELD, [n.toInt, m.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (field? s.heap P.globals n.toInt.toNat) (fun g =>
    opt (field? s.heap g m.toInt.toNat) fun v => .next { (s.adv 3) with accu := v }) = .next s' at step
  obtain ⟨mid, firstSel, rest⟩ := opt_next step
  obtain ⟨v, secondSel, next⟩ := opt_next rest
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, first⟩ := field_selection input.toVmReprAt (by simp [roots]) firstSel
  obtain ⟨loc, b, j, second⟩ := field_selection_reachable input.toVmReprAt
    (first.read input.toVmReprAt (by simp [roots])).root secondSel
  obtain ⟨c', run, running⟩ := getglobalfield_arm stable input
    (OperandAt.of_fetch input.geometry fetchN) (OperandAt.of_fetch input.geometry fetchM)
    nonnegativeN nonnegativeM first second (input.geometry.field_read first)
    (input.geometry.field_read second)
  exact ⟨c', run, h.of_plus run running⟩

/-- **PUSHGETGLOBALFIELD n k from the loop head.** -/
theorem pushgetglobalfield_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {n m : BitVec 32} {high0 : Nat} (rf : RuntimeFrame L high0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHGETGLOBALFIELD)
    (fetchN : P.code[s.pc + 1]? = some n) (fetchM : P.code[s.pc + 2]? = some m)
    (nonnegativeN : 0 ≤ n.toInt) (nonnegativeM : 0 ≤ m.toInt)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHGETGLOBALFIELD, [n.toInt, m.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (field? s.heap P.globals n.toInt.toNat) (fun g =>
    opt (field? s.heap g m.toInt.toNat) fun v =>
      .next { (pushAccu (s.adv 3)) with accu := v }) = .next s' at step
  obtain ⟨mid, firstSel, rest⟩ := opt_next step
  obtain ⟨v, secondSel, next⟩ := opt_next rest
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨x, -, pushed⟩ := input.accu
  obtain ⟨l, a, k, first⟩ := field_selection input.toVmReprAt (by simp [roots]) firstSel
  obtain ⟨loc, b, j, second⟩ := field_selection_reachable input.toVmReprAt
    (first.read input.toVmReprAt (by simp [roots])).root secondSel
  obtain ⟨c', run, running⟩ := pushgetglobalfield_arm
    (by simpa only [Nat.mul_one] using rf.push input space) input
    (PushWriteOk.of_geometry input.geometry input.stack space) pushed
    (OperandAt.of_fetch input.geometry fetchN) (OperandAt.of_fetch input.geometry fetchM)
    nonnegativeN nonnegativeM first second (input.geometry.field_read first)
    (input.geometry.field_read second)
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
