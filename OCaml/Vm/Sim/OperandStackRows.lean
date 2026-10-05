import OCaml.Vm.Sim.Acc
import OCaml.Vm.Sim.Pushacc
import OCaml.Vm.Sim.Pop
import OCaml.Vm.Sim.Envacc
import OCaml.Vm.Sim.Assign
import OCaml.Vm.Sim.StackRows

/-!
# Loop-head simulations of the operand stack/environment reads

`ACC n`, `PUSHACC n`, `POP n` and `ENVACC n` from `LoopAt`: the operand comes
from its fetch alone (`OperandAt.of_fetch`, geometry from the witness), the
read windows from the placement geometry, the push from
`PushWriteOk.of_geometry`/`RuntimeFrame.push`. `nonnegative` is named: BcSem
clamps a negative operand with `Int.toNat`, while `interp.c` indexes below
`sp` (a2-sem's BcSem domain).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A slot of the pushed stack, `sp - 8 + 8 * n` for `n ≤ length`, is readable. -/
theorem StackGeometry.push_read {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high n : Nat} (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes) (bound : n ≤ s.stack.length) :
    RamReadAt (sp - 8 + 8 * n) 8 := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_bss_end, Layout.sym_tohost] at * <;> omega

/-- **ACC n from the loop head.** -/
theorem acc_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ACC)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : stepI P s ⟨.ACC, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (s.stack[w.toInt.toNat]?) (fun v => .next { (s.adv 2) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  obtain ⟨c', run, running⟩ := acc_arm stable input (OperandAt.of_fetch input.geometry fetch)
    nonnegative selected (input.geometry.read input.stack (stack_space input.stack space) bound)
  exact ⟨c', run, h.of_plus run running⟩

/-- **PUSHACC n from the loop head.** -/
theorem pushacc_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 : Nat} (rf : RuntimeFrame L high0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHACC)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHACC, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt ((s.accu :: s.stack)[w.toInt.toNat]?)
    (fun v => .next { (pushAccu (s.adv 2)) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨x, -, pushed⟩ := input.accu
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  simp only [List.length_cons] at bound
  obtain ⟨c', run, running⟩ := pushacc_arm (by simpa only [Nat.mul_one] using rf.push input space)
    input (PushWriteOk.of_geometry input.geometry input.stack space)
    (OperandAt.of_fetch input.geometry fetch) nonnegative selected
    (input.geometry.push_read input.stack space (by omega)) pushed
  exact ⟨c', run, h.of_plus run running⟩

/-- **POP n from the loop head.** -/
theorem pop_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .POP)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (step : stepI P s ⟨.POP, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨c', run, running⟩ := pop_step_arm stable input (OperandAt.of_fetch input.geometry fetch)
    nonnegative step
  exact ⟨c', run, h.of_plus run running⟩

/-- **ENVACC n from the loop head.** -/
theorem envacc_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ENVACC)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (step : stepI P s ⟨.ENVACC, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (field? s.heap s.env w.toInt.toNat)
    (fun v => .next { (s.adv 2) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt (by simp [roots]) selected
  obtain ⟨c', run, running⟩ := envacc_arm stable input (OperandAt.of_fetch input.geometry fetch)
    nonnegative sel (input.geometry.field_read sel)
  exact ⟨c', run, h.of_plus run running⟩

/-- A static range (below `.bss`'s end) is apart from the stack allocation. -/
theorem stackWindow_static {high a n : Nat} (g : Layout.sym_bss_end + Layout.stackBytes ≤ high)
    (static : a + n ≤ Layout.sym_bss_end) : OutWRange [stackWindow high] a n :=
  ⟨Or.inl (by simp only [stackWindow]; omega), trivial⟩

/-- **In-place stack edits are separated from the rest of the payload**: any
write inside the stack allocation misses everything but the stack. -/
theorem StackGeometry.edit {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (inside : LogInW [stackWindow high] log) : StackEditOutside log P s c pl cp high := by
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 :=
    fun a ha => outLRange_of_windows inside (stackWindow_static g.statics ha)
  have domainField : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := by
    intro off hoff
    apply outLRange_of_windows inside
    have hd := g.domain.1
    exact ⟨by simp only [stackWindow] at hd ⊢; omega, trivial⟩
  have objects : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → ObjectOutside log a o := by
    intro l a o placed object
    have ho := (g.heap l a o placed object).1
    refine ⟨outLRange_of_windows inside ⟨?_, trivial⟩, outLRange_of_windows inside ⟨?_, trivial⟩⟩
    · simp only [stackWindow] at ho ⊢; omega
    · simp only [stackWindow] at ho ⊢; omega
  refine ⟨⟨static _ (by decide), domainField _ (by decide), domainField _ (by decide),
    static _ (by decide), static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun i w hw => outLRange_of_windows inside (g.code i w hw)
  · intro i v hv
    cases hv
  · exact fun l a o _ placed object => objects l a o placed object
  · exact fun id ch a hch hcp => outLRange_of_windows inside (g.channels id ch a hch hcp)
  · exact fun l a o _ placed object => objects l a o placed object

/-- A stack slot write is runtime-stable, writable and separated. -/
theorem AssignWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i : Nat} {w : BitVec 64} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (bound : i < s.stack.length) : AssignWriteOk P s c pl cp sp high i w := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have ha := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have inside : LogInW [stackWindow high] (assignLog sp i w) := by
    simp only [assignLog, stackWindow, LogInW, InsideW, or_false, and_true]
    omega
  have hn : (BitVec.ofNat 64 (sp + 8 * i)).toNat = sp + 8 * i := Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, g.edit inside, ?_, ?_⟩
  all_goals first
    | (rw [hn]; simp only [Layout.sym_tohost, Layout.sym_bss_end] at *; omega)
    | skip
  · exact ⟨outLRange_of_windows inside (stackWindow_static g.statics (by decide)),
      outLRange_of_windows inside (stackWindow_static g.statics (by decide))⟩
  · exact ⟨outLRange_of_windows inside (stackWindow_static g.statics (by decide)),
      fun j name hj => outLRange_of_windows inside (g.primitives j name hj)⟩

/-- **ASSIGN n from the loop head.** -/
theorem assign_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 : Nat} (rf : RuntimeFrame L high0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .ASSIGN)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : stepI P s ⟨.ASSIGN, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have bound : w.toInt.toNat < s.stack.length := by
    by_cases inside : w.toInt.toNat < s.stack.length
    · exact inside
    · have : stepI P s ⟨.ASSIGN, [w.toInt]⟩ = .wrong := by simp [stepI, inside]
      rw [this] at step
      cases step
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨x, -, value⟩ := input.accu
  have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
  have hs := input.stack.1
  obtain ⟨c', run, running⟩ := assign_step_arm
    (rf.stackWindow _ _ (by rw [← same]; omega) (by rw [← same]; omega)) input
    (OperandAt.of_fetch input.geometry fetch) nonnegative
    (AssignWriteOk.of_geometry input.geometry input.stack space bound) value step
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
