import OCaml.Vm.Sim.DivisionZeroCaught
import OCaml.Vm.Sim.RaiseRows
import OCaml.Vm.Sim.IntRows

/-!
# The DIVINT/MODINT zero-divisor row (in progress)

A zero divisor raises `Division_by_zero` through the C runtime
(`caml_raise_zero_divide` → `caml_raise` → `longjmp` back into
`caml_interprete`); a1-arms' `division_zero_caught_step` is that native path
as a summary from the arm's zero branch, stated on the post-dispatch
configuration. This file derives its inputs from the loop head.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The dispatch target of DIVINT/MODINT is the zero-branch summary's entry. -/
theorem division_dispatch_entry (kind : DivisionKind) :
    BitVec.ofNat 64 (dispatchTarget (divisionOpcode kind)) = divisionZeroEntry kind := by
  cases kind <;> decide

/-- **The zero-branch selection input** at the post-dispatch configuration:
the VM stack register survives dispatch, and the stack top is the tagged 0. -/
theorem division_zero_input {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {rest : List Val}
    (h : ArmInput L P s op c pl cp sp high) (stack : s.stack = .int 0#63 :: rest)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8)
    (dp : DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    DivisionZeroInput (BitVec.ofNat 64 sp) d where
  good := dp.good
  image := dp.image h.dispatch.image
  tick := dp.tick
  stack := (dp.frame.frame Register.x9 (by decide)).trans h.spReg
  read := read
  zero := by
    have slot := stack_integer_word h.toVmReprAt stack
    have selected : s.stack[0]? = some (.int 0#63) := by simp only [stack, List.getElem?_cons_zero]
    have natAddress : (BitVec.ofNat 64 sp).toNat = sp := by
      simpa only [Nat.mul_zero, Nat.add_zero] using stack_slot_nat h.toVmReprAt selected
    rw [natAddress, word, dp.memory]
    exact slot.trans (by decide)

/-- A log above `.bss`'s end misses the program image. -/
theorem ImageOutside.of_above {log : List WEntry}
    (above : ∀ e ∈ log, Layout.sym_bss_end ≤ e.1) : ImageOutside log := by
  have text : Image.textBase + Image.textSize ≤ Layout.sym_bss_end := by decide
  have ro : Image.rodataBase + Image.rodataSize ≤ Layout.sym_bss_end := by decide
  have out : ∀ A n, A + n ≤ Layout.sym_bss_end → OutLRange log A n := by
    intro A n hA
    induction log with
    | nil => trivial
    | cons e log ih =>
      exact ⟨.inl (Nat.le_trans hA (above e (by simp))), ih fun e' he => above e' (by simp [he])⟩
  exact ⟨out _ _ text, out _ _ ro⟩

/-- The top stack slot is writable. -/
theorem StackGeometry.top_write {P s c pl cp sp high} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (nonempty : 0 < s.stack.length)
    (space : high - Layout.stackBytes ≤ sp) :
    WriteWindow (BitVec.ofNat 64 sp) 8 := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have ha := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hn : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hn] <;> simp only [Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega

/-- **The zero-divisor setup input** at the post-dispatch configuration: the
bytecode PC, VM stack and environment registers survive dispatch; the two VM
stack stores and the `extern_sp` publication are writable and miss the
image and the `Caml_state` pointer. -/
theorem division_zero_setup_input {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c d : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat} {rest : List Val} {env : BitVec 64}
    (h : ArmInput L P s op c pl cp sp high) (stack : s.stack = .int 0#63 :: rest)
    (envReg : gpr c Layout.reg_env = some env)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (dp : DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    DivisionZeroSetupInput (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) env
      (word c Layout.sym_Caml_state) d := by
  have g := h.geometry.toArmGeometry
  have hs := h.stack.1
  have ht := g.top
  have hg := g.statics
  have hl := g.domainLow
  have hda := g.domainArena
  have hdh := g.nursery.domainHigh
  have hal := g.domainAligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hoff : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
  have hoa : Layout.off_extern_sp % 8 = 0 := by decide
  have nonempty : 0 < s.stack.length := by simp [stack]
  have low : high - Layout.stackBytes + 8 * 1 ≤ sp := by
    have := stack_space h.stack (by omega : 8 * s.stack.length ≤ Layout.stackBytes); omega
  have spN : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  have envN : (divisionZeroEnvSp (BitVec.ofNat 64 sp)).toNat = sp - 8 := by
    simp only [divisionZeroEnvSp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have extN : (divisionZeroExtern (word c Layout.sym_Caml_state)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp := by
    simp only [divisionZeroExtern, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Layout.domainStateBytes, Layout.off_extern_sp] at *; omega
  refine {
    good := dp.good, image := dp.image h.dispatch.image, tick := dp.tick
    codeReg := (dp.frame.frame Register.x8 (by decide)).trans h.pc
    stack := (dp.frame.frame Register.x9 (by decide)).trans h.spReg
    environment := (dp.frame.frame Register.x25 (by decide)).trans envReg
    domainWord := by rw [word, dp.memory]; rfl
    codeWrite := g.toStackGeometry.top_write h.stack nonempty (by omega)
    envWrite := ?_, externWrite := ?_, domainOutside := ?_, imageOutside := ?_ }
  · have w := g.toStackGeometry.write h.stack (k := 1) (by decide) low
    have e : divisionZeroEnvSp (BitVec.ofNat 64 sp) = BitVec.ofNat 64 (sp - 8 * 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [envN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e]; exact w
  · have w := g.nursery.domain_write hoff hoa
    exact ⟨by rw [extN]; exact w.lower, by rw [extN]; exact w.upper, by rw [extN]; exact w.htif,
      by rw [extN]; exact w.aligned⟩
  · simp only [divisionZeroStackLog, OutLRange, spN, envN, and_true]
    have hdom : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
    omega
  · apply ImageOutside.of_above
    intro e he
    simp only [divisionZeroSetupLog, divisionZeroStackLog, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [spN]; omega
    · simp only [envN]; omega
    · simp only [extN]; omega

end OCaml.Vm.Sim
