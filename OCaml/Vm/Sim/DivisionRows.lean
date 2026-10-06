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

/-! ## The native scratch window

The C runtime's raise path (`caml_raise_zero_divide`, `caml_raise`, the
pending-action check) stores into frames at most a few hundred bytes below
the interpreter's native stack pointer. `NativeValid.headroom` keeps
`nativeHeadroom` bytes there above the allocator arena. -/

/-- The free native stack below the interpreter frame. -/
def nativeScratch (D : InvocationData) : W := ⟨D.nativeSp - nativeHeadroom, D.nativeSp⟩

/-- An aligned native slot within the headroom is writable RAM. -/
theorem NativeValid.scratch_write {D : InvocationData} (v : NativeValid D) {k : Nat}
    (lo : 8 ≤ k) (hi : k ≤ nativeHeadroom) (al : k % 8 = 0) :
    WriteWindow (BitVec.ofNat 64 (D.nativeSp - k)) 8 := by
  have hh := v.headroom
  have ht := v.high
  have ha := v.aligned
  have hn : (BitVec.ofNat 64 (D.nativeSp - k)).toNat = D.nativeSp - k := Nat.mod_eq_of_lt (by
    simp only [Layout.sym_stack_top] at ht; omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hn] <;>
    simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top, Layout.sym_tohost,
      Layout.interpFrameBytes, Layout.camlMainFrameBytes] at * <;> omega

/-- The native scratch window lies above the allocator arena. -/
theorem NativeValid.scratch_above {D : InvocationData} (v : NativeValid D) :
    Vsa.Sim.DlHeap.heapEnd ≤ (nativeScratch D).lo := by
  have := v.headroom; simp only [nativeScratch]; omega

/-- `ofNat nsp - ofNat a = ofNat (nsp - a)` without wraparound. -/
theorem ofNat_sub_ofNat {nsp a : Nat} (le : a ≤ nsp) (small : nsp < 2 ^ 64) :
    BitVec.ofNat 64 nsp - BitVec.ofNat 64 a = BitVec.ofNat 64 (nsp - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : nsp - a < 2 ^ 64)]
  omega

/-- `ofNat x + ofNat b = ofNat (x + b)`. -/
theorem ofNat_add_ofNat' (x b : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 b = BitVec.ofNat 64 (x + b) :=
  (BitVec.ofNat_add_ofNat x b).symm ▸ rfl

theorem raiseZeroRa_at {nsp : Nat} (le : 16 ≤ nsp) (small : nsp < 2 ^ 64) :
    raiseZeroRa (BitVec.ofNat 64 nsp) = BitVec.ofNat 64 (nsp - 8) := by
  simp only [raiseZeroRa, raiseZeroStack, Layout.raiseZeroFrameBytes, Layout.raiseZeroSaveRaOffset,
    ofNat_sub_ofNat le small, ofNat_add_ofNat']
  congr 1; omega

theorem raiseRuntimeRa_at {nsp : Nat} (le : 48 ≤ nsp) (small : nsp < 2 ^ 64) :
    raiseRuntimeRa (raiseZeroStack (BitVec.ofNat 64 nsp)) = BitVec.ofNat 64 (nsp - 24) := by
  simp only [raiseRuntimeRa, raiseRuntimeStack, raiseZeroStack, Layout.raiseZeroFrameBytes,
    Layout.raiseRuntimeFrameBytes, Layout.raiseRuntimeSaveRaOffset,
    ofNat_sub_ofNat (by omega : 16 ≤ nsp) small, ofNat_sub_ofNat (by omega : 32 ≤ nsp - 16) (by omega),
    ofNat_add_ofNat']
  congr 1; omega

theorem pendingRootRa_at {nsp : Nat} (le : 160 ≤ nsp) (small : nsp < 2 ^ 64) :
    pendingRootRa (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 nsp))) = BitVec.ofNat 64 (nsp - 56) := by
  simp only [pendingRootRa, pendingRootStack, raiseRuntimeStack, raiseZeroStack, Layout.raiseZeroFrameBytes,
    Layout.raiseRuntimeFrameBytes, Layout.pendingRootFrameBytes, Layout.pendingRootSaveRaOffset,
    ofNat_sub_ofNat (by omega : 16 ≤ nsp) small, ofNat_sub_ofNat (by omega : 32 ≤ nsp - 16) (by omega),
    ofNat_sub_ofNat (by omega : 112 ≤ nsp - 16 - 32) (by omega), ofNat_add_ofNat']
  congr 1; omega

theorem pendingRootValue_at {nsp : Nat} (le : 160 ≤ nsp) (small : nsp < 2 ^ 64) :
    pendingRootValue (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 nsp))) = BitVec.ofNat 64 (nsp - 136) := by
  simp only [pendingRootValue, pendingRootStack, raiseRuntimeStack, raiseZeroStack, Layout.raiseZeroFrameBytes,
    Layout.raiseRuntimeFrameBytes, Layout.pendingRootFrameBytes, Layout.pendingRootSaveValueOffset,
    ofNat_sub_ofNat (by omega : 16 ≤ nsp) small, ofNat_sub_ofNat (by omega : 32 ≤ nsp - 16) (by omega),
    ofNat_sub_ofNat (by omega : 112 ≤ nsp - 16 - 32) (by omega), ofNat_add_ofNat']
  rw [show nsp - 16 - 32 - 112 + 24 = nsp - 136 by omega]

/-! ## The `Division_by_zero` exception value -/

/-- **The exception value read by `caml_raise_zero_divide`**: field 5 of the
global data block. Its word is the represented exception; the global block
pointer is even. -/
structure DivisionException (P : Prog) (s : St) (pl : Place) (c : Config) (exn : Val)
    (value : BitVec 64) : Prop where
  valueWord : valWord pl exn = some value
  memory : RaiseZeroValueMemory (word c Layout.sym_caml_global_data) value c
  globalBlock : word c Layout.sym_caml_global_data &&& 1#64 = 0#64
  /-- the field's address (`global + 40`) lies in a placed block -/
  field : ∃ l a k, pl.φ l = some a ∧ (raiseZeroField (word c Layout.sym_caml_global_data)).toNat = a + 8 * (k + 5) ∧
    ∃ o, s.heap.get? l = some o

theorem DivisionException.of_field {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {exn : Val} (h : VmReprAt P s c pl cp sp high) (g : StackGeometry P s c pl cp high)
    (field : field? s.heap P.globals 5 = some exn) :
    ∃ value, DivisionException P s pl c exn value := by
  obtain ⟨l, a, k, sel⟩ := field_selection h (by simp [roots]) field
  have fv := sel.read h (by simp [roots])
  have rd := g.field_read sel
  have src := sel.sourceWord
  rw [h.globals] at src
  have global : word c Layout.sym_caml_global_data = BitVec.ofNat 64 (a + 8 * k) := Option.some.inj src
  have even := g.words.heap l a sel.placed
  have rn := rd.toNat
  have fieldAddr : raiseZeroField (word c Layout.sym_caml_global_data) = BitVec.ofNat 64 (a + 8 * (k + 5)) := by
    rw [global, raiseZeroField, Layout.raiseZeroExceptionOffset, ofNat_add_ofNat']
    congr 1
  have object : ∃ o, s.heap.get? l = some o := by
    have found := sel.selected
    rw [sel.pointer] at found
    simp only [field?] at found
    split at found
    · rename_i t fs got; exact ⟨_, got⟩
    · cases found
  refine ⟨word c (a + 8 * (k + 5)), fv.word, ⟨rfl, ?_, ?_⟩, ?_, ⟨l, a, k, sel.placed, ?_, object⟩⟩
  · rw [fieldAddr]; exact rd.window
  · rw [fieldAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rd.upper; omega)]
  · rw [global]
    apply BitVec.eq_of_toNat_eq
    have small : a + 8 * k < 2 ^ 64 := by have := rd.upper; omega
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    rw [Nat.and_one_is_mod]; simp; omega
  · rw [fieldAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rd.upper; omega)]

end OCaml.Vm.Sim
