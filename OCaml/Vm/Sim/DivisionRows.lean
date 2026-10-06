import OCaml.Vm.Sim.DivisionZeroCaught
import OCaml.Vm.Sim.RaiseRows
import OCaml.Vm.Sim.IntRows
import OCaml.Vm.Sim.LongjmpState
import OCaml.Vm.Sim.PayloadWindows

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
  /-- the field (`global + 40`) lies in a placed block, above `.bss` and
  below the allocator arena's end -/
  fieldLow : Layout.sym_bss_end ≤ (raiseZeroField (word c Layout.sym_caml_global_data)).toNat
  fieldBelow : (raiseZeroField (word c Layout.sym_caml_global_data)).toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd

/-- The exception field lies apart from the VM stack allocation and the
`Caml_state` record (it is a field of a placed block). -/
structure DivisionFieldApart (c : Config) (high : Nat) : Prop where
  stack : OutWRange [stackWindow high] (raiseZeroField (word c Layout.sym_caml_global_data)).toNat 8
  domain : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
    (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩]
    (raiseZeroField (word c Layout.sym_caml_global_data)).toNat 8

theorem DivisionException.of_field {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {exn : Val} (h : VmReprAt P s c pl cp sp high) (g : ArmGeometry P s c pl cp high)
    (field : field? s.heap P.globals 5 = some exn) :
    ∃ value, DivisionException P s pl c exn value ∧ DivisionFieldApart c high := by
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
  have bounds : Layout.sym_bss_end + 8 ≤ a ∧ a + 8 * (k + 5) + 8 ≤ Vsa.Sim.DlHeap.heapEnd ∧
      OutWRange [stackWindow high] (a + 8 * (k + 5)) 8 ∧
      OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
        (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] (a + 8 * (k + 5)) 8 := by
    have found := sel.selected
    rw [sel.pointer] at found
    simp only [field?] at found
    split at found
    · rename_i t fs got
      have idx := (List.getElem?_eq_some_iff.mp found).1
      have arena := g.heapArena l a _ sel.placed got
      have st := g.heap l a _ sel.placed got
      have dm := g.nursery.heapDomain l a _ sel.placed got
      simp only [Obj.wosize, OutWRange, and_true] at arena st dm
      refine ⟨g.heapLow l a _ sel.placed got, by omega, ?_, ?_⟩ <;> simp only [OutWRange, and_true] <;> omega
    · cases found
  have addrN : (raiseZeroField (word c Layout.sym_caml_global_data)).toNat = a + 8 * (k + 5) := by
    rw [fieldAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rd.upper; omega)]
  obtain ⟨blow, bhigh, bstack, bdomain⟩ := bounds
  refine ⟨word c (a + 8 * (k + 5)), ⟨fv.word, ⟨rfl, ?_, ?_⟩, ?_, by rw [addrN]; omega, by rw [addrN]; omega⟩,
    ⟨by rw [addrN]; exact bstack, by rw [addrN]; exact bdomain⟩⟩
  · rw [fieldAddr]; exact rd.window
  · rw [fieldAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := rd.upper; omega)]
  · rw [global]
    apply BitVec.eq_of_toNat_eq
    have small : a + 8 * k < 2 ^ 64 := by have := rd.upper; omega
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    rw [Nat.and_one_is_mod]; simp; omega

/-- **The zero helper's setup memory**: its saved return address lands in
the native scratch window, apart from the image, the global data word and
the exception field. -/
theorem raise_zero_setup_memory {P : Prog} {s : St} {pl : Place} {c : Config} {exn : Val}
    {value ra : BitVec 64} {D : InvocationData} (v : NativeValid D)
    (ex : DivisionException P s pl c exn value) :
    RaiseZeroSetupMemory (BitVec.ofNat 64 D.nativeSp) ra (word c Layout.sym_caml_global_data) value c := by
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have le : 16 ≤ D.nativeSp := by simp only [nativeHeadroom] at hh; omega
  have raN : (raiseZeroRa (BitVec.ofNat 64 D.nativeSp)).toNat = D.nativeSp - 8 := by
    rw [raiseZeroRa_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bss : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have glob : Layout.sym_caml_global_data + 8 ≤ Layout.sym_bss_end := by decide
  have fb := ex.fieldBelow
  refine ⟨⟨?_, ?_⟩, ex.memory, ex.globalBlock, ?_⟩
  · rw [raiseZeroRa_at le small]
    exact v.scratch_write (k := 8) (by decide) (by decide) (by decide)
  · apply ImageOutside.of_above
    intro e he
    simp only [raiseZeroLog, List.mem_singleton] at he
    subst he
    dsimp only
    rw [raN]
    simp only [nativeHeadroom] at hh
    simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at hh ⊢
    omega
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [raiseZeroLog, OutLRange, raN, and_true]
    simp only [nativeHeadroom] at hh
    rcases ha with rfl | rfl <;>
      simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd, Layout.sym_caml_global_data] at hh fb glob bss ⊢ <;>
      omega

/-! ## The interpreter's jump buffer -/

/-- The jump buffer's address (`raise_buf`, in the interpreter frame). -/
def raiseBuffer (D : InvocationData) : Nat := D.nativeSp + raiseBufOffset

/-- The saved words of the jump buffer. -/
def raiseSaved (D : InvocationData) (c : Config) : Nat → BitVec 64 :=
  fun r => word c (raiseBuffer D + Layout.jumpSaveOffset r)

/-- **The jump buffer is a readable saved frame**, returning to
`caml_interprete`'s resume point with the interpreter's native stack. -/
theorem NativeValid.jumpFrame {D : InvocationData} {c : Config} (v : NativeValid D) (inv : Invocation D c) :
    JumpSavedFrame (raiseBuffer D) (raiseSaved D c) c ∧ raiseSaved D c 1 = 0x80001e80#64 ∧
      raiseSaved D c 2 = BitVec.ofNat 64 D.nativeSp := by
  have hl := v.low
  have hh := v.high
  refine ⟨⟨fun _ _ => rfl, fun r hr => ?_⟩, v.jumpRa c inv, v.jumpSp c inv⟩
  have off : Layout.jumpSaveOffset r ≤ 104 := by
    simp only [Layout.jumpSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [raiseBuffer, raiseBufOffset, Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top,
    Layout.interpFrameBytes, Layout.camlMainFrameBytes] at *
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> first | omega | (simp only [Layout.sym_tohost]; omega)

/-! ## The runtime's raise memory -/

/-- **Runtime facts of the C raise path** (named obligation): the disabled
channel-unlock hook and quiet pending flag (a6-gc's F1 runtime pins and
`RuntimeFrame.quiet`), `Caml_state->external_raise` pointing at the
interpreter's jump buffer (a1-arms' `Invocation.raiseBuf`), and an ordinary
(non-exception-result) exception word. -/
structure RaiseRuntimeReady (c : Config) (D : InvocationData) (value : BitVec 64) : Prop where
  hook : word c Layout.sym_caml_channel_mutex_unlock_exn = 0#64
  pending : word32 c Layout.sym_caml_something_to_do = 0#32
  externalWord : word c (raiseExternal (word c Layout.sym_Caml_state)).toNat = BitVec.ofNat 64 (raiseBuffer D)
  ordinary : value &&& 3#64 ≠ 2#64

/-- A `Caml_state` field address without wraparound. -/
theorem domain_field_nat {P s c pl cp high} (g : ArmGeometry P s c pl cp high) {off : Nat}
    (fits : off + 8 ≤ Layout.domainStateBytes) :
    (word c Layout.sym_Caml_state + BitVec.ofNat 64 off).toNat = (word c Layout.sym_Caml_state).toNat + off := by
  have hh := g.nursery.domainHigh
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Layout.domainStateBytes] at hh fits
  omega

/-- **`caml_raise`'s native memory**: its frames lie in the native scratch
window, the exception bucket in the `Caml_state` record, and the jump buffer
in the interpreter frame; all apart. -/
theorem raise_native_memory {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    {D : InvocationData} {value : BitVec 64} (v : NativeValid D) (inv : Invocation D c)
    (g : ArmGeometry P s c pl cp high) (rr : RaiseRuntimeReady c D value) :
    RaiseNativeMemory (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)) 0x8000d1f8#64
      (word c Layout.sym_Caml_state) value (raiseBuffer D) (raiseSaved D c) c := by
  obtain ⟨jump, ra, -⟩ := v.jumpFrame inv
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have le : 160 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have hda := g.domainArena
  have hdl := g.domainLow
  have hal := g.domainAligned
  have ext := domain_field_nat g (off := Layout.off_external_raise) (by decide)
  have bkt := domain_field_nat g (off := Layout.off_exn_bucket) (by decide)
  have rtN : (raiseRuntimeRa (raiseZeroStack (BitVec.ofNat 64 D.nativeSp))).toNat = D.nativeSp - 24 := by
    rw [raiseRuntimeRa_at (by omega) small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have prN : (pendingRootRa (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)))).toNat = D.nativeSp - 56 := by
    rw [pendingRootRa_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pvN : (pendingRootValue (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)))).toNat = D.nativeSp - 136 := by
    rw [pendingRootValue_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bss : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have statics : Layout.sym_caml_something_to_do + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
  have bufN : (BitVec.ofNat 64 (raiseBuffer D)).toNat = raiseBuffer D := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      simp only [raiseBuffer, raiseBufOffset, Layout.sym_stack_top, Layout.interpFrameBytes,
        Layout.camlMainFrameBytes] at ht ⊢; omega)]
  have offs : ∀ r ∈ Layout.jumpSavedRegs, Layout.jumpSaveOffset r ≤ 104 := by decide
  refine ⟨⟨rr.hook, ?_, ?_⟩, ⟨rr.pending, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rr.ordinary, rfl, ?_, rr.externalWord, ?_, ?_, ?_⟩, ⟨jump, ?_, ?_⟩, ?_, ?_⟩
  -- prologue
  · rw [raiseRuntimeRa_at (by omega) small]
    exact v.scratch_write (k := 24) (by decide) (by decide) (by decide)
  · apply ImageOutside.of_above
    intro e he
    simp only [raiseRuntimeLog, List.mem_singleton] at he
    subst he
    dsimp only; rw [rtN]
    simp only [nativeHeadroom, Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at hh bss ⊢; omega
  -- pending
  · simp only [raiseRuntimeLog, OutLRange, rtN, and_true]
    simp only [nativeHeadroom, Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd, Layout.sym_caml_something_to_do] at hh bss statics ⊢
    omega
  · rw [pendingRootRa_at le small]
    exact v.scratch_write (k := 56) (by decide) (by decide) (by decide)
  · rw [pendingRootValue_at le small]
    exact v.scratch_write (k := 136) (by decide) (by decide) (by decide)
  · simp only [OutLRange, prN, pvN, and_true]; omega
  · apply ImageOutside.of_above
    intro e he
    simp only [pendingRootLog, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [nativeHeadroom, Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at hh bss
    rcases he with rfl | rfl
    · dsimp only; rw [prN]; simp only [Layout.sym_bss_end]; omega
    · dsimp only; rw [pvN]; simp only [Layout.sym_bss_end]; omega
  -- publish
  · have w := g.nursery.domain_write (off := Layout.off_external_raise) (by decide) (by decide)
    have rd := w.read.window
    simpa only [raiseExternal] using (show BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) =
        word c Layout.sym_Caml_state + BitVec.ofNat 64 Layout.off_external_raise from by
      apply BitVec.eq_of_toNat_eq; rw [ext, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.upper; omega)]) ▸ rd
  · intro zero
    have := congrArg BitVec.toNat zero
    rw [bufN] at this
    simp only [BitVec.toNat_ofNat, raiseBuffer, raiseBufOffset] at this; omega
  · have w := g.nursery.domain_write (off := Layout.off_exn_bucket) (by decide) (by decide)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [raiseBucket, bkt] <;> first | exact w.lower | exact w.upper | exact w.htif | exact w.aligned
  · apply ImageOutside.of_above
    intro e he
    simp only [raiseBucketLog, List.mem_singleton] at he
    subst he
    dsimp only; rw [raiseBucket, bkt]; omega
  -- jump
  · intro r hr
    have o := offs r hr
    simp only [raiseBucketLog, OutLRange, raiseBucket, bkt, and_true]
    simp only [raiseBuffer, raiseBufOffset, nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Layout.domainStateBytes,
      Layout.off_exn_bucket] at *
    omega
  · rw [ra]; decide
  -- runtimeOutside, savedOutside
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [raisePendingLog, raiseRuntimeLog, pendingRootLog, List.cons_append, List.nil_append,
      OutLRange, rtN, prN, pvN, and_true]
    rcases ha with rfl | rfl
    · simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Layout.sym_bss_end, Layout.sym_Caml_state]
        at hh bss statics ⊢
      omega
    · rw [raiseExternal, ext]
      simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Layout.domainStateBytes, Layout.off_external_raise]
        at hh hda ⊢
      omega
  · intro r hr
    have o := offs r hr
    simp only [raisePendingLog, raiseRuntimeLog, pendingRootLog, List.cons_append, List.nil_append,
      OutLRange, rtN, prN, pvN, and_true, raiseBuffer, raiseBufOffset]
    omega

/-- **The zero helper's complete memory**: setup, `caml_raise`'s native
memory, and the helper's saved return address apart from every word the
rest of the path reads. -/
theorem raise_zero_memory {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    {exn : Val} {D : InvocationData} {value : BitVec 64} (v : NativeValid D) (inv : Invocation D c)
    (g : ArmGeometry P s c pl cp high) (ex : DivisionException P s pl c exn value)
    (rr : RaiseRuntimeReady c D value) :
    RaiseZeroMemory (BitVec.ofNat 64 D.nativeSp) 0x80003cb0#64 (word c Layout.sym_caml_global_data)
      (word c Layout.sym_Caml_state) value (raiseBuffer D) (raiseSaved D c) c := by
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have le : 16 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have raN : (raiseZeroRa (BitVec.ofNat 64 D.nativeSp)).toNat = D.nativeSp - 8 := by
    rw [raiseZeroRa_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hda := g.domainArena
  have ext := domain_field_nat g (off := Layout.off_external_raise) (by decide)
  have fb := ex.fieldBelow
  have statics : Layout.sym_caml_global_data + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_channel_mutex_unlock_exn + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_something_to_do + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  obtain ⟨sg, sm, sc, sp, sb⟩ := statics
  have offs : ∀ r ∈ Layout.jumpSavedRegs, Layout.jumpSaveOffset r ≤ 104 := by decide
  refine ⟨raise_zero_setup_memory v ex, raise_native_memory v inv g rr, ?_, ?_, ?_⟩
  · intro a ha
    simp only [raiseMemoryWords, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [raiseZeroLog, OutLRange, raN, and_true]
    simp only [nativeHeadroom] at hh
    rcases ha with rfl | rfl | rfl
    · omega
    · omega
    · rw [raiseExternal, ext]
      simp only [Layout.domainStateBytes, Layout.off_external_raise] at hda ⊢
      omega
  · simp only [raiseZeroLog, OutLRange, raN, and_true]
    simp only [nativeHeadroom] at hh
    omega
  · intro r hr
    have o := offs r hr
    simp only [raiseZeroLog, OutLRange, raN, and_true, raiseBuffer, raiseBufOffset]
    omega

/-- **The zero path's native input** at the post-dispatch configuration: the
setup input, the native stack pointer, the runtime memory (transported over
dispatch, which writes no memory), and the setup log apart from everything
the rest of the path reads. -/
theorem division_zero_native_input {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c d : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat} {rest : List Val} {env : BitVec 64}
    {exn : Val} {value : BitVec 64} {D : InvocationData}
    (h : ArmInput L P s op c pl cp sp high) (stack : s.stack = .int 0#63 :: rest)
    (envReg : gpr c Layout.reg_env = some env)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (dp : DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d)
    (v : NativeValid D) (inv : Invocation D c)
    (ex : DivisionException P s pl c exn value) (apart : DivisionFieldApart c high)
    (rr : RaiseRuntimeReady c D value) :
    DivisionZeroNativeInput (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) env
      (word c Layout.sym_Caml_state) (BitVec.ofNat 64 D.nativeSp) (word c Layout.sym_caml_global_data)
      value (raiseBuffer D) (raiseSaved D c) d := by
  have g := h.geometry.toArmGeometry
  have hs := h.stack.1
  have hst := g.statics
  have har := g.arena
  have hdl := g.domainLow
  have hda := g.domainArena
  have hdom := g.domain
  simp only [stackWindow, OutWRange, and_true] at hdom
  have nonempty : 0 < s.stack.length := by simp [stack]
  have low := stack_space h.stack (by omega : 8 * s.stack.length ≤ Layout.stackBytes)
  have spN : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by
    have := g.top; simp only [Layout.stackBytes] at *; omega)
  have envN : (divisionZeroEnvSp (BitVec.ofNat 64 sp)).toNat = sp - 8 := by
    simp only [divisionZeroEnvSp, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := g.top; have := g.statics
    simp only [Layout.stackBytes, Layout.sym_bss_end] at *; omega
  have extN : (divisionZeroExtern (word c Layout.sym_Caml_state)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp := by
    rw [divisionZeroExtern]; exact domain_field_nat g (by decide)
  have ext := domain_field_nat g (off := Layout.off_external_raise) (by decide)
  have fa := apart.stack
  have fd := apart.domain
  simp only [stackWindow, OutWRange, and_true] at fa fd
  have fl := ex.fieldLow
  have hh := v.headroom
  have offs : ∀ r ∈ Layout.jumpSavedRegs, Layout.jumpSaveOffset r ≤ 104 := by decide
  have statics : Layout.sym_caml_global_data + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_channel_mutex_unlock_exn + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_something_to_do + 4 ≤ Layout.sym_bss_end ∧
      Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  obtain ⟨sg, sm, sc, sp4, sb⟩ := statics
  have memory : d.σ.mem = writeLog c.σ.mem [] := dp.memory
  refine ⟨division_zero_setup_input h stack envReg space dp,
    (dp.frame.frame Register.x2 (by decide)).trans inv.stack,
    (raise_zero_memory v inv g ex rr).frame memory (fun _ _ => trivial) trivial (fun _ _ => trivial),
    ?_, ?_, ?_⟩
  · intro a ha
    simp only [raiseZeroMemoryWords, raiseMemoryWords, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [divisionZeroSetupLog, divisionZeroStackLog, List.cons_append, List.nil_append,
      OutLRange, spN, envN, extN, and_true]
    simp only [Layout.stackBytes, Layout.domainStateBytes] at hst low space hdom fd fa hda
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · simp only [Layout.off_extern_sp]; omega
    · simp only [Layout.off_extern_sp]; omega
    · simp only [Layout.off_extern_sp]; omega
    · simp only [Layout.off_extern_sp]; omega
    · rw [raiseExternal, ext]; simp only [Layout.off_external_raise, Layout.off_extern_sp]; omega
  · simp only [divisionZeroSetupLog, divisionZeroStackLog, List.cons_append, List.nil_append,
      OutLRange, spN, envN, extN, and_true]
    simp only [Layout.stackBytes, Layout.domainStateBytes, Layout.off_extern_sp, Layout.sym_bss_end,
      Layout.sym_caml_something_to_do] at hst low hda hdl sp4 ⊢
    omega
  · intro r hr
    have o := offs r hr
    simp only [divisionZeroSetupLog, divisionZeroStackLog, List.cons_append, List.nil_append,
      OutLRange, spN, envN, extN, and_true, raiseBuffer, raiseBufOffset]
    simp only [nativeHeadroom, Layout.domainStateBytes, Layout.off_extern_sp] at hh hda ⊢
    omega

/-- **The re-entry memory** at the loop head (and, by `ReentryMemory.frame`,
after dispatch): the saved-roots slot in the interpreter frame, the domain
fields re-entry reads and writes, a trap pointer below the barrier (the raise
is caught), and a disabled backtrace. -/
theorem division_reentry_memory {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high high0 dom0 : Nat} {D : InvocationData}
    (rf : RuntimeFrame L high0 dom0) (h : ArmInput L P s op c pl cp sp high) (v : NativeValid D)
    (caught : s.trap ≠ 0) (trapBound : s.trap ≤ s.stack.length) :
    ReentryMemory D.nativeSp c := by
  have quiet := RaiseQuietReady.of_frame rf h
  have g := h.geometry.toArmGeometry
  have hl := v.low
  have ht := v.high
  have hs := h.stack.1
  have top := g.top
  refine ⟨?_, ?_, g.nursery.domain_write (by decide) (by decide), ?_, quiet.backtrace, ?_⟩
  · simp only [Layout.interpSavedRootsOffset, Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top,
      Layout.interpFrameBytes, Layout.camlMainFrameBytes] at *
    refine ⟨?_, ?_, Or.inr ?_⟩ <;> first | omega | (simp only [Layout.sym_tohost]; omega)
  · intro off hoff
    simp only [reentryReadOffsets, List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact h.geometry.domain_read
  · apply quiet.below
    have tw := h.trapsp
    have hst := g.statics
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, tw]
    simp only [Layout.stackBytes, Layout.sym_bss_end] at top hst
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · apply ImageOutside.of_above
    intro e he
    simp only [reentryLog, List.mem_singleton] at he
    subst he
    have := g.domainLow
    dsimp only; omega

/-- **The zero path's stores miss the re-entry control words**: the
`Caml_state` pointer, `trapsp`, `trap_barrier` and `backtrace_active`. -/
theorem division_control_outside {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat} {rest : List Val} {env value : BitVec 64}
    {D : InvocationData}
    (h : ArmInput L P s op c pl cp sp high) (stack : s.stack = .int 0#63 :: rest)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes) (v : NativeValid D) :
    ∀ a ∈ reentryControlWords c,
      OutLRange (divisionZeroNativeLog (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) env
        (word c Layout.sym_Caml_state) (BitVec.ofNat 64 D.nativeSp) value) a 8 := by
  have g := h.geometry.toArmGeometry
  have hs := h.stack.1
  have hst := g.statics
  have har := g.arena
  have hdl := g.domainLow
  have hda := g.domainArena
  have hdom := g.domain
  simp only [stackWindow, OutWRange, and_true] at hdom
  have low := stack_space h.stack (by omega : 8 * s.stack.length ≤ Layout.stackBytes)
  have nonempty : 0 < s.stack.length := by simp [stack]
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have le : 160 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have spN : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by
    have := g.top; simp only [Layout.stackBytes] at *; omega)
  have envN : (divisionZeroEnvSp (BitVec.ofNat 64 sp)).toNat = sp - 8 := by
    simp only [divisionZeroEnvSp, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := g.top; have := g.statics
    simp only [Layout.stackBytes, Layout.sym_bss_end] at *; omega
  have extN : (divisionZeroExtern (word c Layout.sym_Caml_state)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp := by
    rw [divisionZeroExtern]; exact domain_field_nat g (by decide)
  have bkt := domain_field_nat g (off := Layout.off_exn_bucket) (by decide)
  have raN : (raiseZeroRa (BitVec.ofNat 64 D.nativeSp)).toNat = D.nativeSp - 8 := by
    rw [raiseZeroRa_at (by omega) small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have rtN : (raiseRuntimeRa (raiseZeroStack (BitVec.ofNat 64 D.nativeSp))).toNat = D.nativeSp - 24 := by
    rw [raiseRuntimeRa_at (by omega) small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have prN : (pendingRootRa (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)))).toNat = D.nativeSp - 56 := by
    rw [pendingRootRa_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pvN : (pendingRootValue (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)))).toNat = D.nativeSp - 136 := by
    rw [pendingRootValue_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have sc : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end ∧ Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  intro a ha
  simp only [reentryControlWords, List.mem_cons, List.not_mem_nil, or_false] at ha
  simp only [divisionZeroNativeLog, divisionZeroSetupLog, divisionZeroStackLog, raiseZeroFullLog,
    raiseZeroLog, raiseNativeLog, raisePendingLog, raiseRuntimeLog, pendingRootLog, raiseBucketLog,
    List.cons_append, List.nil_append, List.append_assoc, OutLRange, spN, envN, extN, raN, rtN, prN, pvN,
    and_true]
  rw [show (raiseBucket (word c Layout.sym_Caml_state)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket from by rw [raiseBucket, bkt]]
  simp only [Layout.stackBytes, Layout.domainStateBytes, Layout.off_extern_sp, Layout.off_exn_bucket,
    Layout.off_trapsp, Layout.off_trap_barrier, Layout.off_backtrace_active, nativeHeadroom,
    Vsa.Sim.DlHeap.heapEnd, Layout.sym_bss_end, Layout.sym_Caml_state] at hst har hdl hda hdom low space hh sc
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp only [Layout.off_trapsp, Layout.off_trap_barrier, Layout.off_backtrace_active, Layout.off_extern_sp, Layout.off_exn_bucket,
      Layout.sym_Caml_state] <;> omega

/-! ## The zero path's log lies in payload windows -/

/-- The zero path's store windows: the divisor and environment slots below
the raise state's stack, the two `Caml_state` fields it publishes, and the
native scratch window. -/
def divisionWindows (c : Config) (sp : Nat) (D : InvocationData) : List W :=
  [⟨sp - 8, sp + 8⟩,
   ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp,
    (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp + 8⟩,
   ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket,
    (word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket + 8⟩,
   nativeScratch D]

/-- **Each zero-path window is a payload window** of the raise state at `sp + 8`. -/
theorem division_windows_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {D : InvocationData} (g : StackGeometry P s c pl cp high)
    (v : NativeValid D)
    (low : high - Layout.stackBytes + 8 ≤ sp) :
    ∀ w ∈ divisionWindows c sp D, PayloadWindow P s c pl cp (sp + 8) high w := by
  intro w hw
  simp only [divisionWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact .belowStack (show high - Layout.stackBytes ≤ sp - 8 by omega) (Nat.le_refl _)
  · exact .field (by simp [payloadFreeOffsets])
  · exact .field (by simp [payloadFreeOffsets])
  · exact .separated (WindowSeparated.of_above g
      (show _ ≤ D.nativeSp - nativeHeadroom from Nat.le_sub_of_add_le v.headroom))

/-- **Every store of the zero path lies in a zero-path window.** -/
theorem division_log_in {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat} {rest : List Val} {env value : BitVec 64}
    {D : InvocationData}
    (h : ArmInput L P s op c pl cp sp high) (stack : s.stack = .int 0#63 :: rest)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes) (v : NativeValid D) :
    LogInW (divisionWindows c sp D)
      (divisionZeroNativeLog (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) env
        (word c Layout.sym_Caml_state) (BitVec.ofNat 64 D.nativeSp) value) := by
  have g := h.geometry.toArmGeometry
  have hs := h.stack.1
  have low := stack_space h.stack (by omega : 8 * s.stack.length ≤ Layout.stackBytes)
  have nonempty : 0 < s.stack.length := by simp [stack]
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have le : 160 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have spN : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by
    have := g.top; simp only [Layout.stackBytes] at *; omega)
  have envN : (divisionZeroEnvSp (BitVec.ofNat 64 sp)).toNat = sp - 8 := by
    simp only [divisionZeroEnvSp, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := g.top; have := g.statics
    simp only [Layout.stackBytes, Layout.sym_bss_end] at *; omega
  have extN : (divisionZeroExtern (word c Layout.sym_Caml_state)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp := by
    rw [divisionZeroExtern]; exact domain_field_nat g (by decide)
  have bkt := domain_field_nat g (off := Layout.off_exn_bucket) (by decide)
  have raN : (raiseZeroRa (BitVec.ofNat 64 D.nativeSp)).toNat = D.nativeSp - 8 := by
    rw [raiseZeroRa_at (by omega) small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have rtN : (raiseRuntimeRa (raiseZeroStack (BitVec.ofNat 64 D.nativeSp))).toNat = D.nativeSp - 24 := by
    rw [raiseRuntimeRa_at (by omega) small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have prN : (pendingRootRa (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)))).toNat = D.nativeSp - 56 := by
    rw [pendingRootRa_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pvN : (pendingRootValue (raiseRuntimeStack (raiseZeroStack (BitVec.ofNat 64 D.nativeSp)))).toNat = D.nativeSp - 136 := by
    rw [pendingRootValue_at le small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [divisionWindows, nativeScratch, divisionZeroNativeLog,
    divisionZeroSetupLog, divisionZeroStackLog, raiseZeroFullLog, raiseZeroLog, raiseNativeLog,
    raisePendingLog, raiseRuntimeLog, pendingRootLog, raiseBucketLog, List.cons_append, List.nil_append,
    LogInW, InsideW, spN, envN, extN, raN, rtN, prN, pvN, and_true, or_false]
  rw [show (raiseBucket (word c Layout.sym_Caml_state)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket from by rw [raiseBucket, bkt]]
  simp only [Layout.stackBytes, Layout.off_extern_sp, Layout.off_exn_bucket, nativeHeadroom] at low space hh ⊢
  omega

end OCaml.Vm.Sim
