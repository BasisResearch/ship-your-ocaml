import OCaml.Vm.Sim.CcallReturn
import OCaml.Vm.Sim.CcallnSuffixSegment
import OCaml.Vm.Sim.CcallnSuffixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- C_CALLN's saved caller frame. Its bytecode PC is in a native stack slot;
s7 retains the argument-byte count. Setup establishes these facts, and the
primitive's caller-frame summary preserves them. -/
structure CcallnSaved (s : St) (pl : Place) (sp count : Nat)
    (nativeSp domain frameSp env : BitVec 64) (c : Config) : Prop where
  domainReg : gpr c Layout.reg_env = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  countReg : gpr c 23 = some (BitVec.ofNat 64 (8 * count))
  nativeReg : gpr c 2 = some nativeSp
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)
  envRepr : valWord pl s.env = some env
  domainWord : domain = word c Layout.sym_Caml_state
  savedStack : frameSp = word c (domain + BitVec.ofNat 64 Layout.off_extern_sp).toNat
  savedEnv : env = word c frameSp.toNat
  savedPC : BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) = word c (nativeSp + 88#64).toNat
  restoreStack : frameSp + 24#64 = BitVec.ofNat 64 sp
  domainRead : ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8
  stackRead : ReadWindow (domain + BitVec.ofNat 64 Layout.off_extern_sp) 8
  envRead : ReadWindow frameSp 8
  pcRead : ReadWindow (nativeSp + 88#64) 8

/-- Callee-saved VM/native registers needed by the variable-arity suffix. -/
def callnSavedRegs : List Register :=
  [gprReg Layout.reg_env, gprReg Layout.reg_extra, Register.x23, Register.x2]

/-- A read-only callee preserves the caller-owned native and VM frame. -/
theorem CcallnSaved.frame {s : St} {pl : Place} {sp count : Nat}
    {nativeSp domain frameSp env : BitVec 64} {before after : Config}
    (h : CcallnSaved s pl sp count nativeSp domain frameSp env before)
    (memory : after.σ.mem = before.σ.mem)
    (regs : ∀ r ∈ callnSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r) :
    CcallnSaved s pl sp count nativeSp domain frameSp env after := by
  have reads (a : Nat) : word after a = word before a := by simp only [word, memory]
  exact { h with
    domainReg := (regs _ (by decide)).trans h.domainReg
    countReg := (regs _ (by decide)).trans h.countReg
    nativeReg := (regs _ (by decide)).trans h.nativeReg
    extra := (regs _ (by decide)).trans h.extra
    domainWord := by rw [reads]; exact h.domainWord
    savedStack := by rw [reads]; exact h.savedStack
    savedEnv := by rw [reads]; exact h.savedEnv
    savedPC := by rw [reads]; exact h.savedPC }

/-- C_CALLN result and saved frame stay separate named representation parts. -/
structure CcallnReturn (L : OCaml.Layout) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high count : Nat)
    (nativeSp domain frameSp result env : BitVec 64) (c : Config) : Prop
    extends CcallnSaved s pl sp count nativeSp domain frameSp env c,
      CcallResult (0x80002e64#64) L P s pl cp sp high result c

/-- Consume the represented primitive result and preserved C_CALLN frame.
The bytecode continuation skips the opcode and both operand words. -/
theorem c_calln_primitive_return {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high count : Nat} {name : String} {v : Val}
    {nativeSp domain frameSp result env : BitVec 64} {heap : Heap} {world : World}
    {args : List Val} {writes : List Nat} {memory : Std.ExtHashMap Nat (BitVec 8)}
    {before after : Config}
    (post : PrimitivePost L.runtimeOk P s pl cp sp high name args
      v result heap world writes memory before (0x80002e64#64) after)
    (saved : CcallnSaved {s with pc := s.pc + 3} pl sp count nativeSp domain frameSp env after)
    (geometry : ArmGeometry P {s with accu := v, heap := heap, world := world} after pl cp high)
    (native : NativePlaced after) :
    CcallnReturn L P {s with pc := s.pc + 3, accu := v, heap := heap, world := world}
      pl cp sp high count nativeSp domain frameSp result env after :=
  { toCcallnSaved := { saved with savedPC := saved.savedPC }
    toCcallResult := ccall_primitive_result (s.pc + 3) post geometry native }

/-- Read-only primitive summaries retain the native saved-PC slot as well as
the VM saved frame; the ABI write-set check discharges the register frame. -/
theorem c_calln_readOnly_summary {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high count : Nat} {name : String} {v : Val}
    {nativeSp domain frameSp result env entry : BitVec 64} {args : List Val}
    {writes : List Nat} {before : Config}
    (S : FnSummary entry (fun c => c = before)
      (ReadOnlyPost L.runtimeOk P s pl cp sp high name args
        v result writes before (0x80002e64#64)))
    (preserved : ∀ r ∈ callnSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (saved : CcallnSaved {s with pc := s.pc + 3} pl sp count nativeSp domain frameSp env before)
    (geometry : ArmGeometry P s before pl cp high) (native : NativePlaced before) :
    FnSummary entry (fun c => c = before)
      (CcallnReturn L P {s with pc := s.pc + 3, accu := v}
        pl cp sp high count nativeSp domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after post
  exact c_calln_primitive_return post (saved.frame post.call.memory
    (fun r hr => post.call.frame r (preserved r hr) (by revert r; decide)))
    (geometry.same rfl rfl post.call.memory)
    (native.frame_read post.call.memory
      (post.call.frame (gprReg 2) (preserved _ (by decide)) (by decide)))

/-- The extra pushed accumulator accounts for the difference between the
three-word saved-frame displacement and the consumed stack-argument count. -/
theorem ccalln_return_sp {frameSp : BitVec 64} {sp count : Nat}
    (saved : frameSp + 24#64 = BitVec.ofNat 64 sp) (positive : 0 < count) :
    frameSp + (BitVec.ofNat 64 (8 * count) + 16#64) =
      BitVec.ofNat 64 (sp + 8 * (count - 1)) := by
  have size : 8 * count + 16 = 24 + 8 * (count - 1) := by omega
  rw [← BitVec.ofNat_add, size, BitVec.ofNat_add, ← BitVec.add_assoc,
    saved, ← BitVec.ofNat_add]

/-- The generated C_CALLN suffix restores the saved PC and environment, the
primitive result, and the stack with exactly count-minus-one values removed. -/
theorem c_calln_return {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high count : Nat}
    {nativeSp domain frameSp result env : BitVec 64} {c : Config}
    (stable : MemoryStable L.runtimeOk)
    (h : CcallnReturn L P s pl cp sp high count nativeSp domain frameSp result env c)
    (positive : 0 < count) (bound : count - 1 ≤ s.stack.length) :
    ∃ after, Plus c after ∧ Running L P {s with stack := s.stack.drop (count - 1)} after := by
  have loaded (a : Nat) : sign_extend (m := 64) (bytesT8 c.σ.mem a) = word c a := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have bp : SegSt (0x80002e64#64)
      [⟨Register.x25, BitVec.ofNat 64 Layout.sym_Caml_state⟩,
       ⟨Register.x23, BitVec.ofNat 64 (8 * count)⟩, ⟨Register.x2, nativeSp⟩, ⟨Register.x10, result⟩]
      (fun σ => Vsa.Sim.Code.CamlCcallnSuffixLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.platform.control, h.returnPC, ⟨h.domainReg, h.countReg, h.nativeReg, h.resultReg, trivial⟩,
      h.platform.control.minstret, h.tick, c_calln_suffix_loaded h.platform.image, rfl, rfl⟩
  have run := tr_c_calln_suffix (BitVec.ofNat 64 Layout.sym_Caml_state)
    (BitVec.ofNat 64 (8 * count)) nativeSp result c.σ.mem c.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, loaded,
    show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = Layout.sym_Caml_state from by decide,
    show sign_extend (m := 64) (0x058#12) = 88#64 from by decide,
    show sign_extend (m := 64) (0x0a0#12) = BitVec.ofNat 64 Layout.off_extern_sp from by decide] at run
  obtain ⟨n, after, stepsCount, steps, post⟩ := run
    h.domainRead.lower h.domainRead.upper h.domainRead.htif domain h.domainWord
    h.pcRead.lower h.pcRead.upper h.pcRead.htif (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) h.savedPC
    h.stackRead.lower h.stackRead.upper h.stackRead.htif frameSp h.savedStack
    h.envRead.lower h.envRead.upper h.envRead.htif env h.savedEnv c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨after, ⟨n - 1, by simpa only [show n - 1 + 1 = n from by omega] using steps⟩, ?_⟩
  apply ccall_result_restore stable h.toCcallResult bound ?_ ?_ post.good memory frame.out
    (frame.frame (gprReg 2) (by decide))
  · refine ⟨post.pcAt, PinsHold.get post.pins ⟨4, by simp⟩, ?_,
      ⟨result, PinsHold.get post.pins ⟨2, by simp⟩, h.resultRepr⟩,
      ⟨env, PinsHold.get post.pins ⟨1, by simp⟩, h.envRepr⟩, ?_⟩
    · have hp : gpr after Layout.reg_sp = some
          (frameSp + (BitVec.ofNat 64 (8 * count) + sign_extend (m := 64) (0x010#12))) :=
        PinsHold.get post.pins ⟨0, by simp⟩
      simpa only [show sign_extend (m := 64) (0x010#12) = 16#64 from by decide,
        ccalln_return_sp h.restoreStack positive] using hp
    · exact (frame.frame (gprReg Layout.reg_extra) (by decide)).trans h.extra
  · exact loopRegisters_frame
      (fun r hr => frame.frame r (by revert r; decide)) h.loop

/-- Triple interface for C_CALLN's represented return, consumed by callSeg. -/
theorem c_calln_return_triple {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high count : Nat} {nativeSp domain frameSp result env : BitVec 64}
    (stable : MemoryStable L.runtimeOk) (positive : 0 < count) (bound : count - 1 ≤ s.stack.length) :
    Vsa.Logic.Triple (CcallnReturn L P s pl cp sp high count nativeSp domain frameSp result env)
      (Running L P {s with stack := s.stack.drop (count - 1)}) := by
  intro c h
  obtain ⟨after, ⟨n, steps⟩, repr⟩ := c_calln_return stable h positive bound
  exact ⟨after, steps.toSteps, repr⟩

end OCaml.Vm.Sim
