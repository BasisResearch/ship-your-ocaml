import OCaml.Vm.Sim.RaiseState
import OCaml.Vm.Sim.ComparisonArithmetic
import OCaml.Vm.Sim.RaiseCheckSegment
import OCaml.Vm.Sim.RaiseCheckPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The initial interpreter invocation saved equal stack-high and external-SP
words. Startup supplies this native frame; nested callbacks need a relative
cut instead. This fact is independent of abstract heap relocation. -/
structure RaiseStackFrame (nativeSp : Nat) (c : Config) : Prop where
  stack : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  equalSaved : word c nativeSp = word c (nativeSp + 8)
  highRead : RamReadAt nativeSp 8
  spRead : RamReadAt (nativeSp + 8) 8

/-- Read-only prefixes preserve the saved native invocation boundary. -/
theorem RaiseStackFrame.frame {nativeSp : Nat} {c after : Config}
    (h : RaiseStackFrame nativeSp c) (memory : after.σ.mem = c.σ.mem)
    (stack : gpr after 2 = gpr c 2) : RaiseStackFrame nativeSp after :=
  ⟨stack.trans h.stack, by simpa only [word, memory] using h.equalSaved, h.highRead, h.spRead⟩

/-- The caught-handler test follows from an active represented trap and the
root invocation's saved native frame. No branch result is assumed. -/
theorem raise_check {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high dest nativeSp : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c : Config}
    (h : RaiseCheckInput L P s pl cp sp high dest link env extra rest c)
    (stable : MemoryStable L.runtimeOk) (saved : RaiseStackFrame nativeSp c)
    (highRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8) :
    ∃ count after, StepsN count c after ∧ RaiseReadPost (0x80001ef0#64) c L P s pl cp sp high dest link env extra rest after := by
  have savedHigh : sign_extend (m := 64) (bytesT8 c.σ.mem nativeSp) = word c nativeSp := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have savedSp : sign_extend (m := 64) (bytesT8 c.σ.mem (nativeSp + 8)) = word c nativeSp := by
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using saved.equalSaved.symm
  have highWord : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) = BitVec.ofNat 64 high := by
    rw [← h.data.stackHigh, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have highValue : sign_extend (m := 64) (bytesT8 c.σ.mem ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)) = BitVec.ofNat 64 high := by
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using highWord
  have highAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x090#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl
  have stackNext : BitVec.ofNat 64 nativeSp + 8#64 = BitVec.ofNat 64 (nativeSp + 8) := by simp [BitVec.ofNat_add]
  have bp : SegSt (0x80001ed4#64)
      [⟨Register.x2, BitVec.ofNat 64 nativeSp⟩, ⟨Register.x15, word c Layout.sym_Caml_state⟩,
       ⟨Register.x14, BitVec.ofNat 64 (high - 8 * s.trap)⟩]
      (fun σ => Vsa.Sim.Code.CamlRaiseCheckLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.platform.control, h.pc, ⟨saved.stack, h.domainReg, h.trapReg, trivial⟩,
      h.platform.control.minstret, h.tick, raise_check_loaded h.platform.image, rfl, rfl⟩
  have native := tr_raise_check (BitVec.ofNat 64 nativeSp) (word c Layout.sym_Caml_state)
    (BitVec.ofNat 64 (high - 8 * s.trap)) c.σ.mem c.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from rfl,
    show sign_extend (m := 64) (0x008#12) = 8#64 from rfl, BitVec.add_zero,
    stackNext, saved.highRead.toNat, saved.spRead.toNat, highAddress, highRead.toNat] at native
  have guard : zopz0zI_u (BitVec.ofNat 64 (high - 8 * s.trap))
      (BitVec.ofNat 64 high - (word c nativeSp - word c nativeSp)) = true := by
    simpa only [BitVec.sub_self, BitVec.sub_zero, native_ult, BitVec.ule_eq_not_ult, Bool.not_not] using h.toRaiseContext.caught_guard
  obtain ⟨count, after, _, run, post⟩ := native saved.highRead.lower saved.highRead.upper saved.highRead.htif
    (word c nativeSp) savedHigh.symm saved.spRead.lower saved.spRead.upper saved.spRead.htif
    (word c nativeSp) savedSp.symm highRead.lower highRead.upper highRead.htif (BitVec.ofNat 64 high) highValue.symm guard c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨count, after, run, ?_, memory, frame.frame Register.x2 (by decide)⟩
  refine {
    toRaiseContext := h.toRaiseContext.after_read stable post.good post.tick memory frame.out (frame.frame _ (by decide))
    pc := post.pcAt
    trapReg := (frame.frame Register.x14 (by decide)).trans h.trapReg
    domainReg := ?_ }
  have domain : gpr after 15 = some (word c Layout.sym_Caml_state) :=
    (frame.frame Register.x15 (by decide)).trans h.domainReg
  simpa only [word, memory] using domain

end OCaml.Vm.Sim
