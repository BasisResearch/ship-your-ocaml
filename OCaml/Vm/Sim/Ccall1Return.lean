import OCaml.Vm.Sim.ReadOnly
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.ImmediateContract
import OCaml.Vm.Sim.Ccall1SuffixSegment
import OCaml.Vm.Sim.Ccall1SuffixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Caller-owned C_CALL1 frame. Setup establishes it; primitive frame summaries
preserve the saved words and the callee-saved registers needed on return. -/
structure Ccall1Saved (s : St) (pl : Place) (sp : Nat)
    (domain frameSp env : BitVec 64) (c : Config) : Prop where
  domainReg : gpr c Layout.reg_env = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  pc : gpr c Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)
  envRepr : valWord pl s.env = some env
  domainWord : domain = word c Layout.sym_Caml_state
  savedStack : frameSp = word c (domain + BitVec.ofNat 64 Layout.off_extern_sp).toNat
  savedEnv : env = word c frameSp.toNat
  restoreStack : frameSp + 16#64 = BitVec.ofNat 64 sp
  domainRead : ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8
  stackRead : ReadWindow (domain + BitVec.ofNat 64 Layout.off_extern_sp) 8
  envRead : ReadWindow frameSp 8

/-- VM registers carried through the C primitive by the ABI. -/
def callSavedRegs : List Register :=
  [gprReg Layout.reg_env, gprReg Layout.reg_pc, gprReg Layout.reg_extra]

/-- A read-only primitive preserves the caller-owned saved words and registers. -/
theorem Ccall1Saved.frame {s : St} {pl : Place} {sp : Nat}
    {domain frameSp env : BitVec 64} {before after : Config}
    (h : Ccall1Saved s pl sp domain frameSp env before)
    (memory : after.σ.mem = before.σ.mem)
    (regs : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r) :
    Ccall1Saved s pl sp domain frameSp env after := by
  have reads (a : Nat) : word after a = word before a := by simp only [word, memory]
  exact { h with
    domainReg := (regs _ (by decide)).trans h.domainReg
    pc := (regs _ (by decide)).trans h.pc
    extra := (regs _ (by decide)).trans h.extra
    domainWord := by rw [reads]; exact h.domainWord
    savedStack := by rw [reads]; exact h.savedStack
    savedEnv := by rw [reads]; exact h.savedEnv }

/-- Return boundary shared by successful C_CALL1 primitives. Data/platform
come from the primitive summary; the caller-owned saved frame stays separate. -/
structure Ccall1Return (L : OCaml.Layout) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat)
    (domain frameSp result env : BitVec 64) (c : Config) : Prop
    extends Ccall1Saved s pl sp domain frameSp env c where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  platform : PlatformOk L.runtimeOk c
  loop : LoopRegisters c
  tick : c.tick < 2
  returnPC : pcOf c = some (0x80003060#64)
  resultReg : gpr c 10 = some result
  resultRepr : valWord pl s.accu = some result

/-- Consume a1-prims' represented postcondition without reproving a primitive.
C_CALL1 advances two code words and leaves its argument stack unchanged. -/
theorem c_call1_primitive_return {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {domain frameSp result env : BitVec 64} {heap : Heap} {world : World}
    {writes : List Nat} {memory : Std.ExtHashMap Nat (BitVec 8)} {before after : Config}
    (post : PrimitivePost L.runtimeOk P s pl cp sp high name [s.accu]
      v result heap world writes memory before (0x80003060#64) after)
    (saved : Ccall1Saved {s with pc := s.pc + 2} pl sp domain frameSp env after) :
    Ccall1Return L P {s with pc := s.pc + 2, accu := v, heap := heap, world := world}
      pl cp sp high domain frameSp result env after :=
  { toCcall1Saved := { saved with pc := saved.pc }
    data := payload_pc post.data (s.pc + 2)
    primitives := post.primitives
    platform := post.platform
    loop := post.loop
    tick := post.call.tick
    returnPC := post.call.pc
    resultReg := post.call.result
    resultRepr := post.resultRepr }

/-- Adapt any landed read-only primitive summary to the generated return
boundary. The finite write-set check is an ABI fact, not a primitive proof. -/
theorem c_call1_readOnly_summary {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {domain frameSp result env entry : BitVec 64} {writes : List Nat} {before : Config}
    (S : FnSummary entry (fun c => c = before)
      (ReadOnlyPost L.runtimeOk P s pl cp sp high name [s.accu]
        v result writes before (0x80003060#64)))
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (saved : Ccall1Saved {s with pc := s.pc + 2} pl sp domain frameSp env before) :
    FnSummary entry (fun c => c = before)
      (Ccall1Return L P {s with pc := s.pc + 2, accu := v}
        pl cp sp high domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after post
  exact c_call1_primitive_return post (saved.frame post.call.memory
    (fun r hr => post.call.frame r (preserved r hr) (by revert r; decide)))

/-- The generated return suffix restores Running from a represented primitive
result, including saved VM registers and the complete platform invariant. -/
theorem c_call1_return {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high : Nat} {domain frameSp result env : BitVec 64} {c : Config}
    (stable : MemoryStable L.runtimeOk)
    (h : Ccall1Return L P s pl cp sp high domain frameSp result env c) :
    ∃ after, Plus c after ∧ Running L P s after := by
  have loaded (a : Nat) : sign_extend (m := 64) (bytesT8 c.σ.mem a) = word c a := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have bp : SegSt (0x80003060#64)
      [⟨Register.x25, BitVec.ofNat 64 Layout.sym_Caml_state⟩, ⟨Register.x10, result⟩]
      (fun σ => Vsa.Sim.Code.CamlCcall1SuffixLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.platform.control, h.returnPC, ⟨h.domainReg, h.resultReg, trivial⟩,
      h.platform.control.minstret, h.tick, c_call1_suffix_loaded h.platform.image, rfl, rfl⟩
  have run := tr_c_call1_suffix (BitVec.ofNat 64 Layout.sym_Caml_state) result c.σ.mem c.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, loaded,
    show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = Layout.sym_Caml_state from by decide,
    show sign_extend (m := 64) (0x0a0#12) = BitVec.ofNat 64 Layout.off_extern_sp from by decide] at run
  obtain ⟨n, after, count, steps, post⟩ := run
    h.domainRead.lower h.domainRead.upper h.domainRead.htif domain h.domainWord
    h.stackRead.lower h.stackRead.upper h.stackRead.htif frameSp h.savedStack
    h.envRead.lower h.envRead.upper h.envRead.htif env h.savedEnv c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨after, ⟨n - 1, by simpa only [show n - 1 + 1 = n from by omega] using steps⟩, ?_⟩
  apply readOnly_restore stable h.data h.primitives h.platform ?_ ?_ post.good memory frame.out
  · refine ⟨post.pcAt, ?_, ?_, ⟨result, ?_, h.resultRepr⟩,
      ⟨env, PinsHold.get post.pins ⟨1, by simp⟩, h.envRepr⟩, ?_⟩
    · exact (frame.frame Register.x8 (by decide)).trans h.pc
    · have hp : gpr after Layout.reg_sp = some (frameSp + sign_extend (m := 64) (0x010#12)) :=
        PinsHold.get post.pins ⟨0, by simp⟩
      simpa only [show sign_extend (m := 64) (0x010#12) = 16#64 from by decide,
        h.restoreStack] using hp
    · exact PinsHold.get post.pins ⟨2, by simp⟩
    · exact (frame.frame (gprReg Layout.reg_extra) (by decide)).trans h.extra
  · exact loopRegisters_frame
      (fun r hr => frame.frame r (by revert r; decide)) h.loop

/-- Triple interface for the generated represented return, for callSeg splices. -/
theorem c_call1_return_triple {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high : Nat} {domain frameSp result env : BitVec 64}
    (stable : MemoryStable L.runtimeOk) :
    Vsa.Logic.Triple (Ccall1Return L P s pl cp sp high domain frameSp result env) (Running L P s) := by
  intro c h
  obtain ⟨after, ⟨n, steps⟩, repr⟩ := c_call1_return stable h
  exact ⟨after, steps.toSteps, repr⟩

end OCaml.Vm.Sim
