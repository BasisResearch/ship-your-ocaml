import OCaml.Vm.Sim.ReadOnly
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.ImmediateContract
import OCaml.Vm.Sim.StackDrop

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Caller-owned fixed-arity C_CALL frame. Setup establishes it; primitive frame summaries
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

/-- Return boundary shared by successful fixed-arity C primitives. Data/platform
come from the primitive summary; the caller-owned saved frame stays separate. -/
structure CcallReturn (ra : BitVec 64) (L : OCaml.Layout) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat)
    (domain frameSp result env : BitVec 64) (c : Config) : Prop
    extends Ccall1Saved s pl sp domain frameSp env c where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  platform : PlatformOk L.runtimeOk c
  loop : LoopRegisters c
  tick : c.tick < 2
  returnPC : pcOf c = some ra
  resultReg : gpr c 10 = some result
  resultRepr : valWord pl s.accu = some result

/-- Retain the unary return interface while sharing its saved-frame contract. -/
abbrev Ccall1Return (L : OCaml.Layout) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat)
    (domain frameSp result env : BitVec 64) :=
  CcallReturn (0x80003060#64) L P s pl cp sp high domain frameSp result env

/-- Consume a1-prims' represented postcondition without reproving a primitive.
The caller chooses the next bytecode PC; return restoration consumes stack arguments. -/
theorem ccall_primitive_return {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {domain frameSp result env : BitVec 64} {heap : Heap} {world : World}
    {ra : BitVec 64} {pc : Nat} {args : List Val} {writes : List Nat} {memory : Std.ExtHashMap Nat (BitVec 8)} {before after : Config}
    (post : PrimitivePost L.runtimeOk P s pl cp sp high name args
      v result heap world writes memory before ra after)
    (saved : Ccall1Saved {s with pc := pc} pl sp domain frameSp env after) :
    CcallReturn ra L P {s with pc := pc, accu := v, heap := heap, world := world}
      pl cp sp high domain frameSp result env after :=
  { toCcall1Saved := { saved with pc := saved.pc }
    data := payload_pc post.data pc
    primitives := post.primitives
    platform := post.platform
    loop := post.loop
    tick := post.call.tick
    returnPC := post.call.pc
    resultReg := post.call.result
    resultRepr := post.resultRepr }

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
  ccall_primitive_return post saved

/-- Adapt any landed read-only primitive summary to the generated return
boundary. The finite write-set check is an ABI fact, not a primitive proof. -/
theorem ccall_readOnly_summary {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {domain frameSp result env entry ra : BitVec 64} {pc : Nat} {args : List Val} {writes : List Nat} {before : Config}
    (S : FnSummary entry (fun c => c = before)
      (ReadOnlyPost L.runtimeOk P s pl cp sp high name args
        v result writes before ra))
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (saved : Ccall1Saved {s with pc := pc} pl sp domain frameSp env before) :
    FnSummary entry (fun c => c = before)
      (CcallReturn ra L P {s with pc := pc, accu := v}
        pl cp sp high domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after post
  exact ccall_primitive_return post (saved.frame post.call.memory
    (fun r hr => post.call.frame r (preserved r hr) (by revert r; decide)))

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
        pl cp sp high domain frameSp result env) :=
  ccall_readOnly_summary S preserved saved

/-- Restore the stack pointer after dropping the consumed primitive arguments. -/
theorem ccall_return_sp {frameSp : BitVec 64} {sp : Nat}
    (saved : frameSp + 16#64 = BitVec.ofNat 64 sp) (count : Nat) :
    frameSp + BitVec.ofNat 64 (16 + 8 * count) = BitVec.ofNat 64 (sp + 8 * count) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, saved, ← BitVec.ofNat_add]

/-- Shared restoration for every fixed-arity primitive return. Preserve the
returned accumulator as a root, then discard only consumed stack arguments. -/
theorem ccall_return_restore {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high count : Nat} {ra domain frameSp result env : BitVec 64}
    {c after : Config} (stable : MemoryStable L.runtimeOk)
    (h : CcallReturn ra L P s pl cp sp high domain frameSp result env c)
    (bound : count ≤ s.stack.length)
    (regs : VmRegisters {s with stack := s.stack.drop count} pl (sp + 8 * count) after)
    (loop : LoopRegisters after) (good : GoodState after.σ)
    (memory : after.σ.mem = c.σ.mem) (output : after.σ.sailOutput = c.σ.sailOutput) :
    Running L P {s with stack := s.stack.drop count} after :=
  readOnly_restore stable (payload_stack_drop h.data bound) h.primitives h.platform
    regs loop good memory output

end OCaml.Vm.Sim
