import OCaml.Vm.Sim.ModifyReturn

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Arguments and caller registers at the actual caml_modify boundary. -/
structure ModifyArgs (codeReg : Nat) (ra codeWord stackWord slot value : BitVec 64)
    (c : Config) : Prop extends LeafInput ra c where
  entry : pcOf c = some (0x8000a9a8#64)
  code : gpr c codeReg = some codeWord
  stack : gpr c Layout.reg_sp = some stackWord
  slot : gpr c 10 = some slot
  value : gpr c 11 = some value

/-- Read-only setup observations supplied by a generated caller prefix. -/
structure ModifySetup (before : Config) (codeReg : Nat)
    (ra codeWord stackWord slot value : BitVec 64) (c : Config) : Prop
    extends ModifyArgs codeReg ra codeWord stackWord slot value c where
  memory : c.σ.mem = before.σ.mem
  output : c.σ.sailOutput = before.σ.sailOutput
  preserved : ∀ r ∈ consumePreserved, c.σ.regs.get? r = before.σ.regs.get? r

/-- Full represented precondition at the barrier call, before its heap mutation.
The logical stack still includes any operands already popped in registers. -/
structure ModifyInput (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high codeReg : Nat) (ra codeWord stackWord slot value : BitVec 64) (c : Config) : Prop
    extends ModifyArgs codeReg ra codeWord stackWord slot value c where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  runtime : L.runtimeOk c
  loop : LoopRegisters c
  env : ∃ w, gpr c Layout.reg_env = some w ∧ valWord pl s.env = some w
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)

/-- Reconstruct the represented call input once, from the read-only native setup. -/
theorem modify_input {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high codeReg : Nat} {ra codeWord stackWord slot value : BitVec 64} {c after : Config}
    (stable : MemoryStable L.runtimeOk) (data : VmReprAt P s c pl cp sp high)
    (platform : PlatformOk L.runtimeOk c) (loop : LoopRegisters c)
    (post : ModifySetup c codeReg ra codeWord stackWord slot value after) :
    ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord slot value after := by
  refine {
    toModifyArgs := post.toModifyArgs
    data := (payload_of_repr data).frame post.memory post.output
    primitives := data.primitives.frame post.memory
    runtime := stable c after post.memory platform.runtime
    loop := loopRegisters_frame (fun r hr => post.preserved r (by revert r; decide)) loop
    env := ?_, extra := (post.preserved _ (by decide)).trans data.extra }
  obtain ⟨w, reg, value⟩ := data.env
  exact ⟨w, (post.preserved _ (by decide)).trans reg, value⟩

/-- The GC lane supplies the actual barrier summary. Callers instantiate target
with the successful setField? heap update and their consumed logical stack.
The postcondition retains data, runtime and ABI components separately. -/
structure ModifyCallee (L : OCaml.Layout) (P : Prog) (s target : St) (pl : Place) (cp : ChanPlace)
    (sp targetSp high codeReg : Nat) (ra codeWord stackWord slot value : BitVec 64) : Prop where
  summary : FnSummary (0x8000a9a8#64)
    (ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord slot value)
    (ModifyReturn L P target pl cp targetSp high codeReg ra codeWord stackWord)

end OCaml.Vm.Sim
