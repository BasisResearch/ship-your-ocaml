import OCaml.Vm.Sim.StackConsume

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Represented barrier result and caller registers at its native return.
The caml_modify summary must supply the heap update, runtime invariant and
primitive-table frame. The generated caller suffix supplies loop re-entry.
Data uses the final logical stack; the physical stack register can still
point to the arguments that the suffix consumes. -/
structure ModifyReturn (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high codeReg : Nat) (ra codeWord stackWord : BitVec 64) (c : Config) : Prop where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  platform : PlatformOk L.runtimeOk c
  loop : LoopRegisters c
  tick : c.tick < 2
  returnPC : pcOf c = some ra
  code : gpr c codeReg = some codeWord
  stack : gpr c Layout.reg_sp = some stackWord
  env : ∃ w, gpr c Layout.reg_env = some w ∧ valWord pl s.env = some w
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)
  unit : s.accu = .unit
  /-- the VM stack geometry after the barrier (`Invariant.lean`) -/
  geometry : StackGeometry P s c pl cp high
  /-- the native invocation after the barrier (`Invocation.lean`) -/
  native : NativePlaced c

/-- One restoration rule for all write-barrier caller suffixes. -/
theorem modify_return_restore {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high codeReg : Nat} {ra codeWord stackWord : BitVec 64} {c after : Config}
    (stable : MemoryStable L.runtimeOk)
    (h : ModifyReturn L P s pl cp sp high codeReg ra codeWord stackWord c)
    (post : StackPost c pl s.pc sp (tag64 0) c.σ.mem after) : Running L P s after := by
  apply readOnly_restore stable h.data h.primitives h.platform ?_ ?_ post.good post.memory post.output
    (h.geometry.state rfl rfl) h.native post.nativeSp
  · refine ⟨post.head, post.code, post.stack, ⟨tag64 0, post.accu, ?_⟩, ?_, ?_⟩
    · rw [h.unit]; rfl
    · obtain ⟨w, reg, value⟩ := h.env
      exact ⟨w, (post.preserved _ (by decide)).trans reg, value⟩
    · exact (post.preserved _ (by decide)).trans h.extra
  · exact loopRegisters_frame (fun r hr => post.preserved r (by revert r; decide)) h.loop

end OCaml.Vm.Sim
