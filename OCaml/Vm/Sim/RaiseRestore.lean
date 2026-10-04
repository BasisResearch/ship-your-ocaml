import OCaml.Vm.Sim.RaiseFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Native handler/loop observations, separate from the represented memory. -/
structure RaisePost (before : Config) (pl : Place) (s : St) (sp high trap : Nat) (after : Config) : Prop where
  good : GoodState after.σ
  registers : VmRegisters s pl sp after
  loop : LoopRegisters after
  memory : after.σ.mem = writeLog before.σ.mem (trapLog (word before Layout.sym_Caml_state).toNat high trap)
  output : after.σ.sailOutput = before.σ.sailOutput

/-- Restore the handler's environment, extra arguments and surviving stack
alongside the written previous trap pointer. -/
theorem raise_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    (stable : WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (data : VmPayload P s c pl cp sp high) (bindings : PrimitiveBindings P c)
    (platform : PlatformOk L.runtimeOk c)
    (frame : RaiseFrame s dest link env extra rest)
    (space : TrapWriteOk P s c pl cp sp high (s.trap - link.toNat))
    (post : RaisePost c pl {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat}
      (sp + 8 * (s.stack.length - s.trap + 4)) high (s.trap - link.toNat) after) :
    Running L P {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat} after := by
  have payload := payload_trap_written data space.highNat space.payload post.memory post.output
  have saved := frame.values data
  have entered := return_payload payload frame.count_bound saved.root (pc := dest) (extra := extra.toNat)
  have restored : VmPayload P {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat}
      after pl cp (sp + 8 * (s.stack.length - s.trap + 4)) high := by
    simpa only [frame.drop_rest] using entered
  have memoryFrame : FrameOn [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩] c.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simp only [trapLog, LogInW, InsideW, or_false, and_true]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  exact running_of_payload restored (bindings_frame_log bindings space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable c after memoryFrame platform.runtime⟩ post.registers post.loop

end OCaml.Vm.Sim
