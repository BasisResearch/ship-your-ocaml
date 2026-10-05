import OCaml.Vm.Sim.RestartInput
import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.RestartSuffixSegment
import OCaml.Vm.Sim.RestartSuffixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The generated suffix restores the captured environment and extra count
after the proved saved-argument loop. -/
theorem restart_finish {L : OCaml.Layout} {P : Prog} {s : St} {c middle d : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a tag : Nat} {fields : List Val} {env : Val}
    (stable : WindowStable L.runtimeOk [⟨restartStart sp fields, sp⟩])
    (h : ArmInput L P s .RESTART c pl cp sp high)
    (block : BlockSelection s.heap pl s.env l a tag fields) (environment : fields[2]? = some env)
    (space : RestartInput P s c pl cp sp high a fields)
    (front : RestartCopyStart c sp a (pl.codeBase + 4 * (s.pc + 1)) fields middle)
    (copied : ForwardCopyAt a (restartStart sp fields) (stackWords c (a + 24) (fields.length - 3)) middle
      (stackWords c (a + 24) (fields.length - 3)).length d) :
    ∃ nb after, StepsN nb d after ∧ Running L P (restartState s fields env) after := by
  have written : d.σ.mem = writeLog c.σ.mem (restartLog c sp a fields) := by
    rw [copied.memory, forward_copy_log_complete, front.memory]; rfl
  have extra : gpr d 18 = some (BitVec.ofNat 64 s.extra) :=
    (copied.frame.frame Register.x18 (by decide)).trans ((front.frame.frame Register.x18 (by decide)).trans h.extra)
  have countReg : gpr d 11 = some (BitVec.ofNat 64 (fields.length - 3)) :=
    (copied.frame.frame Register.x11 (by decide)).trans front.extraCount
  have nextReg : gpr d 23 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) :=
    (copied.frame.frame Register.x23 (by decide)).trans front.nextCode
  have spReg : gpr d 9 = some (BitVec.ofNat 64 (restartStart sp fields)) :=
    (copied.frame.frame Register.x9 (by decide)).trans front.spReg
  have loop : LoopRegisters d := loopRegisters_frame (fun r hr =>
    (copied.frame.frame r (by revert r; decide)).trans (front.frame.frame r (by revert r; decide))) h.dispatch.loop
  have field := block.field environment
  have rawRead := space.payload.env_field_load (payload_of_repr h.toVmReprAt) field written
  have envRead : sign_extend (m := 64) (bytesT8 d.σ.mem (a + 16)) = word c (a + 16) :=
    rawRead
  have envWord : valWord pl env = some (word c (a + 16)) :=
    (field.read h.toVmReprAt (by simp [roots])).word
  have address : BitVec.ofNat 64 a + sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 (a + 16) := by
    rw [show sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 16 from by decide, ← BitVec.ofNat_add]
  have bp : SegSt (0x80002bb0#64)
      [⟨Register.x25, BitVec.ofNat 64 a⟩, ⟨Register.x18, BitVec.ofNat 64 s.extra⟩,
       ⟨Register.x11, BitVec.ofNat 64 (fields.length - 3)⟩, ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))⟩]
      (fun σ => Vsa.Sim.Code.CamlRestartSuffixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨copied.good, by change pcOf d = some (0x80002bb0#64); simpa only [Nat.lt_irrefl, ite_false] using copied.pc,
      ⟨copied.sourceReg, extra, countReg, nextReg, trivial⟩,
      copied.good.minstret, copied.tick, restart_suffix_loaded copied.image, rfl, rfl⟩
  have run := tr_restart_suffix (BitVec.ofNat 64 a) (BitVec.ofNat 64 s.extra)
    (BitVec.ofNat 64 (fields.length - 3)) (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) d.σ.mem d.σ
  simp only [address, space.envRead.toNat, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, ← BitVec.ofNat_add] at run
  obtain ⟨nb, after, _, steps, post⟩ := run space.envRead.lower space.envRead.upper space.envRead.htif
    (word c (a + 16)) envRead.symm d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have observations : RestartPost c s pl sp a fields env after := by
    refine ⟨⟨post.pcAt, PinsHold.get post.pins ⟨0, by simp⟩,
      (frame.frame Register.x9 (by decide)).trans spReg, ?_,
      ⟨_, PinsHold.get post.pins ⟨2, by simp⟩, envWord⟩, PinsHold.get post.pins ⟨1, by simp⟩⟩,
      post.good, memory.trans written, frame.out.trans (copied.frame.out.trans front.frame.out), ?_,
      ((frame.frame (gprReg 2) (by decide)).trans ((copied.frame.frame (gprReg 2) (by decide)).trans (front.frame.frame (gprReg 2) (by decide))))⟩
    · obtain ⟨w, reg, value⟩ := h.accu
      exact ⟨w, (frame.frame Register.x21 (by decide)).trans
        ((copied.frame.frame Register.x21 (by decide)).trans ((front.frame.frame Register.x21 (by decide)).trans reg)), value⟩
    · exact loopRegisters_frame (fun r hr => frame.frame r (by revert r; decide)) loop
  exact ⟨nb, after, steps, restart_restore stable h.toVmReprAt h.running.platform block environment space.toRestartWriteOk observations h.geometry h.native⟩

end OCaml.Vm.Sim
