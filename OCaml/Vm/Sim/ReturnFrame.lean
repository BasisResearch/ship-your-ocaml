import OCaml.Vm.Sim.ReturnRead
import OCaml.Vm.Sim.IndexWord
import OCaml.Vm.Sim.SwitchArithmetic
import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Sim.ReturnFrameSegment
import OCaml.Vm.Sim.ReturnFramePins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- RETURN without extra arguments restores its represented saved caller frame.
The saved extra count is nonnegative, as supplied by well-formed return frames. -/
theorem return_frame_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {count : BitVec 32}
    {env : Val} {extra : BitVec 63} {rest : List Val}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .RETURN c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) count) (nonnegative : 0 ≤ count.toInt)
    (noExtra : s.extra = 0) (savedNonnegative : 0 ≤ extra.toInt)
    (stack : s.stack.drop count.toInt.toNat = .code dest :: env :: .int extra :: rest)
    (reads : ReturnFrameReads (sp + 8 * count.toInt.toNat)) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := dest, env := env, extra := extra.toNat, stack := s.stack.drop (count.toInt.toNat + 3)} after := by
  have saved := return_frame_values (payload_of_repr h.toVmReprAt) stack
  have bound : count.toInt.toNat + 3 ≤ s.stack.length := by
    have len := congrArg List.length stack
    simp only [List.length_drop, List.length_cons] at len
    omega
  obtain ⟨accu, accuReg, accuWord⟩ := h.accu
  have baseAddress : BitVec.ofNat 64 sp + BitVec.ofNat 64 (8 * count.toInt.toNat) =
      BitVec.ofNat 64 (sp + 8 * count.toInt.toNat) := (BitVec.ofNat_add _ _).symm
  have envAddress : BitVec.ofNat 64 (sp + 8 * count.toInt.toNat) + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (sp + 8 * count.toInt.toNat + 8) := by simp only [BitVec.ofNat_add]; rfl
  have extraAddress : BitVec.ofNat 64 (sp + 8 * count.toInt.toNat) + sign_extend (m := 64) (0x010#12) =
      BitVec.ofNat 64 (sp + 8 * count.toInt.toNat + 16) := by simp only [BitVec.ofNat_add]; rfl
  apply dispatch_compose h.dispatch
  intro d dp
  have read := operand.read32 h.code dp.memory
  have load (a : Nat) : sign_extend (m := 64) (bytesT8 d.σ.mem a) = word c a :=
    word_read_writeLog_out (log := []) trivial dp.memory
  have bp : SegSt (0x80002b1c#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩, ⟨Register.x18, 0#64⟩]
      (fun σ => Vsa.Sim.Code.CamlReturnFrameLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x9 (by decide)).trans h.spReg,
      by simpa only [noExtra] using (dp.frame.frame Register.x18 (by decide)).trans h.extra, trivial⟩,
      dp.good.minstret, dp.tick, return_frame_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_return_frame (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) 0#64 d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, codePc_succ, operand.geometry.toNat, read] at run
  have run1 := run operand.geometry.lower operand.geometry.upper operand.geometry.htif (sign_extend (m := 64) count) rfl (by decide)
  simp only [index_word count nonnegative, baseAddress, envAddress, extraAddress,
    reads.code.toNat, reads.environment.toNat, reads.extraArgs.toNat] at run1
  obtain ⟨nb, after, _, steps, post⟩ := run1 reads.extraArgs.lower reads.extraArgs.upper reads.extraArgs.htif
    (tag64 extra) ((load _).trans saved.extraArgs).symm
    reads.code.lower reads.code.upper reads.code.htif (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) ((load _).trans saved.code).symm
    reads.environment.lower reads.environment.upper reads.environment.htif
    (word c (sp + 8 * count.toInt.toNat + 8)) (load _).symm d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have payload := return_payload (payload_of_repr h.toVmReprAt) bound saved.root (pc := dest) (extra := extra.toNat)
  have regs : VmRegisters
      {s with pc := dest, env := env, extra := extra.toNat, stack := s.stack.drop (count.toInt.toNat + 3)}
      pl (sp + 8 * (count.toInt.toNat + 3)) after := by
    refine ⟨post.pcAt, PinsHold.get post.pins ⟨3, by simp⟩, ?_,
      ⟨accu, (frame.frame Register.x21 (by decide)).trans ((dp.frame.frame Register.x21 (by decide)).trans accuReg), accuWord⟩,
      ⟨_, PinsHold.get post.pins ⟨2, by simp⟩, saved.environment⟩, ?_⟩
    · have moved : gpr after Layout.reg_sp = some
          (BitVec.ofNat 64 (sp + 8 * count.toInt.toNat) + sign_extend (m := 64) (0x018#12)) :=
        PinsHold.get post.pins ⟨0, by simp⟩
      simpa only [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 (8 * 3) from by decide,
        BitVec.ofNat_add, Nat.mul_add, ← Nat.add_assoc] using moved
    · have untagged : gpr after Layout.reg_extra = some
          (shift_bits_right_arith (tag64 extra) (Sail.BitVec.extractLsb (0x01#6) 5 0)) := PinsHold.get post.pins ⟨1, by simp⟩
      simpa only [longVal_native, longVal_nonnegative extra savedNonnegative] using untagged
  refine ⟨nb, after, steps, ?_⟩
  exact readOnly_restore stable payload h.primitives h.running.platform regs
    (loopRegisters_frame (fun r hr => (frame.frame r (by revert r; decide)).trans
      (dp.frame.frame r (by revert r; decide))) h.dispatch.loop)
    post.good (memory.trans dp.memory) (frame.out.trans dp.frame.out)
    (h.geometry.state rfl rfl) h.native
    ((frame.frame (gprReg 2) (by decide)).trans (dp.frame.frame (gprReg 2) (by decide)))

end OCaml.Vm.Sim
