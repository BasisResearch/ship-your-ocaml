import OCaml.Vm.Sim.ReturnPayload
import OCaml.Vm.Sim.ReturnArithmetic
import OCaml.Vm.Sim.FieldRead
import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Sim.ReadGeometry
import OCaml.Vm.Sim.ReturnMoreSegment
import OCaml.Vm.Sim.ReturnMorePins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- RETURN with extra arguments enters its closure after dropping the consumed
arguments, reusing represented root restoration and the generated native path. -/
theorem return_more_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k dest : Nat} {count : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .RETURN c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) count) (nonnegative : 0 ≤ count.toInt)
    (bound : count.toInt.toNat ≤ s.stack.length) (positive : 0 < s.extra) (small : s.extra < 2^63)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := dest, env := s.accu, extra := s.extra - 1, stack := s.stack.drop count.toInt.toNat} after := by
  have source := represented_register h.accu field.sourceWord
  have fieldWord : word c (a + 8 * k) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) :=
    (Option.some.inj (field.read h.toVmReprAt (by simp [roots])).word).symm
  apply dispatch_compose h.dispatch
  intro d dp
  have read := operand.read32 h.code dp.memory
  have closureRead : sign_extend (m := 64) (bytesT8 d.σ.mem (a + 8 * k)) =
      BitVec.ofNat 64 (pl.codeBase + 4 * dest) :=
    (word_read_writeLog_out (log := []) trivial dp.memory).trans fieldWord
  have bp : SegSt (0x80002b1c#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩, ⟨Register.x18, BitVec.ofNat 64 s.extra⟩,
       ⟨Register.x21, BitVec.ofNat 64 (a + 8 * k)⟩]
      (fun σ => Vsa.Sim.Code.CamlReturnMoreLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x9 (by decide)).trans h.spReg,
      (dp.frame.frame Register.x18 (by decide)).trans h.extra,
      (dp.frame.frame Register.x21 (by decide)).trans source, trivial⟩,
      dp.good.minstret, dp.tick, return_more_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_return_more (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp)
    (BitVec.ofNat 64 s.extra) (BitVec.ofNat 64 (a + 8 * k)) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, codePc_succ, operand.geometry.toNat, read, geometry.toNat] at run
  obtain ⟨nb, after, _, steps, post⟩ := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (sign_extend (m := 64) count) rfl (return_more_guard s.extra positive small)
    geometry.lower geometry.upper geometry.htif (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) closureRead.symm d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have payload := return_payload (payload_of_repr h.toVmReprAt) bound
    (show ∀ l, s.accu.loc? = some l → Live s.heap (roots P s) l from fun _ loc => Live.root (by simp [roots]) loc)
    (pc := dest) (extra := s.extra - 1)
  have regs : VmRegisters
      {s with pc := dest, env := s.accu, extra := s.extra - 1, stack := s.stack.drop count.toInt.toNat}
      pl (sp + 8 * count.toInt.toNat) after := by
    refine ⟨post.pcAt, PinsHold.get post.pins ⟨2, by simp⟩, ?_,
      ⟨_, PinsHold.get post.pins ⟨5, by simp⟩, field.sourceWord⟩,
      ⟨_, PinsHold.get post.pins ⟨0, by simp⟩, field.sourceWord⟩, ?_⟩
    · have stack : gpr after Layout.reg_sp = some (BitVec.ofNat 64 sp +
          Sail.shift_bits_left (sign_extend (m := 64) count) (Sail.BitVec.extractLsb (0x03#6) 5 0)) :=
        PinsHold.get post.pins ⟨3, by simp⟩
      simpa only [index_word count nonnegative, BitVec.ofNat_add] using stack
    · have extra : gpr after Layout.reg_extra = some
          (BitVec.ofNat 64 s.extra + sign_extend (m := 64) (0xfff#12)) := PinsHold.get post.pins ⟨1, by simp⟩
      simpa only [extra_decrement s.extra positive] using extra
  refine ⟨nb, after, steps, ?_⟩
  exact readOnly_restore stable payload h.primitives h.running.platform regs
    (loopRegisters_frame (fun r hr => (frame.frame r (by revert r; decide)).trans
      (dp.frame.frame r (by revert r; decide))) h.dispatch.loop)
    post.good (memory.trans dp.memory) (frame.out.trans dp.frame.out)
    (h.geometry.state rfl rfl) h.native
    ((frame.frame (gprReg 2) (by decide)).trans (dp.frame.frame (gprReg 2) (by decide)))

end OCaml.Vm.Sim
