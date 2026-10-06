import OCaml.Vm.Sim.MulintCall
import OCaml.Vm.Sim.BinarySemantics
import OCaml.Vm.Sim.MulintPrefixSegment
import OCaml.Vm.Sim.MulintPrefixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

abbrev MulintScratch := BinaryLibScratch

/-- The generated five-step prefix establishes the exact libgcc call boundary. -/
theorem mulint_setup {L : OCaml.Layout} {P : Prog} {s : OCaml.Bytecode.St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {m n : BitVec 63} {rest : List Val}
    (h : ArmInput L P s .MULINT c pl cp sp high)
    (accu : s.accu = .int m) (stack : s.stack = .int n :: rest)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8)
    (dp : DispatchPost c .MULINT (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ nb after, StepsN nb d after ∧ MulintCall d pl (s.pc + 1) (sp + 8) m n after := by
  have source := represented_register h.accu (by rw [accu]; rfl : valWord pl s.accu = some (tag64 m))
  have slot := stack_integer_word h.toVmReprAt stack
  have selected : s.stack[0]? = some (.int n) := by simp only [stack, List.getElem?_cons_zero]
  have natAddress : (BitVec.ofNat 64 sp).toNat = sp := by
    simpa only [Nat.mul_zero, Nat.add_zero] using stack_slot_nat h.toVmReprAt selected
  have loaded : sign_extend (m := 64) (bytesT8 d.σ.mem (BitVec.ofNat 64 sp).toNat) = tag64 n := by
    simpa only [natAddress, dp.memory, word, bytesT_eight_eq, sign_extend,
      Sail.BitVec.signExtend, BitVec.signExtend_eq] using slot
  have bp : SegSt (0x80002d38#64)
      [⟨Register.x9, BitVec.ofNat 64 sp⟩, ⟨Register.x21, tag64 m⟩]
      (fun σ => Vsa.Sim.Code.CamlMulintPrefixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x9 (by decide)).trans h.spReg,
        (dp.frame.frame Register.x21 (by decide)).trans source, trivial⟩,
      dp.good.minstret, dp.tick, mulint_prefix_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_mulint_prefix (BitVec.ofNat 64 sp) (tag64 m) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, loaded] at run
  obtain ⟨nb, after, _, steps, post⟩ := run read.lower read.upper read.htif d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have image : ExecutableImage after :=
    ⟨by simpa only [memory] using (dp.image h.dispatch.image).text,
     by simpa only [memory] using (dp.image h.dispatch.image).rodata⟩
  refine ⟨nb, after, steps, ?_, ?_, post.pcAt⟩
  · exact ⟨⟨post.good, image, post.good.minstret, PinsHold.get post.pins ⟨0, by simp⟩,
      by decide, post.tick⟩, PinsHold.get post.pins ⟨1, by simp⟩,
      PinsHold.get post.pins ⟨3, by simp⟩⟩
  · refine ⟨?_, ?_, memory, frame.out, fun r hr => frame.frame r (by revert r; decide)⟩
    · have hp : gpr after 23 = some
          (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) :=
        (frame.frame Register.x23 (by decide)).trans dp.nextCode
      simpa only [codePc_succ] using hp
    · have hp : gpr after Layout.reg_sp = some
          (BitVec.ofNat 64 sp + sign_extend (m := 64) (0x008#12)) :=
        PinsHold.get post.pins ⟨2, by simp⟩
      simpa only [show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
        BitVec.ofNat_add] using hp

end OCaml.Vm.Sim
