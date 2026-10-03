import OCaml.Vm.Sim.Muldi3
import OCaml.Vm.Sim.MulArithmetic
import OCaml.Vm.Sim.StackConsume
import OCaml.Vm.Sim.MulintSuffixSegment
import OCaml.Vm.Sim.MulintSuffixPins
import Vsa.Sim.DeriveCallSeg

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Caller observations retained while libgcc computes the product. -/
structure MulintFrame (before : Config) (pl : Place) (pc sp : Nat) (c : Config) : Prop where
  nextCode : gpr c 23 = some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  stack : gpr c Layout.reg_sp = some (BitVec.ofNat 64 sp)
  memory : c.σ.mem = before.σ.mem
  output : c.σ.sailOutput = before.σ.sailOutput
  preserved : ∀ r ∈ consumePreserved, c.σ.regs.get? r = before.σ.regs.get? r

/-- Represented caller state at the generated direct-call boundary. -/
structure MulintCall (before : Config) (pl : Place) (pc sp : Nat)
    (m n : BitVec 63) (c : Config) : Prop
    extends Muldi3Input ((tag64 n).sshiftRight 1) ((tag64 m).sshiftRight 1) 0x80002d4c#64 c,
      MulintFrame before pl pc sp c where
  calleePC : pcOf c = some 0x80037234#64

/-- Native product and caller frame at the generated return boundary. -/
structure MulintReturn (before : Config) (pl : Place) (pc sp : Nat)
    (m n : BitVec 63) (c : Config) : Prop
    extends LeafInput 0x80002d4c#64 c, MulintFrame before pl pc sp c where
  returnPC : pcOf c = some 0x80002d4c#64
  result : gpr c 10 = some ((tag64 n).sshiftRight 1 * (tag64 m).sshiftRight 1)

/-- Preserve caller observations through the proved total multiplication call. -/
theorem mulint_callee {before : Config} {pl : Place} {pc sp : Nat} {m n : BitVec 63} :
    Vsa.Logic.Triple (MulintCall before pl pc sp m n) (MulintReturn before pl pc sp m n) := by
  intro c h
  obtain ⟨after, run, post⟩ := (muldi3_summary h.toMuldi3Input).run c ⟨h.calleePC, rfl⟩
  refine ⟨after, run, post.toLeafInput, ?_, post.pc, post.result⟩
  exact ⟨(post.frame Register.x23 (by decide)).trans h.nextCode,
    (post.frame Register.x9 (by decide)).trans h.stack,
    post.memory.trans h.memory, post.output.trans h.output,
    fun r hr => (post.frame r (by revert r; decide)).trans (h.preserved r hr)⟩

/-- Retag the libgcc result and restore the interpreter loop observations. -/
theorem mulint_return {before : Config} {pl : Place} {pc sp : Nat} {m n : BitVec 63} :
    Vsa.Logic.Triple (MulintReturn before pl pc sp m n) (ConsumePost before pl pc sp (m * n)) := by
  intro c h
  have bp : SegSt (0x80002d4c#64)
      [⟨Register.x10, (tag64 n).sshiftRight 1 * (tag64 m).sshiftRight 1⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * pc)⟩]
      (fun σ => Vsa.Sim.Code.CamlMulintSuffixLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.returnPC, ⟨h.result, h.nextCode, trivial⟩,
      h.minstret, h.tick, mulint_suffix_loaded h.image, rfl, rfl⟩
  obtain ⟨_, after, _, run, post⟩ := tr_mulint_suffix _ _ c.σ.mem c.σ c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨after, run.toSteps, post.good, post.pcAt, ?_,
    (frame.frame Register.x9 (by decide)).trans h.stack, ?_,
    memory.trans h.memory, frame.out.trans h.output,
    fun r hr => (frame.frame r (by revert r; decide)).trans (h.preserved r hr)⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * pc) + Functions.sign_extend (0x000#12)) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    simpa only [show Functions.sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero] using hp
  · have hp : gpr after Layout.reg_accu = some
        ((((tag64 n).sshiftRight 1 * (tag64 m).sshiftRight 1) <<< 1) + 1#64) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [tag_mul_native] using hp

end OCaml.Vm.Sim
