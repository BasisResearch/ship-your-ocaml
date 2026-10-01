import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Platform

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Ordinary ABI/platform requirements for a register-only primitive. -/
structure LeafInput (ra : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  raReg : gprGet c.σ 1 = some ra
  aligned : ra.toNat % 4 = 0
  tick : c.tick < 2

/-- Return value and complete frame of an a0-only primitive. -/
structure LeafPost (before : Config) (ra value : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, r ≠ Register.x10 → (∀ q ∈ noiseRegs, (q == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- One frame/return composition shared by every generated constant leaf.
All four symbolic-evaluation hypotheses are checked from its finite blocks. -/
theorem leaf_of_blocks {bs : List BBlock} {entry : BitVec 64} {before : Config}
    {ra value : BitVec 64} (image : ExecutableImage before)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry [(1, ra)] [] before))
    (hlog : (evalBlocks bs (SegEvalState.init [(1, ra)] [])).log = [])
    (hpc : evalBlocksPC entry (SegEvalState.init [(1, ra)] []) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init [(1, ra)] [])).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n = 10) :
    FnSummary entry (fun c => c = before) (LeafPost before ra value) := by
  apply S.weaken (fun _ h => h)
  intro after h
  have hm : after.σ.mem = before.σ.mem := by simpa [hlog, writeLog] using h.memory
  refine ⟨h.good, ?_, h.minstret, h.tick, ?_, hresult _ h.regs, hm, h.output, ?_⟩
  · exact ⟨fun i hi => by rw [hm]; exact image.text i hi,
      fun i hi => by rw [hm]; exact image.rodata i hi⟩
  · exact h.pc.trans (congrArg some hpc)
  · intro r hr hn
    apply h.frame r hn
    intro n hmem
    rw [hwrites n hmem]
    simpa only [gprReg, beq_eq_false_iff_ne] using Ne.symm hr

end OCaml.Vm.Primitives
