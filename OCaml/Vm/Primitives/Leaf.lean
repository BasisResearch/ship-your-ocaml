import OCaml.Vm.Primitives.Register
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
  have S' := register_of_blocks (writes := [10]) image S hlog hpc hresult
    (fun n hn => List.mem_singleton.mpr (hwrites n hn))
  apply S'.weaken (fun _ h => h)
  intro after h
  refine ⟨h.good, h.image, h.minstret, h.tick, h.pc, h.result, h.memory, h.output, ?_⟩
  intro r hr hn
  apply h.frame r _ hn
  intro n hn
  have he : n = 10 := List.mem_singleton.mp hn
  subst n
  exact Ne.symm hr

end OCaml.Vm.Primitives
