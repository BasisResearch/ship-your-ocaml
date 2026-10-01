import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Platform

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- A read-only primitive may clobber the listed ABI temporaries. -/
structure RegisterPost (writes : List Nat) (before : Config) (ra value : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ writes, gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Package the segment kernel's complete frame for a read-only callee.
Loads are allowed; the generated certificate proves their concrete accesses. -/
theorem register_of_blocks {bs : List BBlock} {entry : BitVec 64} {before : Config}
    {L : GRegs} {loads : List (List (BitVec 8))} {writes : List Nat}
    {ra value : BitVec 64} (image : ExecutableImage before)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = [])
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes) :
    FnSummary entry (fun c => c = before) (RegisterPost writes before ra value) := by
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
    exact beq_eq_false_iff_ne.mpr (hr n (hwrites n hmem))

end OCaml.Vm.Primitives
