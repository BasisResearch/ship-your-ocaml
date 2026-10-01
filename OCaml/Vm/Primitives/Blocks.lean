import Vsa.Sim.FnSummary
import Vsa.Sim.SegEvalSound

/-! Shared whole-function packaging for the generated primitive blocks.
The segment kernel supplies execution and frames; this layer only gives its
result named fields and the `FnSummary` interface used by call splices. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

structure BlockInput (bs : List BBlock) (entry : BitVec 64) (L : GRegs)
    (loads : List (List (BitVec 8))) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  regs : GHolds c.σ L
  keys : KeysOK (keysG L)
  facts : ChainFacts c.σ.mem c.σ.mem L loads bs
  shape : ChainOK entry (keysG L) bs
  tick : c.tick < 2

structure BlockPost (bs : List BBlock) (entry : BitVec 64) (L : GRegs)
    (loads : List (List (BitVec 8))) (before after : Config) : Prop where
  tick : after.tick < 2
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem (evalBlocks bs (SegEvalState.init L loads)).log
  output : after.σ.sailOutput = before.σ.sailOutput
  pc : after.σ.regs.get? Register.PC = some (evalBlocksPC entry (SegEvalState.init L loads) bs)
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  regs : GHolds after.σ (evalBlocks bs (SegEvalState.init L loads)).regs
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ wrChain bs, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- The input certificate is discharged by generated code pins, decode facts,
operand facts and finite structural checks. It is not a run premise. -/
theorem block_summary (bs : List BBlock) (entry : BitVec 64) (L : GRegs)
    (loads : List (List (BitVec 8))) (before : Config)
    (h : BlockInput bs entry L loads before) :
    FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before) := by
  constructor
  rintro c ⟨hpc, rfl⟩
  obtain ⟨v, hv⟩ := h.minstret
  obtain ⟨σ', tick', hs, ht, hg, hm, ho, hp, hi, hr, hf⟩ :=
    segEval_sound bs c.σ c.tick c.steps entry v L loads h.good hpc hv h.regs h.keys
      h.facts h.shape h.tick
  exact ⟨⟨σ', tick', c.steps + evalBlocksFuel bs⟩, hs, ⟨ht, hg, hm, ho, hp, hi, hr, hf⟩⟩

end OCaml.Vm.Primitives
