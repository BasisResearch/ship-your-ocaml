import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.FnSummary

namespace Vsa.Sim
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

/-- Exact reflected effects shared by generated concatenations of segments. -/
structure SegmentPost (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  memory : c.σ.mem = writeLog mem (evalBlocks bs (SegEvalState.init L lds)).log
  pc : c.σ.regs.get? LeanRV64DExecutable.Register.PC =
    some (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? LeanRV64DExecutable.Register.minstret = some w
  registers : GHolds c.σ (evalBlocks bs (SegEvalState.init L lds)).regs

/-- Concatenate generated blocks under one ChainOK certificate. Calls and
loops still use their respective summary rules; this rule adds no run premise. -/
theorem segmentSummary (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8))
    (checked : ChainOK pc0 (keysG L) bs) :
    FnSummary pc0 (SegPre bs L lds pc0 mem) (SegmentPost bs L lds pc0 mem) := by
  refine ⟨Triple.lmap (fun _ h => h.2) ?_⟩
  apply segToTriple bs L lds pc0 mem (SegmentPost bs L lds pc0 mem) checked
  intro σ tick count good tickBound memory atPC minstret registers
  exact ⟨good, memory, atPC, tickBound, minstret, registers⟩

end Vsa.Sim
