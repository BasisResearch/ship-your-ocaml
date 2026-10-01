import Vsa.Sim.SegEvalSound
import Vsa.Sim.BlockAdapter
import Vsa.Sim.DeriveCase

/-!
# Generated segment to machine triple

Port of `Vsa/Sim/DeriveCaseRow.lean` from ship-your-interpreter, source
commit d3be8dc07d15b806281966b6d0bdc96885f84076 (syi-refine checkout).
The generated row API is retained; SegPre has named fields, the unused
FrameCalc import and concrete demo are omitted, and no elaboration budget
is raised. This is the adapter imported by scripts/syi/gen_fn.py.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- The hypotheses consumed by the reflected segment's soundness theorem. -/
structure SegPre (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  memory : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some pc0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  registers : GHolds c.σ L
  keys : KeysOK (keysG L)
  facts : ChainFacts c.σ.mem c.σ.mem L lds bs
  tick : c.tick < 2

/-- Marshal a reflected segment's computed outcome into the caller's post.
Instruction execution is supplied by segEval_sound, not re-proved here. -/
theorem segToTriple (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hpost : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      Q ⟨σ', i', u'⟩) :
    Triple (SegPre bs L lds pc0 m0) Q := by
  intro c pre
  obtain ⟨vm, hmi⟩ := pre.minstret
  obtain ⟨σ', i', hs, hi', hG', hmem', _, hpc', hmi', hregs, _⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds pre.good pre.pc hmi
      pre.registers pre.keys pre.facts hwf pre.tick
  rw [pre.memory] at hmem'
  exact ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs,
    hpost σ' i' (c.steps + evalBlocksFuel bs) hG' hi' hmem' hpc' hmi' hregs⟩

end Vsa.Sim
