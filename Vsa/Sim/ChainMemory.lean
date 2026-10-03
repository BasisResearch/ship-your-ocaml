import Vsa.Sim.SegEval

namespace Vsa.Sim

/-- The existing per-block store policy lifts to a finite chain. All ordinary
stores are above HTIF, so bytes below HTIF keep their original values. -/
theorem memChain_low {mc m L lds bs} (facts : ChainFacts mc m L lds bs)
    (a : Nat) (low : a < tohostAddr) : (memChain bs m L lds)[a]? = m[a]? := by
  induction bs generalizing m L lds with
  | nil => rfl
  | cons b bs ih =>
      exact (ih facts.2).trans (writeLog_wlog_low_bt mc b.body m L lds facts.1.1 a low)

/-- Code frames follow from the actual scalar store obligations, independently
of the symbolic values stored. No extra disjointness premise is needed. -/
theorem evalBlocks_low {mc m L lds bs} (facts : ChainFacts mc m L lds bs)
    (a : Nat) (low : a < tohostAddr) :
    (writeLog m (evalBlocks bs (SegEvalState.init L lds)).log)[a]? = m[a]? := by
  rw [writeLog_evalBlocks_init]
  exact memChain_low facts a low

end Vsa.Sim
