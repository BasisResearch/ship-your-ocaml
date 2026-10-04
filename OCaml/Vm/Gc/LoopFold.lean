import Vsa.Sim.DeriveLoop
import Vsa.Sim.FnSummary

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Vsa.Logic

/-- Shared PC-guarded loop adapter for collector invariants with distinct
active and returned states. The body is a proved concrete iteration; all
iteration/termination algebra delegates to the machine loop kernel. -/
theorem loop_to_exit {entry : BitVec 64} {active finished : Config → Prop} (rank : Config → Nat)
    (activePc : ∀ c, active c → PCAt entry c)
    (finishedPc : ∀ c, finished c → ¬ PCAt entry c)
    (body : ∀ c, active c → ∃ after, Steps c after ∧ (active after ∨ finished after) ∧ rank after < rank c) :
    Triple active finished := by
  let Inv := fun c => active c ∨ finished c
  let Branch := fun c => PCAt entry c
  have iteration : ∀ n, Triple (fun c => Inv c ∧ Branch c ∧ rank c = n)
      (fun c => Inv c ∧ rank c < n) := by
    intro n c pre
    rcases pre with ⟨state,pc,equal⟩
    rcases state with state | state
    · obtain ⟨after,run,post,less⟩ := body c state
      exact ⟨after,run,post,by omega⟩
    · exact False.elim (finishedPc c state pc)
  apply (loopFromBody (I := Inv) (B := Branch) rank iteration).conseq
  · intro c state
    exact Or.inl state
  · intro c post
    rcases post with ⟨state,offHead⟩
    rcases state with state | state
    · exact False.elim (offHead (activePc c state))
    · exact state

end OCaml.Vm.Gc
