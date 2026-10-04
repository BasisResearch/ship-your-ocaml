import OCaml.Vm.Boot.Startup.FindUnlockNormalized
import OCaml.Vm.Boot.Startup.FindUnlockCallInterface
import OCaml.Vm.Boot.Startup.EnvLock
import OCaml.Vm.Boot.Startup.LeafCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def findUnlockInput (stack reent : BitVec 64) : GRegs := [(21, reent), (2, stack)]
def findUnlockRegs (stack reent : BitVec 64) : GRegs := [(10, reent), (21, reent), (2, stack)]

theorem findUnlock_input {stack reent ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findUnlockInput stack reent)) :
    BlockInput findenv_rX74f4Seg 0x800374f4#64 (findUnlockInput stack reent) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [21, 2]; decide
  shape := by change ChainOK _ [21, 2] _; decide
  tick := leaf.tick
  facts := by
    have code := findUnlock_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"

/-- Select the caller's reentrancy argument before releasing the environment lock. -/
theorem find_unlock_prefix (c : Config) (stack reent ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findUnlockInput stack reent)) :
    FnSummary 0x800374f4#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c jal_800374f8_call.pc reent (findUnlockRegs stack reent)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findUnlock_input leaf regs))
  · rfl
  · rfl
  · change [(10, reent + 0#64), (21, reent), (2, stack)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · decide

/-- The not-found path releases the environment lock and reaches its epilogue. -/
theorem find_unlock (c : Config) (stack reent ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findUnlockInput stack reent)) :
    FnSummary 0x800374f4#64 (fun d => d = c)
      (WriteRegistersPost [10, 1, 10] [] c jal_800374f8_call.link (envLockValue true)
        [(10, envLockValue true), (1, jal_800374f8_call.link), (21, reent), (2, stack)]) := by
  apply summary_bind (find_unlock_prefix c stack reent ra leaf regs) (fun _ post => post.pc)
  intro mid prepared
  have leaf' : LeafInput ra mid :=
    ⟨prepared.good, prepared.image, prepared.minstret,
      (prepared.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, prepared.tick⟩
  have call := scalar_leaf_call jal_800374f8_call jal_800374f8_call_shape jal_800374f8_call_decode
    (envLockValue true) mid ra reent leaf' (jal_800374f8_call_pins prepared.image)
    [(21, reent), (2, stack)] prepared.regs
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by simp only [keysG]; decide) (by simp only [keysG]; decide) (by decide)
    (fun state h => env_lock true state _ h)
  apply call.weaken (fun _ eq => eq)
  intro after post
  exact prefix_readonly_post prepared post
end OCaml.Vm.Boot.Startup
