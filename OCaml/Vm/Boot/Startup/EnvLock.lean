import OCaml.Vm.Boot.Startup.EnvLockRows
import OCaml.Vm.Boot.Startup.EnvUnlockRows
import OCaml.Vm.Boot.Startup.LockAcquireRows
import OCaml.Vm.Boot.Startup.LockReleaseRows
import OCaml.Vm.Boot.Startup.EnvLockImage
import OCaml.Vm.Boot.Startup.EnvUnlockImage
import OCaml.Vm.Boot.Startup.LockAcquireImage
import OCaml.Vm.Boot.Startup.LockReleaseImage
import OCaml.Vm.Boot.Startup.LeafCall
import OCaml.Vm.Primitives.Control
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def lockEntry (release : Bool) : BitVec 64 := if release then 0x80042550#64 else 0x80042538#64
def lockBlocks (release : Bool) : List BBlock := if release then retarget_lock_release_recursiveX2550Seg else retarget_lock_acquire_recursiveX2538Seg

theorem lock_input (release : Bool) {ra value c} (h : LeafInput ra c) (pointer : gprGet c.σ 10 = some value) :
    BlockInput (lockBlocks release) (lockEntry release) [(1, ra), (10, value)] [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.raReg, pointer, trivial⟩
  keys := by change KeysOK [1, 10]; decide
  shape := by change ChainOK _ [1, 10] _; cases release <;> decide
  tick := h.tick
  facts := by
    have ret : (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt ra h.aligned]; exact h.aligned
    cases release with
    | false =>
      have code := lockAcquire_code h.image
      chain_facts code with "Vsa.Sim.Code.__retarget_lock_acquire_recursive_at_"
      exact ret
    | true =>
      have code := lockRelease_code h.image
      chain_facts code with "Vsa.Sim.Code.__retarget_lock_release_recursive_at_"
      exact ret

/-- The linked bare-metal recursive-lock hooks return without modifying state. -/
theorem lock_noop (release : Bool) (c : Config) (ra value : BitVec 64) (h : LeafInput ra c)
    (pointer : gprGet c.σ 10 = some value) :
    FnSummary (lockEntry release) (fun d => d = c)
      (WriteRegistersPost [] [] c ra value [(1, ra), (10, value)]) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (lock_input release h pointer))
  · cases release <;> rfl
  · cases release <;> exact ret_tgt ra h.aligned
  · cases release <;> rfl
  · rfl
  · cases release <;> decide

def envLockEntry (release : Bool) : BitVec 64 := if release then 0x80044728#64 else 0x8004471c#64
def envLockBlocks (release : Bool) : List BBlock := if release then env_unlockX4728Seg else env_lockX471cSeg

/-- The lock argument is computed from the generated ELF instructions. -/
def envLockValue (release : Bool) : BitVec 64 :=
  (lookupG 10 (evalBlocks (envLockBlocks release) (SegEvalState.init [] [])).regs).getD 0

theorem envLock_input (release : Bool) {ra c} (h : LeafInput ra c) :
    BlockInput (envLockBlocks release) (envLockEntry release) [(1, ra)] [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.raReg, trivial⟩
  keys := by change KeysOK [1]; decide
  shape := by change ChainOK _ [1] _; cases release <;> decide
  tick := h.tick
  facts := by
    cases release with
    | false =>
      have code := envLock_code h.image
      chain_facts code with "Vsa.Sim.Code.__env_lock_at_"
    | true =>
      have code := envUnlock_code h.image
      chain_facts code with "Vsa.Sim.Code.__env_unlock_at_"

theorem env_lock_prefix (release : Bool) (c : Config) (ra : BitVec 64) (h : LeafInput ra c) :
    FnSummary (envLockEntry release) (fun d => d = c)
      (WriteRegistersPost [10] [] c (lockEntry release) (envLockValue release) [(10, envLockValue release), (1, ra)]) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (envLock_input release h))
  · cases release <;> rfl
  · cases release <;> rfl
  · cases release <;> rfl
  · rfl
  · cases release <;> decide

/-- Newlib's environment lock/unlock wrappers have only their generated a0 effect. -/
theorem env_lock (release : Bool) (c : Config) (ra : BitVec 64) (h : LeafInput ra c) :
    FnSummary (envLockEntry release) (fun d => d = c)
      (WriteRegistersPost [10] [] c ra (envLockValue release) [(10, envLockValue release), (1, ra)]) := by
  apply summary_bind (env_lock_prefix release c ra h) (fun _ post => post.pc)
  intro mid prepared
  apply (lock_noop release mid ra _ (prepared.leaf (by rfl) h.aligned) prepared.result).weaken (fun _ eq => eq)
  intro after returned
  have effects := prefix_readonly_post prepared returned
  exact ⟨effects.toEffectPost, returned.regs.2.1, returned.regs.1, trivial⟩
end OCaml.Vm.Boot.Startup
