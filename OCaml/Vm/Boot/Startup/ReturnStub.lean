import OCaml.Vm.Boot.Startup.LockAcquireRows
import OCaml.Vm.Boot.Startup.LockReleaseRows
import OCaml.Vm.Boot.Startup.LocaleRows
import OCaml.Vm.Boot.Startup.LockAcquireImage
import OCaml.Vm.Boot.Startup.LockReleaseImage
import OCaml.Vm.Boot.Startup.LocaleImage
import OCaml.Vm.Boot.Startup.LeafCall
import OCaml.Vm.Primitives.Control
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The linked bare-metal lock and locale hooks are identical return-only stubs. -/
inductive ReturnStub where
  | acquire | release | locale

def ReturnStub.entry : ReturnStub → BitVec 64
  | .acquire => 0x80042538#64
  | .release => 0x80042550#64
  | .locale => 0x800121ec#64

def ReturnStub.blocks : ReturnStub → List BBlock
  | .acquire => retarget_lock_acquire_recursiveX2538Seg
  | .release => retarget_lock_release_recursiveX2550Seg
  | .locale => caml_init_localeX21ecSeg

theorem returnStub_input (kind : ReturnStub) {ra value c} (h : LeafInput ra c)
    (valueReg : gprGet c.σ 10 = some value) :
    BlockInput kind.blocks kind.entry [(1, ra), (10, value)] [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.raReg, valueReg, trivial⟩
  keys := by change KeysOK [1, 10]; decide
  shape := by change ChainOK kind.entry [1, 10] kind.blocks; cases kind <;> decide
  tick := h.tick
  facts := by
    have ret : (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt ra h.aligned]; exact h.aligned
    cases kind with
    | acquire =>
      have code := lockAcquire_code h.image
      chain_facts code with "Vsa.Sim.Code.__retarget_lock_acquire_recursive_at_"
      exact ret
    | release =>
      have code := lockRelease_code h.image
      chain_facts code with "Vsa.Sim.Code.__retarget_lock_release_recursive_at_"
      exact ret
    | locale =>
      have code := locale_code h.image
      chain_facts code with "Vsa.Sim.Code.caml_init_locale_at_"
      exact ret

/-- All return-only runtime hooks preserve memory and every ordinary register. -/
theorem return_stub (kind : ReturnStub) (c : Config) (ra value : BitVec 64) (h : LeafInput ra c)
    (valueReg : gprGet c.σ 10 = some value) :
    FnSummary kind.entry (fun d => d = c)
      (WriteRegistersPost [] [] c ra value [(1, ra), (10, value)]) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (returnStub_input kind h valueReg))
  · cases kind <;> rfl
  · cases kind <;> exact ret_tgt ra h.aligned
  · cases kind <;> rfl
  · rfl
  · cases kind <;> decide
end OCaml.Vm.Boot.Startup
