import OCaml.Vm.Boot.Startup.StrncmpReturnNormalized
import OCaml.Vm.Boot.Startup.StrncmpReturnImage
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Control
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

theorem strncmpReturn_input {ra c} (h : LeafInput ra c) :
    BlockInput strncmpX0d70Seg 0x80040d70#64 [(1, ra)] [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.raReg, trivial⟩
  keys := by change KeysOK [1]; decide
  shape := by change ChainOK _ [1] _; decide
  tick := h.tick
  facts := by
    have code := strncmpReturn_code h.image
    chain_facts code with "Vsa.Sim.Code.strncmp_at_"
    change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
    rw [ret_tgt ra h.aligned]
    exact h.aligned

/-- Native zero result after exhausting the equal bounded prefix. -/
theorem strncmp_return (c : Config) (ra : BitVec 64) (h : LeafInput ra c) :
    FnSummary 0x80040d70#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c ra 0#64 [(10, 0#64), (1, ra)]) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (strncmpReturn_input h))
  · rfl
  · exact ret_tgt ra h.aligned
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
