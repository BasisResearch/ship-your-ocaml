import OCaml.Vm.Boot.Startup.CamlSharedTableNormalized
import OCaml.Vm.Boot.Startup.CamlSharedTableCallInterface
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def sharedTableAddress : BitVec 64 := BitVec.ofNat 64 Layout.sym_caml_shared_libs_path
def sharedTableArgs (sp : BitVec 64) : GRegs := [(10, sharedTableAddress), (11, 8#64), (2, sp)]

theorem camlSharedTable_input {sp ra c} (leaf : LeafInput ra c) (stack : gprGet c.σ 2 = some sp) :
    BlockInput camlSharedTableSave 0x80004dd4#64 [(2, sp)] [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := ⟨stack, trivial⟩
  keys := by change KeysOK [2]; decide
  shape := by change ChainOK _ [2] _; decide
  tick := leaf.tick
  facts := by
    have code := camlSharedTable_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_main_at_"

/-- The actual caml_main call initializes its shared-library path table with eight slots. -/
theorem caml_shared_table (c : Config) (sp ra : BitVec 64)
    (leaf : LeafInput ra c) (stack : gprGet c.σ 2 = some sp) :
    FnSummary 0x80004dd4#64 (fun d => d = c)
      (WriteRegistersPost [11, 10, 1] [] c jal_80004de0_call.target sharedTableAddress
        ((1, jal_80004de0_call.link) :: sharedTableArgs sp)) := by
  have front : FnSummary 0x80004dd4#64 (fun d => d = c)
      (WriteRegistersPost [11, 10] [] c jal_80004de0_call.pc sharedTableAddress (sharedTableArgs sp)) := by
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (camlSharedTable_input leaf stack))
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_80004de0_call_shape jal_80004de0_call_decode request
    (jal_80004de0_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [10, 11, 2]; decide)
    (by simp only [KeysAvoidRa, sharedTableArgs, keysG]; decide) (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
