import OCaml.Vm.Boot.Startup.ParameterFirstTestRows
import OCaml.Vm.Boot.Startup.ParameterFallbackNormalized
import OCaml.Vm.Boot.Startup.ParameterFallbackCallInterface
import OCaml.Vm.Boot.Startup.ParameterSecondTestNormalized
import OCaml.Vm.Boot.Startup.ParameterNames
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def parameterFallbackBlocks : List BBlock := caml_parse_ocamlrunparamX4534TSeg ++ caml_parse_ocamlrunparamX473cSeg

theorem parameterFallback_input {ra c} (leaf : LeafInput ra c) (zero : gprGet c.σ 10 = some 0#64) :
    BlockInput parameterFallbackBlocks 0x80004534#64 [(10, 0#64)] [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := ⟨zero, trivial⟩
  keys := by change KeysOK [10]; decide
  shape := by change ChainOK _ [10] _; decide
  tick := leaf.tick
  facts := by
    have code := parameterFallback_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_parse_ocamlrunparam_at_"
    decide

/-- A missing primary variable selects the certified fallback name. -/
theorem parameter_fallback (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (zero : gprGet c.σ 10 = some 0#64) :
    FnSummary 0x80004534#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c jal_80004744_call.pc (parameterName true) [(10, parameterName true)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (parameterFallback_input leaf zero))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

theorem parameterSecond_input {ra c} (leaf : LeafInput ra c) (zero : gprGet c.σ 10 = some 0#64) :
    BlockInput caml_parse_ocamlrunparamX4748TSeg 0x80004748#64 [(10, 0#64)] [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := ⟨zero, trivial⟩
  keys := by change KeysOK [10]; decide
  shape := by change ChainOK _ [10] _; decide
  tick := leaf.tick
  facts := by
    have code := parameterFallback_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_parse_ocamlrunparam_at_"
    decide

/-- With neither variable present, the parser bypasses its option-processing loop. -/
theorem parameter_second_missing (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (zero : gprGet c.σ 10 = some 0#64) :
    FnSummary 0x80004748#64 (fun d => d = c)
      (WriteRegistersPost [8] [] c 0x800045a8#64 0#64 [(8, 0#64), (10, 0#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (parameterSecond_input leaf zero))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
