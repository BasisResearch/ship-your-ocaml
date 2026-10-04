import OCaml.Vm.Boot.Startup.CamlAuxNormalized
import OCaml.Vm.Boot.Startup.CamlAuxCallInterface
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Word32Access
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def camlAuxInput (sp ra : BitVec 64) : GRegs := [(2, sp), (1, ra)]
def camlAuxRegs (sp ra : BitVec 64) : GRegs := [(10, 0#64), (2, sp), (1, ra)]

local macro "caml_aux_nf" : tactic =>
  `(tactic| simp only [camlaux_line_80004d9c, camlaux_line_80004da0,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    camlAuxInput, wvalM, wentryM, widthOfM, imm20Of,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem camlAux_input {sp ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (camlAuxInput sp ra))
    (cleanup : LPins4 c.σ.mem Layout.sym_caml_cleanup_on_exit (List.replicate 4 0#8)) :
    BlockInput caml_mainX4d9cSeg 0x80004d9c#64 (camlAuxInput sp ra) [List.replicate 4 0#8] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 1]; decide
  shape := by change ChainOK _ [2, 1] _; decide
  tick := leaf.tick
  facts := by
    have code := camlAux_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_main_at_"
    caml_aux_nf
    apply (show ReadWindow (BitVec.ofNat 64 Layout.sym_caml_cleanup_on_exit) 4 from by constructor <;> decide).lw rfl
    · caml_aux_nf
      decide
    · exact cleanup

/-- caml_main obtains the pooling argument from the generated cleanup global. -/
theorem caml_aux_prefix (c : Config) (sp ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (camlAuxInput sp ra))
    (cleanup : LPins4 c.σ.mem Layout.sym_caml_cleanup_on_exit (List.replicate 4 0#8)) :
    FnSummary 0x80004d9c#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c jal_80004da4_call.pc 0#64 (camlAuxRegs sp ra)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (camlAux_input leaf regs cleanup))
  · rfl
  · rfl
  · simp only [caml_mainX4d9cSeg, evalBlocks, evalBlock, SegEvalState.init]
    caml_aux_nf
    rfl
  · rfl
  · decide

/-- The real caller load and JAL reach caml_startup_aux with pooling disabled. -/
theorem caml_aux_call (c : Config) (sp ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (camlAuxInput sp ra))
    (cleanup : LPins4 c.σ.mem Layout.sym_caml_cleanup_on_exit (List.replicate 4 0#8)) :
    FnSummary 0x80004d9c#64 (fun d => d = c)
      (WriteRegistersPost [10, 1] [] c jal_80004da4_call.target 0#64
        [(1, jal_80004da4_call.link), (10, 0#64), (2, sp)]) := by
  apply summary_bind (caml_aux_prefix c sp ra leaf regs cleanup) (fun _ post => post.pc)
  intro mid post
  have input : GHolds mid.σ [(10, 0#64), (2, sp)] :=
    holds_project post.regs (by simp [camlAuxRegs, lookupG])
  have call := call_registers_summary jal_80004da4_call_shape jal_80004da4_call_decode mid
    (jal_80004da4_call_pins post.image) post.good post.image post.tick post.minstret _ input
    (by change KeysOK [10, 2]; decide) (by simp [KeysAvoidRa, keysG]) (by rfl)
  apply call.weaken (fun _ eq => eq)
  intro after called
  exact prefix_call_post post called
end OCaml.Vm.Boot.Startup
