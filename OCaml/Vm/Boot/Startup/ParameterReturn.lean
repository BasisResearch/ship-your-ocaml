import OCaml.Vm.Boot.Startup.ParameterReturnNormalized
import OCaml.Vm.Boot.Startup.ParameterReturnImage
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def parameterReturnInput (sp : BitVec 64) : GRegs := [(2, nativeStack sp 64), (10, 0#64)]
def parameterReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 64 + 56), read8 c.σ.mem (nativeFrameBase sp 64 + 48)]
def parameterReturnRegs (sp ra s0 : BitVec 64) : GRegs := [(2, sp), (8, s0), (1, ra), (10, 0#64)]

local macro "parameter_return_nf" : tactic =>
  `(tactic| simp only [parameterreturn_line_800045a8, parameterreturn_line_800045ac, parameterreturn_line_800045b0,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    parameterReturnInput, parameterReturnLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem parameterReturn_input {sp ra s0 oldra c} (leaf : LeafInput oldra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (parameterReturnInput sp))
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 64 + 56) 8 = ra)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 64 + 48) 8 = s0) (aligned : ra.toNat % 4 = 0) :
    BlockInput caml_parse_ocamlrunparamX45a8Seg 0x800045a8#64 (parameterReturnInput sp) (parameterReturnLoads sp c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 10]; decide
  shape := by change ChainOK _ [2, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := parameterReturn_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_parse_ocamlrunparam_at_"
    · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · parameter_return_nf
      rw [read8_value, savedRa, ret_tgt ra aligned]
      exact aligned

/-- The no-parameter path restores the original parser caller frame. -/
theorem parameter_return (c : Config) (sp ra s0 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (parameterReturnInput sp))
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 64 + 56) 8 = ra)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 64 + 48) 8 = s0) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800045a8#64 (fun d => d = c)
      (WriteRegistersPost [1, 8, 2] [] c ra 0#64 (parameterReturnRegs sp ra s0)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (parameterReturn_input leaf frame regs savedRa saved0 aligned))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa]
    exact ret_tgt ra aligned
  · change [(2, nativeStack sp 64 + 64#64), (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 48))),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56))), (10, 0#64)] = _
    rw [read8_value, read8_value, savedRa, saved0, nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
