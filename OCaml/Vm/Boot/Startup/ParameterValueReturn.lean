import OCaml.Vm.Boot.Startup.ParameterValueReturnNormalized
import OCaml.Vm.Boot.Startup.ParameterValueReturnImage
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def parameterValueReturnInput (sp value : BitVec 64) : GRegs := [(2, nativeStack sp 64), (10, value)]
def parameterValueReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 64 + 40), read8 c.σ.mem (nativeFrameBase sp 64 + 32),
   read8 c.σ.mem (nativeFrameBase sp 64 + 24), read8 c.σ.mem (nativeFrameBase sp 64 + 56), read8 c.σ.mem (nativeFrameBase sp 64 + 48)]
def parameterValueReturnRegs (sp ra s0 s1 s2 s3 value : BitVec 64) : GRegs := [(2, sp), (8, s0), (1, ra), (19, s3), (18, s2), (9, s1), (10, value)]

local macro "parameter_value_return_nf" : tactic =>
  `(tactic| simp only [parametervaluereturn_line_8000459c, parametervaluereturn_line_800045a0, parametervaluereturn_line_800045a4, parametervaluereturn_line_800045a8, parametervaluereturn_line_800045ac, parametervaluereturn_line_800045b0,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    parameterValueReturnInput, parameterValueReturnLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem parameterValueReturn_input {sp ra s0 s1 s2 s3 value oldra c} (leaf : LeafInput oldra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (parameterValueReturnInput sp value))
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 64 + 56) 8 = ra)
    (saved1 : bytesT c.σ.mem (nativeFrameBase sp 64 + 40) 8 = s1)
    (saved2 : bytesT c.σ.mem (nativeFrameBase sp 64 + 32) 8 = s2)
    (saved3 : bytesT c.σ.mem (nativeFrameBase sp 64 + 24) 8 = s3)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 64 + 48) 8 = s0) (aligned : ra.toNat % 4 = 0) :
    BlockInput caml_parse_ocamlrunparamX459cSeg 0x8000459c#64 (parameterValueReturnInput sp value) (parameterValueReturnLoads sp c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 10]; decide
  shape := by change ChainOK _ [2, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := parameterValueReturn_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_parse_ocamlrunparam_at_"
    · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · parameter_value_return_nf
      rw [read8_value, savedRa, ret_tgt ra aligned]
      exact aligned

/-- Restore all parser saves after processing an existing parameter value. -/
theorem parameter_value_return (c : Config) (sp ra s0 s1 s2 s3 value oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (parameterValueReturnInput sp value))
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 64 + 56) 8 = ra)
    (saved1 : bytesT c.σ.mem (nativeFrameBase sp 64 + 40) 8 = s1)
    (saved2 : bytesT c.σ.mem (nativeFrameBase sp 64 + 32) 8 = s2)
    (saved3 : bytesT c.σ.mem (nativeFrameBase sp 64 + 24) 8 = s3)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 64 + 48) 8 = s0) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000459c#64 (fun d => d = c)
      (WriteRegistersPost [9, 18, 19, 1, 8, 2] [] c ra value (parameterValueReturnRegs sp ra s0 s1 s2 s3 value)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (parameterValueReturn_input leaf frame regs savedRa saved1 saved2 saved3 saved0 aligned))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa]
    exact ret_tgt ra aligned
  · change [(2, nativeStack sp 64 + 64#64), (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 48))),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56))), (19, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 24))),
      (18, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 32))),
      (9, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 40))), (10, value)] = _
    rw [read8_value, read8_value, read8_value, read8_value, read8_value, savedRa, saved0, saved1, saved2, saved3, nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
