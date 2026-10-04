import OCaml.Vm.Boot.Startup.ParameterValueNormalized
import OCaml.Vm.Boot.Startup.ParameterValueImage
import OCaml.Vm.Boot.Startup.ParameterFirstTestRows
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def parameterValueBlocks : List BBlock := caml_parse_ocamlrunparamX4534FSeg ++ caml_parse_ocamlrunparamX4538TSeg

def parameterValueInput (sp s1 s2 s3 value : BitVec 64) : GRegs :=
  [(2, nativeStack sp 64), (9, s1), (18, s2), (19, s3), (10, value)]
def parameterValueLog (sp s1 s2 s3 : BitVec 64) : List WEntry :=
  nativeWordLog sp 64 [(40, s1), (32, s2), (24, s3)]
def parameterValueRegs (sp s1 s2 s3 value : BitVec 64) : GRegs :=
  (evalBlocks parameterValueBlocks (SegEvalState.init (parameterValueInput sp s1 s2 s3 value) [[0#8]])).regs

local macro "parameter_value_nf" : tactic =>
  `(tactic| simp only [parametervalue_line_80004538, parametervalue_line_8000453c,
    parametervalue_line_80004540, parametervalue_line_80004544, parametervalue_line_80004548,
    parametervalue_line_8000454c, parametervalue_line_80004550, parametervalue_line_80004554,
    parametervalue_line_80004558,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    parameterValueInput, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem parameterValueLog_inside {sp s1 s2 s3} (frame : NativeFrame sp 64) :
    LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (parameterValueLog sp s1 s2 s3) := by
  apply frame.word_log_inside
  intro off value member
  have choices : (off, value) = (40, s1) ∨ (off, value) = (32, s2) ∨ (off, value) = (24, s3) := by simpa using member
  rcases choices with eq | eq | eq <;> cases eq <;> decide

theorem parameterValue_input {sp s1 s2 s3 value ra c} (leaf : LeafInput ra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (parameterValueInput sp s1 s2 s3 value)) (nonnull : value ≠ 0#64)
    (window : ReadWindow value 1)
    (pin : ((writeLog c.σ.mem (parameterValueLog sp s1 s2 s3))[value.toNat]?).getD 0 = 0#8) :
    BlockInput parameterValueBlocks 0x80004534#64 (parameterValueInput sp s1 s2 s3 value) [[0#8]] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 9, 18, 19, 10]; decide
  shape := by change ChainOK _ [2, 9, 18, 19, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := parameterValue_code leaf.image
    have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, frame.address off (by omega)]
      exact frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_parse_ocamlrunparam_at_"
    · exact beq_eq_false_iff_ne.mpr nonnull
    · exact (slot 40 (by decide) (by decide)).sd rfl rfl
    · exact (slot 32 (by decide) (by decide)).sd rfl rfl
    · exact (slot 24 (by decide) (by decide)).sd rfl rfl
    · apply window.lbu rfl
      · parameter_value_nf
        change value + 0#64 + 0#64 = value
        simp only [BitVec.add_zero]
      · exact pin
    · parameter_value_nf
      rfl

/-- A present but empty parameter value bypasses option processing after saving
three additional caller registers. The empty-string read is framed explicitly. -/
theorem parameter_value_empty (c : Config) (sp s1 s2 s3 value ra : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (parameterValueInput sp s1 s2 s3 value)) (nonnull : value ≠ 0#64)
    (window : ReadWindow value 1)
    (pin : ((writeLog c.σ.mem (parameterValueLog sp s1 s2 s3))[value.toNat]?).getD 0 = 0#8) :
    FnSummary 0x80004534#64 (fun d => d = c)
      (WriteRegistersPost [8, 19, 18, 9, 15] (parameterValueLog sp s1 s2 s3) c 0x8000459c#64 value
        (parameterValueRegs sp s1 s2 s3 value)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (parameterValueLog_inside frame))
    (block_summary _ _ _ _ _ (parameterValue_input leaf frame regs nonnull window pin))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
