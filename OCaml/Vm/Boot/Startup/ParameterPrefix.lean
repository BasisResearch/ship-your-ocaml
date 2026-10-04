import OCaml.Vm.Boot.Startup.ParameterPrefixNormalized
import OCaml.Vm.Boot.Startup.ParameterPrefixCallInterface
import OCaml.Vm.Boot.Startup.ParameterNames
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def parameterPrefixInput (sp ra s0 : BitVec 64) : GRegs := [(2, sp), (1, ra), (8, s0)]
def parameterLog (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 64 [(56, ra), (48, s0)]
def parameterPrefixRegs (sp ra s0 : BitVec 64) : GRegs :=
  [(10, parameterName false), (2, nativeStack sp 64), (1, ra), (8, s0)]

theorem parameterPrefix_input {sp ra s0 c} (leaf : LeafInput ra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (parameterPrefixInput sp ra s0)) :
    BlockInput caml_parse_ocamlrunparamX451cSeg 0x8000451c#64 (parameterPrefixInput sp ra s0) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 1, 8]; decide
  shape := by change ChainOK _ [2, 1, 8] _; decide
  tick := leaf.tick
  facts := by
    have code := parameterPrefix_code leaf.image
    have window (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, frame.address off (by omega)]
      exact frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_parse_ocamlrunparam_at_"
    · exact (window 56 (by decide) (by decide)).sd rfl rfl
    · exact (window 48 (by decide) (by decide)).sd rfl rfl

theorem parameterLog_inside {sp ra s0} (frame : NativeFrame sp 64) :
    LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (parameterLog sp ra s0) := by
  apply frame.word_log_inside
  intro off value member
  have cases : (off, value) = (56, ra) ∨ (off, value) = (48, s0) := by simpa using member
  rcases cases with eq | eq <;> cases eq <;> decide

/-- Save the parameter parser's caller frame and select the certified primary name. -/
theorem parameter_prefix (c : Config) (sp ra s0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (parameterPrefixInput sp ra s0)) :
    FnSummary 0x8000451c#64 (fun d => d = c)
      (WriteRegistersPost [2, 10] (parameterLog sp ra s0) c jal_80004530_call.pc (parameterName false)
        (parameterPrefixRegs sp ra s0)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (parameterLog_inside frame))
    (block_summary _ _ _ _ _ (parameterPrefix_input leaf frame regs))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
