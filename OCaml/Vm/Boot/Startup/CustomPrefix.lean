import OCaml.Vm.Boot.Startup.CustomPrefixNormalized
import OCaml.Vm.Boot.Startup.CustomPrefixCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def customSaveLog (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 16 [(8, ra), (0, s0)]
def customSaveInput (sp ra s0 : BitVec 64) : GRegs := [(2, sp), (1, ra), (8, s0)]
def customSaveRegs (sp ra s0 : BitVec 64) : GRegs := [(10, 16#64), (2, nativeStack sp 16), (1, ra), (8, s0)]

theorem customSaveLog_inside {sp ra s0} (frame : NativeFrame sp 16) :
    LogInW [⟨nativeFrameBase sp 16, sp.toNat⟩] (customSaveLog sp ra s0) := by
  apply frame.word_log_inside
  intro off value member
  have choices : (off, value) = (8, ra) ∨ (off, value) = (0, s0) := by simpa using member
  rcases choices with eq | eq <;> cases eq <;> decide

theorem customSave_input {sp ra s0 c} (leaf : LeafInput ra c) (frame : NativeFrame sp 16)
    (regs : GHolds c.σ (customSaveInput sp ra s0)) :
    BlockInput customPrefixSave 0x80024a2c#64 (customSaveInput sp ra s0) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 1, 8]; decide
  shape := by change ChainOK _ [2, 1, 8] _; decide
  tick := leaf.tick
  facts := by
    have code := customPrefix_code leaf.image
    have slot (off : Nat) (bound : off + 8 ≤ 16) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 16 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, frame.address _ (by omega)]
      exact frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_init_custom_operations_at_"
    · exact (slot 8 (by decide) (by decide)).sd rfl rfl
    · exact (slot 0 (by decide) (by decide)).sd rfl rfl

/-- Save the custom initializer's caller and prepare its first two-word request. -/
theorem custom_save (c : Config) (sp ra s0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ (customSaveInput sp ra s0)) :
    FnSummary 0x80024a2c#64 (fun d => d = c)
      (WriteRegistersPost [2, 10] (customSaveLog sp ra s0) c jal_80024a3c_call.pc 16#64
        (customSaveRegs sp ra s0)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (customSaveLog_inside frame))
    (block_summary _ _ _ _ _ (customSave_input leaf frame regs))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
