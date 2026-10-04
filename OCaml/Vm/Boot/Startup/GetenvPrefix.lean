import OCaml.Vm.Boot.Startup.GetenvPrefixNormalized
import OCaml.Vm.Boot.Startup.GetenvPrefixCallInterface
import OCaml.Vm.Boot.Startup.AllocatorPins
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def getenvPrefixInput (sp name ra : BitVec 64) : GRegs := [(10, name), (2, sp), (1, ra)]
def getenvReent (c : Config) : BitVec 64 := bytesT c.σ.mem allocatorImpureAddr 8
def getenvPrefixLoads (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem allocatorImpureAddr]
def getenvLog (sp ra : BitVec 64) : List WEntry := nativeWordLog sp 32 [(24, ra)]
def getenvPrefixRegs (sp name ra reent : BitVec 64) : GRegs :=
  [(12, nativeStack sp 32 + 12#64), (2, nativeStack sp 32), (10, reent), (11, name), (1, ra)]

local macro "getenv_prefix_nf" : tactic =>
  `(tactic| simp only [getenvprefix_line_80037410, getenvprefix_line_80037414, getenvprefix_line_80037418,
    getenvprefix_line_8003741c, getenvprefix_line_80037420, getenvprefix_line_80037424,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    getenvPrefixInput, getenvPrefixLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem getenvPrefix_input {sp name ra c} (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ (getenvPrefixInput sp name ra)) :
    BlockInput getenvX7410Seg 0x80037410#64 (getenvPrefixInput sp name ra) (getenvPrefixLoads c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 2, 1]; decide
  shape := by change ChainOK _ [10, 2, 1] _; decide
  tick := leaf.tick
  facts := by
    have code := getenvPrefix_code leaf.image
    chain_facts code with "Vsa.Sim.Code.getenv_at_"
    · exact (show ReadWindow (BitVec.ofNat 64 allocatorImpureAddr) 8 from by constructor <;> decide).ld rfl rfl (read8_pins _ _)
    · have window : WriteWindow (nativeStack sp 32 + 24#64) 8 := by
        rw [nativeStack, frame.address 24 (by decide)]
        exact frame.word (by decide) (by decide)
      exact window.sd rfl rfl

theorem getenvLog_inside {sp ra} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (getenvLog sp ra) := by
  apply frame.word_log_inside
  intro off value member
  have eq : (off, value) = (24, ra) := List.mem_singleton.mp member
  cases eq
  decide

/-- Getenv loads the generated reentrancy-pointer word and saves its caller link. -/
theorem getenv_prefix (c : Config) (sp name ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ (getenvPrefixInput sp name ra)) :
    FnSummary 0x80037410#64 (fun d => d = c)
      (WriteRegistersPost [11, 10, 2, 12] (getenvLog sp ra) c jal_80037428_call.pc (getenvReent c)
        (getenvPrefixRegs sp name ra (getenvReent c))) := by
  apply registers_of_blocks leaf.image (frame.image_outside (getenvLog_inside frame))
    (block_summary _ _ _ _ _ (getenvPrefix_input leaf frame regs))
  · rfl
  · rfl
  · change [(12, nativeStack sp 32 + 12#64), (2, nativeStack sp 32),
      (10, bytesVal .ld (read8 c.σ.mem allocatorImpureAddr)), (11, name + 0#64), (1, ra)] = _
    rw [read8_value, BitVec.add_zero name]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
