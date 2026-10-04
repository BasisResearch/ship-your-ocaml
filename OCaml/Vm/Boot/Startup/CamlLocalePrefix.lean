import OCaml.Vm.Boot.Startup.CamlAuxTestRows
import OCaml.Vm.Boot.Startup.CamlLocaleNormalized
import OCaml.Vm.Boot.Startup.CamlLocaleCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def camlLocaleBlocks : List BBlock := caml_mainX4da8TSeg ++ caml_mainX4dbcSeg
def camlLocaleParked (sp s0 s2 s3 s4 : BitVec 64) : GRegs :=
  [(2, nativeStack sp Layout.camlMainFrameBytes), (8, s0), (20, s4), (18, s2), (19, s3)]
def camlLocaleInput (sp ra s0 s2 s3 s4 : BitVec 64) : GRegs :=
  (1, ra) :: (10, 1#64) :: camlLocaleParked sp s0 s2 s3 s4

def camlLocaleSlots (s0 s2 s3 s4 : BitVec 64) : List (Nat × BitVec 64) :=
  [(Layout.camlMainSaveOffset 8, s0), (Layout.camlMainSaveOffset 20, s4),
   (Layout.camlMainSaveOffset 18, s2), (Layout.camlMainSaveOffset 19, s3)]
def camlLocaleLog (sp s0 s2 s3 s4 : BitVec 64) : List WEntry :=
  nativeWordLog sp Layout.camlMainFrameBytes (camlLocaleSlots s0 s2 s3 s4)

structure CamlLocaleInput (sp ra s0 s2 s3 s4 : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp Layout.camlMainFrameBytes
  regs : GHolds c.σ (camlLocaleInput sp ra s0 s2 s3 s4)

theorem camlLocaleLog_inside {sp s0 s2 s3 s4} (frame : NativeFrame sp Layout.camlMainFrameBytes) :
    LogInW [⟨nativeFrameBase sp Layout.camlMainFrameBytes, sp.toNat⟩] (camlLocaleLog sp s0 s2 s3 s4) := by
  apply frame.word_log_inside
  intro off value member
  have choices : (off, value) = (Layout.camlMainSaveOffset 8, s0) ∨
      (off, value) = (Layout.camlMainSaveOffset 20, s4) ∨
      (off, value) = (Layout.camlMainSaveOffset 18, s2) ∨
      (off, value) = (Layout.camlMainSaveOffset 19, s3) := by simpa [camlLocaleSlots] using member
  rcases choices with eq | eq | eq | eq <;> cases eq <;> decide

theorem camlLocale_input {sp ra s0 s2 s3 s4 c} (h : CamlLocaleInput sp ra s0 s2 s3 s4 c) :
    BlockInput camlLocaleBlocks 0x80004da8#64 (camlLocaleInput sp ra s0 s2 s3 s4) [] c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by change KeysOK [1, 10, 2, 8, 20, 18, 19]; decide
  shape := by change ChainOK _ [1, 10, 2, 8, 20, 18, 19] _; decide
  tick := h.tick
  facts := by
    have code := camlLocale_code h.image
    have slot (r : Nat) (bound : Layout.camlMainSaveOffset r + 8 ≤ Layout.camlMainFrameBytes)
        (aligned : Layout.camlMainSaveOffset r % 8 = 0) :
        WriteWindow (nativeStack sp Layout.camlMainFrameBytes + BitVec.ofNat 64 (Layout.camlMainSaveOffset r)) 8 := by
      rw [nativeStack, h.frame.address _ (by omega)]
      exact h.frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_main_at_"
    · rfl
    · exact (slot 8 (by decide) (by decide)).sd rfl rfl
    · exact (slot 20 (by decide) (by decide)).sd rfl rfl
    · exact (slot 18 (by decide) (by decide)).sd rfl rfl
    · exact (slot 19 (by decide) (by decide)).sd rfl rfl

/-- First-start success saves the rest of caml_main's generated caller frame. -/
theorem caml_locale_prefix (c : Config) (sp ra s0 s2 s3 s4 : BitVec 64)
    (h : CamlLocaleInput sp ra s0 s2 s3 s4 c) :
    FnSummary 0x80004da8#64 (fun d => d = c)
      (WriteRegistersPost [] (camlLocaleLog sp s0 s2 s3 s4) c jal_80004dcc_call.pc 1#64
        (camlLocaleInput sp ra s0 s2 s3 s4)) := by
  apply registers_of_blocks h.image (h.frame.image_outside (camlLocaleLog_inside h.frame))
    (block_summary _ _ _ _ _ (camlLocale_input h))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
