import OCaml.Vm.Boot.Startup.FindStartNormalized
import OCaml.Vm.Boot.Startup.FindStartImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findStartBlocks : List BBlock := findenv_rX746cFSeg ++ findenv_rX7474FSeg ++ findenv_rX7484FSeg

def findStartInput (sp name s4 value : BitVec 64) : GRegs :=
  [(19, BitVec.ofNat 64 Layout.sym_environ), (2, nativeStack sp 80), (20, s4), (18, name), (10, value)]
def findStartLog (sp s4 : BitVec 64) : List WEntry := nativeWordLog sp 80 [(32, s4)]
def findStartLoads (b : BitVec 8) (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem Layout.sym_environ, [b]]
def findStartRegs (sp name s4 value env : BitVec 64) (b : BitVec 8) : GRegs :=
  [(12, name), (15, nameSignedByte b + (-61#64)), (14, nameByteWord b), (9, env),
   (19, BitVec.ofNat 64 Layout.sym_environ), (2, nativeStack sp 80), (20, s4), (18, name), (10, value)]

structure FindStartInput (sp name s4 value env ra : BitVec 64) (b : BitVec 8) (c : Config) : Prop extends LeafInput ra c where
  regs : GHolds c.σ (findStartInput sp name s4 value)
  frame : NativeFrame sp 80
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  envNonzero : env ≠ 0#64
  window : ReadWindow name 1
  pin : ((writeLog c.σ.mem (findStartLog sp s4))[name.toNat]?).getD 0 = b
  nonzero : b ≠ 0#8
  notEquals : b ≠ 61#8

local macro "find_start_nf" : tactic =>
  `(tactic| simp only [findstart_line_8003746c, findstart_line_80037474, findstart_line_80037478,
    findstart_line_8003747c, findstart_line_80037484, findstart_line_80037488,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findStartInput, findStartLoads, wvalM, wentryM, widthOfM, name_lbu_value,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findStart_input {sp name s4 value env ra b c} (h : FindStartInput sp name s4 value env ra b c) :
    BlockInput findStartBlocks 0x8003746c#64 (findStartInput sp name s4 value) (findStartLoads b c) c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by change KeysOK [19, 2, 20, 18, 10]; decide
  shape := by change ChainOK _ [19, 2, 20, 18, 10] _; decide
  tick := h.tick
  facts := by
    have code := findStart_code h.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_environ) 8 from by constructor <;> decide).ld rfl rfl (read8_pins _ _)
    · find_start_nf
      rw [read8_value, h.environment]
      exact beq_eq_false_iff_ne.mpr h.envNonzero
    · have window : WriteWindow (nativeStack sp 80 + 32#64) 8 := by
        rw [nativeStack, h.frame.address 32 (by decide)]
        exact h.frame.word (by decide) (by decide)
      exact window.sd rfl rfl
    · apply h.window.lbu rfl
      · find_start_nf
        exact BitVec.add_zero name
      · exact h.pin
    · find_start_nf
      exact nameByte_zero_guard (by simp [h.nonzero])
    · find_start_nf
      exact beq_eq_false_iff_ne.mpr (fun eq => h.notEquals ((nameByte_equals b).mp eq))

theorem findStart_log_inside {sp s4} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (findStartLog sp s4) := by
  apply frame.word_log_inside
  intro off value member
  have eq : (off, value) = (32, s4) := List.mem_singleton.mp member
  cases eq
  decide

/-- A nonnull environment and ordinary first name byte select the native scan. -/
theorem find_start (c : Config) (sp name s4 value env ra : BitVec 64) (b : BitVec 8)
    (h : FindStartInput sp name s4 value env ra b c) :
    FnSummary 0x8003746c#64 (fun d => d = c)
      (WriteRegistersPost [9, 14, 15, 12] (findStartLog sp s4) c 0x80037490#64 value
        (findStartRegs sp name s4 value env b)) := by
  apply registers_of_blocks h.image (h.frame.image_outside (findStart_log_inside h.frame))
    (block_summary _ _ _ _ _ (findStart_input h))
  · rfl
  · rfl
  · change [(12, name + 0#64), (15, nameSignedByte b + (-61#64)), (14, nameByteWord b),
      (9, bytesVal .ld (read8 c.σ.mem Layout.sym_environ)),
      (19, BitVec.ofNat 64 Layout.sym_environ), (2, nativeStack sp 80), (20, s4), (18, name), (10, value)] = _
    rw [read8_value, h.environment]
    rw [BitVec.add_zero name]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
