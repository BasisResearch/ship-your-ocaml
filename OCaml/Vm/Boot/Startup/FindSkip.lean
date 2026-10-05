import OCaml.Vm.Boot.Startup.FindSkipNormalized
import OCaml.Vm.Boot.Startup.FindSkipImage
import OCaml.Vm.Boot.Startup.FindMatchNormalized
import OCaml.Vm.Boot.Startup.FindRestore
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- A nonzero comparison skips to the next entry; a null next entry ends the
search, restoring s0 and s4 before the common unlock path. -/
def findSkipBlocks : List BBlock := findenv_rX74ccTSeg ++ findenv_rX74e0FSeg ++ findenv_rX74ecSeg

def findSkipInput (sp env reent result : BitVec 64) : GRegs :=
  [(10, result), (9, env), (2, nativeStack sp 80), (21, reent)]
def findSkipLoads (sp env : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (env + 8#64).toNat, read8 c.σ.mem (nativeFrameBase sp 80 + 64),
   read8 c.σ.mem (nativeFrameBase sp 80 + 32)]
def findSkipRegs (sp env reent s0 s4 : BitVec 64) : GRegs :=
  [(20, s4), (8, s0), (9, env + 8#64), (10, 0#64), (2, nativeStack sp 80), (21, reent)]

theorem findSkip_input {sp env reent result ra c} (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findSkipInput sp env reent result)) (nonzero : result ≠ 0#64)
    (window : ReadWindow (env + 8#64) 8) (last : bytesT c.σ.mem (env + 8#64).toNat 8 = 0#64) :
    BlockInput findSkipBlocks 0x800374cc#64 (findSkipInput sp env reent result) (findSkipLoads sp env c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 9, 2, 21]; decide
  shape := by change ChainOK _ [10, 9, 2, 21] _; decide
  tick := leaf.tick
  facts := by
    have code := findSkip_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · exact bne_iff_ne.mpr nonzero
    · exact window.ld rfl rfl (read8_pins _ _)
    · change (bytesVal .ld (read8 c.σ.mem (env + 8#64).toNat) != 0#64) = false
      rw [read8_value, last]
      decide
    · exact (frame.read_slot (off := 64) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))

theorem find_skip (c : Config) (sp env reent result s0 s4 ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findSkipInput sp env reent result))
    (nonzero : result ≠ 0#64) (window : ReadWindow (env + 8#64) 8)
    (last : bytesT c.σ.mem (env + 8#64).toNat 8 = 0#64)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 80 + 64) 8 = s0)
    (saved4 : bytesT c.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4) :
    FnSummary 0x800374cc#64 (fun d => d = c)
      (WriteRegistersPost [20, 8, 9, 10] [] c 0x800374f4#64 0#64 (findSkipRegs sp env reent s0 s4)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findSkip_input leaf frame regs nonzero window last))
  · rfl
  · rfl
  · change [(20, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 32))),
      (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 64))), (9, env + 8#64),
      (10, bytesVal .ld (read8 c.σ.mem (env + 8#64).toNat)), (2, nativeStack sp 80), (21, reent)] = _
    rw [read8_value, read8_value, read8_value, saved4, saved0, last]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
