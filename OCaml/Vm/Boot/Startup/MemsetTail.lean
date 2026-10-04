import OCaml.Vm.Boot.Startup.MemsetTailNormalized
import OCaml.Vm.Boot.Startup.MemsetPrefix
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def memsetTailBlocks : List BBlock := memsetX27a0TSeg ++ memsetX27a8Seg

def memsetTailInput : GRegs := [(12, 8#64), (6, 15#64)]
def memsetTailRegs : GRegs := [(13, 0x800427cc#64), (5, 0x800427b0#64), (12, 8#64), (6, 15#64)]

/-- The eight-byte remainder selects the corresponding entry in the native
computed byte-store tail. -/
theorem memset_tail_dispatch (c : Config) (ra : BitVec 64) (h : LeafInput ra c)
    (size : gprGet c.σ 12 = some 8#64) (mask : gprGet c.σ 6 = some 15#64) :
    FnSummary 0x800427a0#64 (fun d => d = c)
      (BoundaryPost [13, 5] c ra 0x800427d8#64 memsetTailRegs) := by
  have input : BlockInput memsetTailBlocks 0x800427a0#64 memsetTailInput [] c := {
    good := h.good
    minstret := h.minstret
    regs := ⟨size, mask, trivial⟩
    keys := by decide
    shape := by decide
    tick := h.tick
    facts := by
      have code := memsetPrefix_code h.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals decide }
  apply boundary_of_blocks h (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    exact pins
  · decide
  · decide
end OCaml.Vm.Boot.Startup
