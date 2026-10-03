import OCaml.Vm.Boot.Startup.StatAllocRows
import OCaml.Vm.Boot.Startup.StatAllocImage
import OCaml.Vm.Primitives.Boundary
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The source's disabled-pooling path consists of its test and malloc tail jump. -/
def statAllocDirect : List BBlock :=
  caml_stat_alloc_noexcXab2cTSeg ++ caml_stat_alloc_noexcXab7cSeg

theorem statAlloc_input {c : Config} {ra : BitVec 64} (h : LeafInput ra c)
    (pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)) :
    BlockInput statAllocDirect (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc)
      [] [List.replicate 8 0#8] c where
  good := h.good
  minstret := h.minstret
  regs := True.intro
  keys := by decide
  shape := by decide
  tick := h.tick
  facts := by
    have code := statAlloc_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_noexc_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_pool)
        (by constructor <;> decide) rfl rfl
      exact pool
    · decide

/-- The wrapper reaches malloc, preserving the caller's argument, stack and return
address through its complete nonwritten-register frame. No allocator run is assumed. -/
theorem statAlloc_dispatch (c : Config) (ra : BitVec 64) (h : LeafInput ra c)
    (pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) (fun d => d = c)
      (BoundaryPost [15] c ra (BitVec.ofNat 64 Layout.sym_malloc) [(15, 0#64)]) := by
  apply boundary_of_blocks h (block_summary _ _ _ _ _ (statAlloc_input h pool))
  · rfl
  · rfl
  · intro σ pins
    apply holds_project pins
    decide
  · decide
  · decide

/-- A supplied malloc summary closes the tail path with the ordinary summary rule.
The supplier is the landed allocator contract, instantiated at the reached heap. -/
theorem statAlloc_with_malloc (c : Config) (ra : BitVec 64) (h : LeafInput ra c)
    (pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8))
    (Q : Config → Prop)
    (malloc : ∀ d, BoundaryPost [15] c ra (BitVec.ofNat 64 Layout.sym_malloc) [(15, 0#64)] d →
      FnSummary (BitVec.ofNat 64 Layout.sym_malloc) (fun e => e = d) Q) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) (fun d => d = c) Q :=
  boundary_bind (statAlloc_dispatch c ra h pool) malloc
end OCaml.Vm.Boot.Startup
