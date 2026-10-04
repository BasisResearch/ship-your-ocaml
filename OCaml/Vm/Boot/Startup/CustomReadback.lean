import OCaml.Vm.Boot.Startup.CustomPublish
import OCaml.Vm.Gc.Readback
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

def customCells (kind : CustomKind) (p head : BitVec 64) : List (Nat × BitVec 64) :=
  [(p.toNat, BitVec.ofNat 64 kind.ops), (p.toNat + 8, head), (Layout.sym_custom_ops_table, p)]

/-- The list head and both freshly initialized node words are separated stores. -/
theorem customPublish_read {kind p head a value}
    (region : ZeroPairRegion p.toNat 1) (mem : Vsa.MemRepr.Mem)
    (member : (a, value) ∈ customCells kind p head) :
    bytesT (writeLog mem (customPublishLog kind p head)) a 8 = value := by
  have lower := region.lower
  have bound : Layout.sym_custom_ops_table + 8 ≤ heapStart := by decide
  have separate : (customCells kind p head).Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by
    simp [customCells]
    omega
  have read := OCaml.Vm.Gc.word_writeLog_cells mem (customCells kind p head) separate member
  simpa only [customPublishLog, customCells, List.map_cons, List.map_nil, customPublish_second region] using read
end OCaml.Vm.Boot.Startup
