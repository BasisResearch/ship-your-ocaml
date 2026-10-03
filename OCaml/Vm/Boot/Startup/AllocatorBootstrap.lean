import OCaml.Vm.Boot.WhileMinElfLoaded
import OCaml.Vm.Boot.Startup.BssFrame
import Vsa.Sim.DlHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.Boot Vsa.MemRepr OCaml.Vm.Primitives
open Vsa.Sim.DlHeap

/-- The library arena predicate requires an initialized sbrk base. -/
theorem heap_base_word {m : Mem} {exts reallocs top brkv chunks bins}
    (heap : HeapAt m exts reallocs top brkv chunks bins) :
    bytesT m sbrkBaseAddr 8 = BitVec.ofNat 64 heapStart := by
  have read : read64 m sbrkBaseAddr = some (BitVec.ofNat 64 heapStart).toNat := by
    simpa only [show (BitVec.ofNat 64 heapStart).toNat = heapStart from by decide] using heap.sbrk_base
  have value := execRetEpilogueWord_value m sbrkBaseAddr (BitVec.ofNat 64 heapStart) read
  change bytesVal .ld (read8 m sbrkBaseAddr) = _ at value
  simpa only [read8_value] using value

/-- This is an eight-byte certificate over the pinned loader view, not memory evaluation. -/
theorem initial_sbrk_base : bytesT WhileMinImage.initialMem sbrkBaseAddr 8 = 0xffffffffffffffff#64 :=
  (loaderMem_bytes WhileMinImage.pieces WhileMinImage.imageByte sbrkBaseAddr 8).trans (by decide +kernel)

/-- The sbrk sentinel lies before BSS and after main's global store. -/
theorem CrtCamlMainPost.sbrk_base {initial c : Config} (post : CrtCamlMainPost initial c) :
    bytesT c.σ.mem sbrkBaseAddr 8 = bytesT initial.σ.mem sbrkBaseAddr 8 := by
  apply post.bytes_below _ _ (by decide)
  intro i hi
  apply mainWrites_between <;>
    simp only [sbrkBaseAddr, Layout.sym_environ, Layout.sym_stack_top] <;> omega

/-- A source-initialized arena cannot satisfy the library's post-bootstrap heap predicate. -/
theorem heap_not_initialized {m : Mem}
    (sentinel : bytesT m sbrkBaseAddr 8 = 0xffffffffffffffff#64)
    (exts reallocs top brkv chunks bins) : ¬ HeapAt m exts reallocs top brkv chunks bins := by
  intro heap
  have contradiction := sentinel.symm.trans (heap_base_word heap)
  exact (by decide : 0xffffffffffffffff#64 ≠ BitVec.ofNat 64 heapStart) contradiction

end OCaml.Vm.Boot.Startup
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.Boot Vsa.Sim.DlHeap Startup

/-- The closed reset-to-C-entry witness retains the actual uninitialized allocator sentinel. -/
theorem ResetCamlMainWitness.sbrk_base {initial after : Config}
    (witness : ResetCamlMainWitness initial after) :
    bytesT after.σ.mem sbrkBaseAddr 8 = 0xffffffffffffffff#64 := by
  have resetWord := (congrArg (fun m => bytesT m sbrkBaseAddr 8)
    (witness.reset.memory.trans loaded_memory)).trans initial_sbrk_base
  exact witness.post.toCrtCamlMainPost.sbrk_base.trans
    ((bytesT_memEqv (fun a => (Vsa.Densify.memEqv_fillZeroMem initial.σ.mem a).symm) _ _).trans resetWord)

/-- Checked startup obligation: prove the first malloc bootstrap path before applying
`malloc_all`/`mallocLocalRun_proved`, whose input arena predicate is false here. -/
theorem ResetCamlMainWitness.heap_not_initialized {initial after : Config}
    (witness : ResetCamlMainWitness initial after) (exts reallocs top brkv chunks bins) :
    ¬ HeapAt after.σ.mem exts reallocs top brkv chunks bins :=
  Startup.heap_not_initialized witness.sbrk_base exts reallocs top brkv chunks bins
end OCaml.Vm.Boot.WhileMinElfParse
