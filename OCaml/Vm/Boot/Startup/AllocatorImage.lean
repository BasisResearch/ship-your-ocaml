import OCaml.Vm.Boot.Startup.AllocatorPins
import OCaml.Vm.Boot.Startup.MallocPlatform
import VsaIris.Vsa.MallocCtx
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.Sym VsaIris.VsaHeap

/-- Allocator read-only pins lie below its heap and outside mutable globals. -/
structure AllocatorPinGeometry (a : Nat) : Prop where
  low : Vsa.Densify.ramBase ≤ a
  high : a < heapStart
  outsideGlobals : ¬ allocGlobal a

theorem AllocatorByteSource.geometry {p : Nat × BitVec 8} (h : AllocatorByteSource p) :
    AllocatorPinGeometry p.1 := by
  unfold AllocatorByteSource at h
  split at h <;> constructor <;>
    simp only [Image.textBase, Image.textSize, Vsa.Densify.ramBase, heapStart,
      allocGlobal, InRange, allocatorImpureAddr] at * <;> omega

/-- Project all allocator code pins from the executable image and its one
read-only data word. The generated balanced certificate identifies each byte. -/
theorem allocator_loaded {c : Config} (image : ExecutableImage c)
    (impure : ∀ i, i < 8 → c.σ.mem[allocatorImpureAddr + i]? = some (allocatorImpureByte i)) :
    TextLoaded allocText c.σ.mem := by
  intro p hp
  have source := allocator_sources p hp
  unfold AllocatorByteSource at source
  split at source
  · next inside =>
      have byte := image.text (p.1 - Image.textBase) (by omega)
      rw [Nat.add_sub_of_le source.1, source.2] at byte
      exact byte
  · have byte := impure (p.1 - allocatorImpureAddr) (by omega)
    rw [Nat.add_sub_of_le source.1, source.2.2] at byte
    exact byte
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.Boot Startup OCaml.Vm.Primitives

/-- Any untouched pre-BSS loader byte survives the complete prefix to malloc. -/
theorem ResetMallocWitness.initial_byte {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (a : Nat) (v : BitVec 8) (beforeBss : a < Layout.sym_bss_start)
    (envOutside : a < Layout.sym_environ ∨ Layout.sym_environ + 8 ≤ a)
    (byte : WhileMinImage.initialMem[a]? = some v) : atMalloc.σ.mem[a]? = some v := by
  have bounds : Layout.sym_bss_start + 8 ≤ Layout.sym_stack_top - 136 := by decide
  have frame : atMalloc.σ.mem[a]? = atMain.σ.mem[a]? := by
    rw [w.post.memory, w.alloc.post.memory, w.alloc.domain.post.memory]
    rw [writeLog_out, writeLog_out]
    · exact outL_of_range (camlMainLog_below _ _ a (by omega)) (by omega) (by omega)
    · change (a < Layout.sym_stack_top - 136 ∨ _) ∧ True
      exact ⟨Or.inl (by omega), trivial⟩
  rw [frame, w.alloc.domain.main.post.toCrtCamlMainPost.memory_below a beforeBss (by
    rcases envOutside with lo | hi
    · exact mainWrites_before _ _ _ lo (by omega)
    · exact mainWrites_between _ _ _ hi (by omega))]
  apply Vsa.Densify.fillZeroMem_some
  rw [w.alloc.domain.main.reset.memory, loaded_memory]
  exact byte

/-- The immutable reentrancy pointer is supplied by the actual ELF loader. -/
theorem ResetMallocWitness.impure {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (i : Nat) (hi : i < 8) :
    atMalloc.σ.mem[allocatorImpureAddr + i]? = some (allocatorImpureByte i) := by
  apply w.initial_byte _ _
  · unfold allocatorImpureAddr Layout.sym_bss_start; omega
  · right
    unfold allocatorImpureAddr Layout.sym_environ
    omega
  · exact allocator_initial_impure i (by omega) hi

/-- No allocator code-image premise remains at the actual first call. -/
theorem ResetMallocWitness.allocator_loaded {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) :
    VsaIris.Sym.TextLoaded VsaIris.Sym.allocText atMalloc.σ.mem :=
  Startup.allocator_loaded w.post.image w.impure
end OCaml.Vm.Boot.WhileMinElfParse
