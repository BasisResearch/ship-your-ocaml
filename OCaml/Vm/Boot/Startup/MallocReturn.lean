import OCaml.Vm.Boot.Startup.MallocRun
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem startup_image_live : ImageLive startupLive := by
  constructor <;> intro i hi <;>
    simp only [startupLive, Vsa.Densify.ramBase, Vsa.Densify.ramSize,
      Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] at * <;> omega

/-- Runtime code and read-only data are outside every startup allocator call's
metadata and stack ownership. -/
theorem allocator_image_separate (H : List (Nat × Nat)) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) : ImageSeparate (mS H s) := by
  constructor <;> intro i hi owned <;>
    change stackWin s allocHeadroom _ ∨ vsaFoot H _ at owned <;>
    simp only [stackWin, InExt, allocHeadroom, vsaFoot, allocGlobal, InRange,
      Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize,
      heapStart, heapEnd] at * <;> omega

theorem firstMalloc_image_separate : ImageSeparate (mS [] firstMallocStack) :=
  allocator_image_separate [] firstMallocStack (by decide)
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup
open VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem ResetFirstAllocation.pc {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    pcOf after = some jal_8002a8e8_call.link := library_pc w.post.good w.post.result.frame.pc

theorem ResetFirstAllocation.pointer {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    gprGet after.σ 10 = some (BitVec.ofNat 64 (heapStart + 16)) :=
  library_gpr w.post.good (by decide) (by decide) w.post.result.pointer

theorem ResetFirstAllocation.stack {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    gprGet after.σ 2 = some firstMallocStack :=
  library_gpr w.post.good (by decide) (by decide) w.post.result.frame.sp

theorem ResetFirstAllocation.image {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    ExecutableImage after :=
  image_local w.before.post.image w.post.good startup_image_live firstMalloc_image_separate w.post.memory

/-- The allocator return can directly feed the generated startup blocks. -/
theorem ResetFirstAllocation.leaf {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    LeafInput jal_8002a8e8_call.link after where
  good := w.post.good.good
  image := w.image
  minstret := w.post.good.good.minstret
  raReg := library_gpr w.post.good (by decide) (by decide) w.post.result.frame.ra
  aligned := by decide
  tick := w.post.good.tick
end OCaml.Vm.Boot.WhileMinElfParse
