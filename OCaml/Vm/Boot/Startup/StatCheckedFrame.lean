import OCaml.Vm.Boot.Startup.StatChecked
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Successful checked allocation preserves every byte below the arena ceiling
that was outside the allocator's original ownership, including old live blocks. -/
theorem StatCheckedReturned.framed_byte {H capacity sp ra s0 n before after a}
    (w : StatCheckedReturned H capacity sp ra s0 n before after)
    (frame : NativeFrame sp 544) (below : a < heapEnd) (outside : ¬ vsaFoot H a) :
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 := by
  have short := frame.resize (small := 32) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 32) 512 := frame.nested (front := 32) (by decide)
  have unowned : ¬ mS H (nativeStack sp 32) a := by
    intro owned
    rcases owned with scratch | heap
    · have high := nested.lower
      unfold stackWin InExt allocHeadroom at scratch
      omega
    · exact outside heap
  have unchanged := w.allocation.allocation.memory a unowned
  change (w.allocated.σ.mem[a]?).getD 0 = (w.allocation.atMalloc.σ.mem[a]?).getD 0 at unchanged
  have restored : after.σ.mem = w.allocated.σ.mem := w.returned.memory
  rw [restored, unchanged, w.allocation.call.memory, w.allocation.setup.memory]
  have low : a < nativeFrameBase sp 32 := by
    have lower := short.lower
    unfold nativeFrameBase
    omega
  rw [frameOn_writeLog _ _ _ (statCheckedLog_inside short) a ⟨Or.inl low, trivial⟩]
end OCaml.Vm.Boot.Startup
