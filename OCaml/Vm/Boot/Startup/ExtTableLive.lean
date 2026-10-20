import OCaml.Vm.Boot.Startup.ExtTableFinish
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.ReadyPerm
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! caml_ext_table_init keeps the owned blocks of its caller. -/

/-- Table initialization keeps every byte of every live block outside the table header. -/
theorem ExtTableReturned.live_byte_away {H capacity sp ra s0 t n before after}
    (w : ExtTableReturned H capacity sp ra s0 t n before after) (frame : NativeFrame sp 560)
    {e : Nat × Nat} (member : e ∈ H) {x : Nat} (inside : InExt e x)
    (bounds : heapStart ≤ e.1 ∧ e.1 + e.2 ≤ heapEnd) (away : x < t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ x) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  have short32 := nested.resize (small := 32) (by decide) (by decide)
  have lower := frame.lower
  unfold InExt at inside
  have hx : x < heapEnd := by omega
  have below : x < nativeFrameBase sp 16 := by unfold nativeFrameBase; omega
  have nest := short.stack_nat
  have below32 : x < nativeFrameBase (nativeStack sp 16) 32 := by
    unfold nativeFrameBase at nest ⊢; omega
  have unowned : ¬ mS H (nativeStack (nativeStack sp 16) 32) x := by
    intro owned
    rcases owned with scratch | heap
    · unfold stackWin InExt allocHeadroom at scratch
      rw [short32.stack_nat] at scratch
      unfold nativeFrameBase at scratch below32 nest
      omega
    · have := allocator_payload_outside member bounds.1 heap
      omega
  have alloc := w.allocation.allocation.allocation.allocation.memory x unowned
  change (w.allocation.allocation.allocated.σ.mem[x]?).getD 0 =
    (w.allocation.allocation.allocation.atMalloc.σ.mem[x]?).getD 0 at alloc
  rw [show after.σ.mem = w.published.σ.mem from w.post.memory, w.publication.memory,
    writeLog_out _ _ _ (show OutL (extTablePublishLog t _) x from ⟨by
      unfold Layout.off_ext_table_contents; unfold Layout.ext_table_bytes at away; dsimp only; omega, trivial⟩),
    show w.allocated.σ.mem = w.allocation.allocation.allocated.σ.mem from w.allocation.allocation.returned.memory,
    alloc, w.allocation.allocation.allocation.call.memory, w.allocation.allocation.allocation.setup.memory,
    frameOn_writeLog _ _ _ (statCheckedLog_inside short32) x ⟨Or.inl below32, trivial⟩,
    w.allocation.call.memory, w.allocation.setup.memory,
    frameOn_writeLog _ _ _ (extTableLog_inside (t := t) short) x ⟨Or.inl below,
      by unfold Layout.ext_table_bytes at away; exact away, trivial⟩]

/-- Table initialization keeps the owned blocks when the header lies outside the arena. -/
theorem ExtTableReturned.live {H capacity sp ra s0 t n before after}
    (w : ExtTableReturned H capacity sp ra s0 t n before after) (frame : NativeFrame sp 560)
    (tableOut : heapEnd ≤ t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ heapStart) : LiveFrame H before after :=
  ⟨fun e he x hx => by
    have b := w.ready.block_bounds (List.mem_cons_of_mem _ he)
    have hx' := hx
    unfold InExt at hx'
    exact w.live_byte_away frame he hx b (by omega)⟩

end OCaml.Vm.Boot.Startup
