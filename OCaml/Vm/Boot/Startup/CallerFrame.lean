import OCaml.Vm.Boot.Startup.StatCheckedFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- A callee preserves all memory at and above its entry stack boundary. -/
structure CallerFrame (sp : BitVec 64) (before after : Config) : Prop where
  byte : ∀ a, sp.toNat ≤ a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0

theorem CallerFrame.trans {sp before middle after} (first : CallerFrame sp before middle)
    (second : CallerFrame sp middle after) : CallerFrame sp before after :=
  ⟨fun a bound => (second.byte a bound).trans (first.byte a bound)⟩

theorem CallerFrame.of_memory {sp before after} (same : after.σ.mem = before.σ.mem) :
    CallerFrame sp before after := ⟨fun _ _ => by rw [same]⟩

theorem StatCheckedReturned.caller_frame {H capacity sp ra s0 n before after}
    (w : StatCheckedReturned H capacity sp ra s0 n before after)
    (frame : NativeFrame sp 544) : CallerFrame sp before after := by
  constructor
  intro a caller
  have short := frame.resize (small := 32) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 32) 512 := frame.nested (front := 32) (by decide)
  have unchanged := w.allocation.allocation.memory a
    (allocator_caller_outside nested.lower (by rw [short.stack_nat]; unfold nativeFrameBase; omega))
  change (w.allocated.σ.mem[a]?).getD 0 = (w.allocation.atMalloc.σ.mem[a]?).getD 0 at unchanged
  have restored : after.σ.mem = w.allocated.σ.mem := w.returned.memory
  rw [restored, unchanged, w.allocation.call.memory, w.allocation.setup.memory,
    frameOn_writeLog _ _ _ (statCheckedLog_inside short) a ⟨Or.inr caller, trivial⟩]
end OCaml.Vm.Boot.Startup
