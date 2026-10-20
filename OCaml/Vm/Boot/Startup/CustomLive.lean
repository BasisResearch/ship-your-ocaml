import OCaml.Vm.Boot.Startup.CustomFinish
import OCaml.Vm.Boot.Startup.CustomRegistered
import OCaml.Vm.Boot.Startup.CustomPublishReady
import OCaml.Vm.Boot.Startup.StatCheckedFrame
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.ReadyPerm
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! caml_init_custom_operations keeps every owned block: each checked
allocation keeps bytes outside the allocator's footprint, and each prepend
writes only the fresh node and the global list head. -/

/-- A store log confined to a native frame above the arena keeps every owned block. -/
theorem LiveFrame.of_stack {H : List (Nat × Nat)} {before after : Config} {log : List WEntry} {sp : BitVec 64}
    {size : Nat} (memory : after.σ.mem = writeLog before.σ.mem log)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log) (frame : NativeFrame sp size)
    (bounds : ∀ e ∈ H, e.1 + e.2 ≤ heapEnd) : LiveFrame H before after :=
  ⟨fun e he x hx => by
    have b := bounds e he
    have lower := frame.lower
    unfold InExt at hx
    rw [memory, frameOn_writeLog _ _ _ inside x ⟨Or.inl (show x < nativeFrameBase sp size by
      unfold nativeFrameBase at *; omega), trivial⟩]⟩

theorem CustomRegistered.live {H : List (Nat × Nat)} {capacity : Nat} {kind : CustomKind} {sp s0 head : BitVec 64}
    {before after : Config} (w : CustomRegistered H capacity kind sp s0 head before after) (frame : NativeFrame sp 544) :
    LiveFrame H before after := by
  have region := w.region
  have fresh : FreshBlock vsaLayoutP H (vsaReg w.allocation.allocated 10).toNat (16#64).toNat :=
    w.allocation.allocation.allocation.result.fresh
  rw [w.allocatedEq] at fresh
  constructor
  intro e he x hx
  have b := w.ready.block_bounds (List.mem_cons_of_mem _ he)
  have hx' := hx
  unfold InExt at hx'
  have apart := FreshBlock.apart fresh (q := e.1) (m := e.2) he (by decide) (by omega)
  have n16 : (16#64).toNat = 16 := rfl
  rw [n16] at apart
  have table : Layout.sym_custom_ops_table + 8 ≤ heapStart := by decide
  rw [w.publication.memory, writeLog_out _ _ _ (customPublish_out_byte region (by omega) (Or.inr (by omega)))]
  exact w.allocation.framed_byte frame (by omega) (owned_not_foot (by omega) ⟨e, he, hx⟩)

theorem CustomNextRegistered.live {H : List (Nat × Nat)} {capacity : Nat} {kind : CustomLater} {sp head : BitVec 64}
    {before after : Config} (w : CustomNextRegistered H capacity kind sp head before after) (frame : NativeFrame sp 544) :
    LiveFrame H before after :=
  (LiveFrame.of_memory w.setup.memory).trans (w.registration.live frame)

theorem CustomFirstRegistered.live {H : List (Nat × Nat)} {capacity : Nat} {sp ra s0 head : BitVec 64}
    {before after : Config} (w : CustomFirstRegistered H capacity sp ra s0 head before after) (frame : NativeFrame sp 560) :
    LiveFrame H before after := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  have bounds : ∀ e ∈ H, e.1 + e.2 ≤ heapEnd := fun e he =>
    (w.registration.ready.block_bounds (List.mem_cons_of_mem _ he)).2
  exact (LiveFrame.of_stack w.setup.memory (customSaveLog_inside short) short bounds).trans
    ((LiveFrame.of_memory w.call.memory).trans (w.registration.live nested))

/-- All four registrations keep the initializer's incoming owned blocks. -/
theorem CustomNodes.live {H : List (Nat × Nat)} {capacity : Nat} {sp ra s0 head : BitVec 64} {before after : Config}
    (w : CustomNodes H capacity sp ra s0 head before after) (frame : NativeFrame sp 560) :
    LiveFrame H before after := by
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  have s1 : ∀ e ∈ H, e ∈ w.H1 := fun e he => by rw [w.heap1]; exact List.mem_cons_of_mem _ he
  have s2 : ∀ e ∈ H, e ∈ w.H2 := fun e he => by rw [w.heap2]; exact List.mem_cons_of_mem _ (s1 e he)
  have s3 : ∀ e ∈ H, e ∈ w.H3 := fun e he => by rw [w.heap3]; exact List.mem_cons_of_mem _ (s2 e he)
  exact (w.int32.live frame).trans (((w.nativeint.live nested).mono s1).trans
    (((w.int64.live nested).mono s2).trans ((w.bigarray.live nested).mono s3)))

theorem CustomReturned.live {H : List (Nat × Nat)} {capacity : Nat} {sp ra s0 head : BitVec 64} {before after : Config}
    (w : CustomReturned H capacity sp ra s0 head before after) (frame : NativeFrame sp 560) :
    LiveFrame H before after :=
  (w.nodes.live frame).trans (LiveFrame.of_memory w.post.memory)
end OCaml.Vm.Boot.Startup
