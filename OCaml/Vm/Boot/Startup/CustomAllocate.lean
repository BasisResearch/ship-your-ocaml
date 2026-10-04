import OCaml.Vm.Boot.Startup.CustomPublishReady
import OCaml.Vm.Boot.Startup.CustomReadback
import OCaml.Vm.Boot.Startup.StatCheckedFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem customTable_allocator_outside {H a}
    (lo : Layout.sym_custom_ops_table ≤ a) (hi : a < Layout.sym_custom_ops_table + 8) :
    ¬ vsaFoot H a := by
  intro owned
  unfold vsaFoot allocGlobal InRange at owned
  unfold Layout.sym_custom_ops_table heapStart at *
  omega

structure CustomRegistered (H : List (Nat × Nat)) (capacity : Nat) (kind : CustomKind)
    (sp s0 head : BitVec 64) (before after : Config) where
  returned : Config
  allocated : Config
  allocation : StatCheckedReturned H capacity sp kind.entry s0 16#64 before returned
  allocatedEq : allocation.allocated = allocated
  publication : WriteRegistersPost [8, 15, 14] (customPublishLog kind (vsaReg allocated 10) head)
    returned kind.exit (vsaReg allocated 10) (customPublishRegs kind (vsaReg allocated 10) head) after
  ready : RuntimeReady (((vsaReg allocated 10).toNat, 16) :: H) capacity sp kind.entry after

/-- One complete registration consists of the checked allocation and the shared
native prepend protocol; prior list bytes remain outside allocator ownership. -/
theorem custom_allocate_publish (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (kind : CustomKind) (sp s0 head : BitVec 64)
    (ready : RuntimeReady H (capacity + 32) sp kind.entry c)
    (frame : NativeFrame sp 544) (saved0 : gprGet c.σ 8 = some s0)
    (parked : kind ≠ .int32 → s0 = customTable)
    (request : gprGet c.σ 10 = some 16#64)
    (headWord : bytesT c.σ.mem Layout.sym_custom_ops_table 8 = head) :
    FnSummary 0x8000bb2c#64 (fun d => d = c)
      (fun after => Nonempty (CustomRegistered H capacity kind sp s0 head c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨returned, run1, ⟨w⟩⟩ :=
    (stat_checked c H capacity 32 sp kind.entry s0 16#64 ready frame saved0 request
      (by constructor <;> decide)).run c ⟨pc, rfl⟩
  let p := vsaReg w.allocated 10
  have region : ZeroPairRegion p.toNat 1 :=
    ⟨w.allocation.allocation.result.fresh.lo, w.allocation.allocation.result.fresh.hi,
      w.allocation.allocation.result.align⟩
  have preserved : bytesT returned.σ.mem Layout.sym_custom_ops_table 8 = head := by
    rw [word_observed (m := c.σ.mem) Layout.sym_custom_ops_table (fun i hi =>
      w.framed_byte frame (by unfold Layout.sym_custom_ops_table heapEnd; omega)
        (customTable_allocator_outside (by omega) (by omega)))]
    exact headWord
  have regs : GHolds returned.σ (customPublishInput kind p) := by
    have r0 := gholds_lookup (n := 8) _ w.returned.regs (by rfl)
    cases kind
    · exact ⟨w.returned.result, trivial⟩
    all_goals exact ⟨by rw [r0, parked (by decide)], w.returned.result, trivial⟩
  have input : CustomPublishInput kind p head kind.entry returned :=
    ⟨w.ready.toLeafInput, regs, region, preserved⟩
  obtain ⟨after, run2, published⟩ := (custom_publish returned kind p head kind.entry input).run
    returned ⟨w.returned.pc, rfl⟩
  exact ⟨after, run1.trans run2, ⟨returned, w.allocated, w, rfl, published,
    custom_publish_ready w.ready region (by simp [p]) published⟩⟩
end OCaml.Vm.Boot.Startup
