import OCaml.Vm.Boot.Startup.CustomPublish
import OCaml.Vm.Boot.Startup.RuntimeLog
import OCaml.Vm.Boot.Startup.StartupAuxMemory
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem customPublish_out_byte {kind p head a}
    (region : ZeroPairRegion p.toNat 1)
    (payload : a < p.toNat ∨ p.toNat + 16 ≤ a)
    (table : a < Layout.sym_custom_ops_table ∨ Layout.sym_custom_ops_table + 8 ≤ a) :
    OutL (customPublishLog kind p head) a := by
  simp only [customPublishLog, OutL, customPublish_second region]
  exact ⟨by omega, by omega, table, trivial⟩

theorem customPublish_out_low {kind p head a}
    (region : ZeroPairRegion p.toNat 1) (below : a + 8 ≤ heapStart)
    (table : a + 8 ≤ Layout.sym_custom_ops_table ∨ Layout.sym_custom_ops_table + 8 ≤ a) :
    OutLRange (customPublishLog kind p head) a 8 := by
  have lower := region.lower
  simp only [customPublishLog, OutLRange, customPublish_second region]
  exact ⟨Or.inl (by omega), Or.inl (by omega), table, trivial⟩

/-- Publishing a fresh custom node changes neither allocator ownership nor the
runtime platform, pool flag, domain pointer or caller registers. -/
theorem custom_publish_ready {H capacity sp ra before after kind p head}
    (ready : RuntimeReady H capacity sp ra before) (region : ZeroPairRegion p.toNat 1)
    (member : (p.toNat, 16) ∈ H)
    (post : WriteRegistersPost [8, 15, 14] (customPublishLog kind p head) before kind.exit p
      (customPublishRegs kind p head) after) : RuntimeReady H capacity sp ra after := by
  apply ready.disjoint_log post (by decide) (by simp only [customPublishRegs, keysG]; decide) (by decide)
    ((post.frame .x2 (by decide) (by decide)).trans ready.stack)
    ((post.frame .x1 (by decide) (by decide)).trans ready.raReg) ready.aligned
  · intro pin hp
    have source := allocator_sources pin hp
    have below := source.geometry.high
    have table := source.before_startup_count
    have bound : Layout.sym_startup_count ≤ Layout.sym_custom_ops_table := by decide
    exact customPublish_out_byte region (Or.inl (Nat.lt_of_lt_of_le below region.lower)) (Or.inl (by omega))
  · exact customPublish_out_low region (by decide) (Or.inr (by decide))
  · exact customPublish_out_low region (by decide) (Or.inl (by decide))
  · intro a owned
    apply customPublish_out_byte region (allocator_payload_outside member region.lower owned)
    unfold vsaFoot allocGlobal InRange at owned
    unfold Layout.sym_custom_ops_table heapStart at *
    omega
end OCaml.Vm.Boot.Startup
