import OCaml.Vm.Boot.Startup.ExtTablePublishNormalized
import OCaml.Vm.Boot.Startup.ExtTablePublishImage
import OCaml.Vm.Boot.Startup.ExtTableReady
import OCaml.Vm.Boot.Startup.ExtTableSite
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

def extTablePublishLog (t p : BitVec 64) : List WEntry :=
  [(t.toNat + Layout.off_ext_table_contents, 8, p)]
def extTablePublishRegs (t p : BitVec 64) : GRegs := [(8, t), (10, p)]

theorem extTablePublish_input {sp ra t p c} (leaf : LeafInput ra c) (site : ExtTableSite sp t)
    (regs : GHolds c.σ (extTablePublishRegs t p)) :
    BlockInput caml_ext_table_initX3dd8Seg 0x80003dd8#64 (extTablePublishRegs t p) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [8, 10]; decide
  shape := by change ChainOK _ [8, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := extTablePublish_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_ext_table_init_at_"
    exact (site.window 8 8 (by decide) (by decide) (by decide)).sd rfl rfl

theorem extTablePublish_image {sp t p} (frame : NativeFrame sp 16) (site : ExtTableSite sp t) :
    ImageOutside (extTablePublishLog t p) := by
  have image := site.image frame
  constructor <;> simp only [extTablePublishLog, OutLRange] <;> refine ⟨Or.inl ?_, trivial⟩ <;> omega

/-- Publish the newly allocated contents buffer into the table at `t`. -/
theorem ext_table_publish (c : Config) (sp ra t p : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (site : ExtTableSite sp t) (regs : GHolds c.σ (extTablePublishRegs t p)) :
    FnSummary 0x80003dd8#64 (fun d => d = c)
      (WriteRegistersPost [] (extTablePublishLog t p) c 0x80003ddc#64 p (extTablePublishRegs t p)) := by
  apply registers_of_blocks leaf.image (extTablePublish_image frame site)
    (block_summary _ _ _ _ _ (extTablePublish_input leaf site regs))
  · change [((t + 8#64).toNat, 8, p)] = _
    rw [site.addr (k := 8) (by decide)]
    rfl
  · rfl
  · rfl
  · rfl
  · decide

theorem ext_table_publish_ready {H capacity sp0 sp ra t before after p}
    (ready : RuntimeReady H capacity sp ra before) (frame : NativeFrame sp0 16) (site : ExtTableSite sp0 t)
    (post : WriteRegistersPost [] (extTablePublishLog t p) before 0x80003ddc#64 p (extTablePublishRegs t p) after) :
    RuntimeReady H capacity sp ra after := by
  apply ready.disjoint_log post (by decide) (by simp) (by decide)
    ((post.frame .x2 (by decide) (by decide)).trans ready.stack)
    ((post.frame .x1 (by decide) (by decide)).trans ready.raReg) ready.aligned
  · intro pin hp
    have low := site.pin frame (allocator_sources pin hp).before_startup_count
    exact ⟨Or.inl (by omega), trivial⟩
  · have h := site.domain frame
    simp only [extTablePublishLog, OutLRange]
    unfold Layout.off_ext_table_contents Layout.ext_table_bytes at *
    exact ⟨by omega, trivial⟩
  · have h := site.pool frame
    simp only [extTablePublishLog, OutLRange]
    unfold Layout.off_ext_table_contents Layout.ext_table_bytes at *
    exact ⟨by omega, trivial⟩
  · intro a owned
    have outside := site.foot frame owned
    unfold Layout.ext_table_bytes at outside
    simp only [extTablePublishLog, OutL, Layout.off_ext_table_contents]
    exact ⟨by omega, trivial⟩
end OCaml.Vm.Boot.Startup
