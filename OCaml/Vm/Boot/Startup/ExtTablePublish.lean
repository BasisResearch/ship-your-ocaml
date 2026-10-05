import OCaml.Vm.Boot.Startup.ExtTablePublishNormalized
import OCaml.Vm.Boot.Startup.ExtTablePublishImage
import OCaml.Vm.Boot.Startup.ExtTableReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

def extTablePublishLog (p : BitVec 64) : List WEntry :=
  [(Layout.sym_caml_shared_libs_path + Layout.off_ext_table_contents, 8, p)]
def extTablePublishRegs (p : BitVec 64) : GRegs := [(8, sharedTableAddress), (10, p)]

theorem extTablePublish_input {ra p c} (leaf : LeafInput ra c) (regs : GHolds c.σ (extTablePublishRegs p)) :
    BlockInput caml_ext_table_initX3dd8Seg 0x80003dd8#64 (extTablePublishRegs p) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [8, 10]; decide
  shape := by change ChainOK _ [8, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := extTablePublish_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_ext_table_init_at_"
    exact (show WriteWindow (sharedTableAddress + 8#64) 8 from by constructor <;> decide).sd rfl rfl

/-- Publish the newly allocated contents buffer into the native ext_table. -/
theorem ext_table_publish (c : Config) (ra p : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (extTablePublishRegs p)) :
    FnSummary 0x80003dd8#64 (fun d => d = c)
      (WriteRegistersPost [] (extTablePublishLog p) c 0x80003ddc#64 p (extTablePublishRegs p)) := by
  apply registers_of_blocks leaf.image (by constructor <;> change OutLRange _ _ _ <;> simp only [extTablePublishLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (extTablePublish_input leaf regs))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

theorem ext_table_publish_ready {H capacity sp ra before after p}
    (ready : RuntimeReady H capacity sp ra before)
    (post : WriteRegistersPost [] (extTablePublishLog p) before 0x80003ddc#64 p (extTablePublishRegs p) after) :
    RuntimeReady H capacity sp ra after := by
  apply ready.disjoint_log post (by decide) (by simp) (by decide)
    ((post.frame .x2 (by decide) (by decide)).trans ready.stack)
    ((post.frame .x1 (by decide) (by decide)).trans ready.raReg) ready.aligned
  · intro pin hp
    have low := (allocator_sources pin hp).before_startup_count
    have bounds : Layout.sym_startup_count ≤ Layout.sym_caml_shared_libs_path + Layout.off_ext_table_contents := by decide
    exact ⟨Or.inl (by omega), trivial⟩
  · simp only [extTablePublishLog, OutLRange]; decide
  · simp only [extTablePublishLog, OutLRange]; decide
  · intro a owned
    have outside := sharedTable_outside_allocator owned
    unfold Layout.ext_table_bytes at outside
    simp only [extTablePublishLog, OutL, Layout.off_ext_table_contents]
    exact ⟨by omega, trivial⟩
end OCaml.Vm.Boot.Startup
