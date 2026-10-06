import OCaml.Vm.Boot.Startup.SearchExeDecomposeNormalized
import OCaml.Vm.Boot.Startup.SearchExeDecomposeCallInterface
import OCaml.Vm.Boot.Startup.SearchExeSearchNormalized
import OCaml.Vm.Boot.Startup.SearchExeSearchCallInterface
import OCaml.Vm.Boot.Startup.SearchExeFreeTofreeNormalized
import OCaml.Vm.Boot.Startup.SearchExeFreeTofreeCallInterface
import OCaml.Vm.Boot.Startup.SearchExeFreeTableNormalized
import OCaml.Vm.Boot.Startup.SearchExeFreeTableCallInterface
import OCaml.Vm.Boot.Startup.SearchExeReturnNormalized
import OCaml.Vm.Boot.Startup.SearchExeReturnImage
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- `caml_decompose_path(&path, getenv("PATH"))`. -/
theorem search_exe_decompose (c : Config) (ra sp env : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, env), (2, sp)]) :
    FnSummary 0x8002555c#64 (fun d => d = c)
      (WriteRegistersPost ([11, 10] ++ [1]) [] c jal_80025564_call.target sp
        ((1, jal_80025564_call.link) :: [(10, sp), (11, env), (2, sp)])) := by
  apply block_then_call c jal_80025564_call_shape jal_80025564_call_decode (fun _ h => jal_80025564_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput searchExeDecomposeSave 0x8002555c#64 [(10, env), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := searchExeDecompose_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_" }))
  · rfl
  · rfl
  · change [(10, sp + 0#64), (11, env + 0#64), (2, sp)] = _
    rw [BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide

/-- `caml_search_in_path(&path, name)`, keeping `tofree` in s1. -/
theorem search_exe_search (c : Config) (ra sp name tofree : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, name), (10, tofree), (2, sp)]) :
    FnSummary 0x80025568#64 (fun d => d = c)
      (WriteRegistersPost ([11, 9, 10] ++ [1]) [] c jal_80025574_call.target sp
        ((1, jal_80025574_call.link) :: [(10, sp), (9, tofree), (11, name), (8, name), (2, sp)])) := by
  apply block_then_call c jal_80025574_call_shape jal_80025574_call_decode (fun _ h => jal_80025574_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput searchExeSearchSave 0x80025568#64
        [(8, name), (10, tofree), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10, 2]; decide
      shape := by change ChainOK _ [8, 10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := searchExeSearch_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_" }))
  · rfl
  · rfl
  · change [(10, sp + 0#64), (9, tofree + 0#64), (11, name + 0#64), (8, name), (2, sp)] = _
    rw [BitVec.add_zero, BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide

/-- Keep the result in s0 and call `caml_stat_free(tofree)`. -/
theorem search_exe_free_tofree (c : Config) (ra result tofree : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, result), (9, tofree)]) :
    FnSummary 0x80025578#64 (fun d => d = c)
      (WriteRegistersPost ([8, 10] ++ [1]) [] c jal_80025580_call.target tofree
        ((1, jal_80025580_call.link) :: [(10, tofree), (8, result), (9, tofree)])) := by
  apply block_then_call c jal_80025580_call_shape jal_80025580_call_decode (fun _ h => jal_80025580_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput searchExeFreeTofreeSave 0x80025578#64
        [(10, result), (9, tofree)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 9]; decide
      shape := by change ChainOK _ [10, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := searchExeFreeTofree_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_" }))
  · rfl
  · rfl
  · change [(10, tofree + 0#64), (8, result + 0#64), (9, tofree)] = _
    rw [BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide

/-- `caml_ext_table_free(&path, 0)`. -/
theorem search_exe_free_table (c : Config) (ra sp : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, sp)]) :
    FnSummary 0x80025584#64 (fun d => d = c)
      (WriteRegistersPost ([10, 11] ++ [1]) [] c jal_8002558c_call.target sp
        ((1, jal_8002558c_call.link) :: [(11, 0#64), (10, sp), (2, sp)])) := by
  apply block_then_call c jal_8002558c_call_shape jal_8002558c_call_decode (fun _ h => jal_8002558c_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput searchExeFreeTableSave 0x80025584#64 [(2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2]; decide
      shape := by change ChainOK _ [2] _; decide
      tick := leaf.tick
      facts := by
        have code := searchExeFreeTable_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_" }))
  · rfl
  · rfl
  · change [(11, 0#64 + 0#64), (10, sp + 0#64), (2, sp)] = _
    rw [BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide

def searchExeReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 48 + 40), read8 c.σ.mem (nativeFrameBase sp 48 + 32),
   read8 c.σ.mem (nativeFrameBase sp 48 + 24)]

/-- Restore the caller and return the resolved name. -/
theorem search_exe_return (c : Config) (sp ra s0 s1 result oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, nativeStack sp 48), (8, result)])
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 48 + 40) 8 = ra)
    (savedS0 : bytesT c.σ.mem (nativeFrameBase sp 48 + 32) 8 = s0)
    (savedS1 : bytesT c.σ.mem (nativeFrameBase sp 48 + 24) 8 = s1) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80025590#64 (fun d => d = c)
      (WriteRegistersPost [1, 10, 8, 9, 2] [] c ra result [(2, sp), (9, s1), (8, s0), (10, result), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_search_exe_in_pathX5590Seg 0x80025590#64
        [(2, nativeStack sp 48), (8, result)] (searchExeReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8]; decide
      shape := by change ChainOK _ [2, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := searchExeReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_"
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · change [(2, nativeStack sp 48 + 48#64), (9, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 24))),
      (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 32))), (10, result + 0#64),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)))] = _
    rw [read8_value, read8_value, read8_value, savedRa, savedS0, savedS1, BitVec.add_zero, nativeStack_restore]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
