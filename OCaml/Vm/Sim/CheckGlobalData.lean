import OCaml.Vm.Sim.CheckGlobalDataRows
import OCaml.Vm.Sim.CheckGlobalDataImage
import OCaml.Vm.Primitives.Control
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.ImageFrame
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The normal check returns when the global-data value is a block pointer. -/
structure CheckGlobalDataInput (ra : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  returnReg : gpr c 1 = some ra
  aligned : ra.toNat % 4 = 0
  globalBlock : word c Layout.sym_caml_global_data &&& 1#64 = 0#64

/-- The check preserves its argument, memory and all registers except native scratch. -/
structure CheckGlobalDataPost (before : Config) (ra : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some ra
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut ([Register.x15] ++ noiseRegs) before.σ after.σ

def checkGlobalBlocks : List BBlock := check_global_dataXcde0FSeg ++ check_global_dataXcdf0Seg

theorem check_global_input {ra : BitVec 64} {c : Config} (h : CheckGlobalDataInput ra c) :
    BlockInput checkGlobalBlocks 0x8000cde0#64 [(1, ra)] [read8 c.σ.mem Layout.sym_caml_global_data] c := by
  refine ⟨h.good, h.good.minstret, ⟨h.returnReg, trivial⟩, ?_, ?_, ?_, h.tick⟩
  · change KeysOK [1]; decide
  · have code := check_global_data_loaded h.image
    chain_facts code with "Vsa.Sim.Code.check_global_data_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_caml_global_data)
        (by constructor <;> decide) rfl
        (by
          change (0x8000cde0#64 + sign_extend (m := 64) ((0x00058#20) +++ 0#12)) +
            sign_extend (m := 64) (0xa08#12) = BitVec.ofNat 64 Layout.sym_caml_global_data
          decide)
      change LPins8 c.σ.mem Layout.sym_caml_global_data (read8 c.σ.mem Layout.sym_caml_global_data)
      exact read8_pins c.σ.mem Layout.sym_caml_global_data
    · change (bytesVal .ld (read8 c.σ.mem Layout.sym_caml_global_data) &&& 1#64 != 0#64) = false
      rw [read8_value]
      change (word c Layout.sym_caml_global_data &&& 1#64 != 0#64) = false
      rw [h.globalBlock]; decide
    · change (Sail.BitVec.update (ra + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt ra h.aligned]
      exact h.aligned
  · change ChainOK 0x8000cde0#64 [1] checkGlobalBlocks; decide

/-- Complete check_global_data normal return over the generated whole-function CFG. -/
theorem check_global_data_summary {ra : BitVec 64} {c : Config} (h : CheckGlobalDataInput ra c) :
    FnSummary 0x8000cde0#64 (fun start => start = c) (CheckGlobalDataPost c ra) := by
  have summary := block_summary _ _ _ _ _ (check_global_input h)
  apply summary.weaken (fun _ eq => eq)
  intro after post
  have log : (evalBlocks checkGlobalBlocks (SegEvalState.init [(1, ra)]
      [read8 c.σ.mem Layout.sym_caml_global_data])).log = [] := by rfl
  have memory : after.σ.mem = c.σ.mem := by
    simpa only [log, writeLog, List.foldl_nil] using post.memory
  refine ⟨post.good, image_of_writeLog (log := []) h.image ⟨trivial, trivial⟩ memory, post.tick, ?_, memory, post.output, ?_⟩
  · have target : evalBlocksPC 0x8000cde0#64 (SegEvalState.init [(1, ra)]
        [read8 c.σ.mem Layout.sym_caml_global_data]) checkGlobalBlocks = ra := by
      change Sail.BitVec.update (ra + sign_extend (m := 64) (0#12)) 0 0#1 = ra
      exact ret_tgt ra h.aligned
    exact post.pc.trans (congrArg some target)
  · intro r outside
    apply post.frame r
    · intro q member
      exact outside q (List.mem_append_right _ member)
    · intro n member
      have written : ∀ n ∈ wrChain checkGlobalBlocks, gprReg n ∈ [Register.x15] ++ noiseRegs := by decide
      exact outside _ (written n member)

end OCaml.Vm.Sim
