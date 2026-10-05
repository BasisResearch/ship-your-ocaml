import OCaml.Vm.Boot.Startup.ExtTablePrefixNormalized
import OCaml.Vm.Boot.Startup.ExtTablePrefixCallInterface
import OCaml.Vm.Boot.Startup.CamlSharedTable
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Primitives.Word32Access
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def extTableSave (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 16 [(0, s0), (8, ra)]
def extTableHeader : List WEntry :=
  [(Layout.sym_caml_shared_libs_path + Layout.off_ext_table_size, 4, 0#64),
   (Layout.sym_caml_shared_libs_path + Layout.off_ext_table_capacity, 4, 8#64)]
def extTableLog (sp ra s0 : BitVec 64) : List WEntry := extTableSave sp ra s0 ++ extTableHeader

def extTableInput (sp ra s0 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (1, ra), (10, sharedTableAddress), (11, 8#64)]
def extTableRegs (sp ra : BitVec 64) : GRegs :=
  [(10, 64#64), (8, sharedTableAddress), (2, nativeStack sp 16), (1, ra), (11, 8#64)]

def extTableWindows (sp : BitVec 64) : List W :=
  [⟨nativeFrameBase sp 16, sp.toNat⟩,
   ⟨Layout.sym_caml_shared_libs_path, Layout.sym_caml_shared_libs_path + Layout.ext_table_bytes⟩]

theorem extTableLog_inside {sp ra s0} (frame : NativeFrame sp 16) :
    LogInW (extTableWindows sp) (extTableLog sp ra s0) := by
  have address0 := frame.slot_nat (off := 0) (by decide)
  have address8 := frame.slot_nat (off := 8) (by decide)
  have low := frame.lower
  simp only [extTableWindows, extTableLog, extTableSave, nativeWordLog, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, extTableHeader, nativeStack, frame.address 0 (by decide),
    frame.address 8 (by decide), address0, address8, LogInW, InsideW]
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inr (Or.inl ?_), Or.inr (Or.inl ?_), trivial⟩
  · omega
  · unfold nativeFrameBase; omega
  · omega
  · unfold nativeFrameBase; omega
  · constructor <;> decide
  · constructor <;> decide

theorem extTable_image_outside {sp ra s0} (frame : NativeFrame sp 16) : ImageOutside (extTableLog sp ra s0) := by
  have lower := frame.lower
  have bounds : Image.textBase + Image.textSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.rodataBase + Image.rodataSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.textBase + Image.textSize ≤ Layout.sym_caml_shared_libs_path ∧
      Image.rodataBase + Image.rodataSize ≤ Layout.sym_caml_shared_libs_path := by decide
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows (extTableLog_inside frame)
  all_goals exact ⟨Or.inl (by change _ ≤ nativeFrameBase sp 16; unfold nativeFrameBase; omega), Or.inl (by dsimp only; omega), trivial⟩

theorem extTablePrefix_input {sp ra s0 c} (leaf : LeafInput ra c) (frame : NativeFrame sp 16)
    (regs : GHolds c.σ (extTableInput sp ra s0)) :
    BlockInput extTablePrefixSave 0x80003db8#64 (extTableInput sp ra s0) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 8, 1, 10, 11]; decide
  shape := by change ChainOK _ [2, 8, 1, 10, 11] _; decide
  tick := leaf.tick
  facts := by
    have code := extTablePrefix_code leaf.image
    have slot (off : Nat) (bound : off + 8 ≤ 16) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 16 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, frame.address _ (by omega)]
      exact frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_ext_table_init_at_"
    · exact (slot 0 (by decide) (by decide)).sd rfl rfl
    · exact (slot 8 (by decide) (by decide)).sd rfl rfl
    · exact (show WriteWindow sharedTableAddress 4 from by constructor <;> decide).sw rfl rfl
    · exact (show WriteWindow (sharedTableAddress + 4#64) 4 from by constructor <;> decide).sw rfl rfl

local macro "ext_prefix_nf" : tactic =>
  `(tactic| simp only [extTablePrefixSave, evalBlocks, evalBlock, SegEvalState.init,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    extTableInput, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
    Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem extTablePrefix_log (sp ra s0 : BitVec 64) :
    (evalBlocks extTablePrefixSave (SegEvalState.init (extTableInput sp ra s0) [])).log = extTableLog sp ra s0 := by
  ext_prefix_nf
  change [((nativeStack sp 16 + 0#64).toNat, 8, s0),
    ((nativeStack sp 16 + 8#64).toNat, 8, ra),
    ((sharedTableAddress + 0#64).toNat, 4, 0#64),
    ((sharedTableAddress + 4#64).toNat, 4, 8#64)] = _
  rw [show (sharedTableAddress + 0#64).toNat = Layout.sym_caml_shared_libs_path + Layout.off_ext_table_size from by decide,
    show (sharedTableAddress + 4#64).toNat = Layout.sym_caml_shared_libs_path + Layout.off_ext_table_capacity from by decide]
  rfl

theorem extTablePrefix_regs (sp ra s0 : BitVec 64) :
    (evalBlocks extTablePrefixSave (SegEvalState.init (extTableInput sp ra s0) [])).regs = extTableRegs sp ra := by
  ext_prefix_nf
  change [(10, Sail.shift_bits_left (8#64) (3#6)), (8, sharedTableAddress + 0#64),
    (2, nativeStack sp 16), (1, ra), (11, 8#64)] = _
  rw [show Sail.shift_bits_left (8#64) (3#6) = 64#64 from by decide, BitVec.add_zero]
  rfl

/-- Initialize the shared-library table header, save its caller and request
space for eight pointers using the actual checked-allocation call seam. -/
theorem ext_table_prefix (c : Config) (sp ra s0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ (extTableInput sp ra s0)) :
    FnSummary 0x80003db8#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 10] (extTableLog sp ra s0) c jal_80003dd4_call.pc 64#64
        (extTableRegs sp ra)) := by
  apply registers_of_blocks leaf.image (extTable_image_outside frame)
    (block_summary _ _ _ _ _ (extTablePrefix_input leaf frame regs))
  · exact extTablePrefix_log sp ra s0
  · rfl
  · exact extTablePrefix_regs sp ra s0
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
