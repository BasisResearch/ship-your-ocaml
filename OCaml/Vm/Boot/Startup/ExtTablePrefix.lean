import OCaml.Vm.Boot.Startup.ExtTablePrefixNormalized
import OCaml.Vm.Boot.Startup.ExtTablePrefixCallInterface
import OCaml.Vm.Boot.Startup.ExtTableSite
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Primitives.Word32Access
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def extTableSave (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 16 [(0, s0), (8, ra)]
def extTableHeader (t n : BitVec 64) : List WEntry :=
  [(t.toNat + Layout.off_ext_table_size, 4, 0#64),
   (t.toNat + Layout.off_ext_table_capacity, 4, n)]
def extTableLog (sp ra s0 t n : BitVec 64) : List WEntry := extTableSave sp ra s0 ++ extTableHeader t n

/-- The contents request `n * sizeof(void *)`, as the generated `slli` computes it. -/
def extTableRequest (n : BitVec 64) : BitVec 64 := Sail.shift_bits_left n (3#6)

def extTableInput (sp ra s0 t n : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (1, ra), (10, t), (11, n)]
def extTableRegs (sp ra t n : BitVec 64) : GRegs :=
  [(10, extTableRequest n), (8, t), (2, nativeStack sp 16), (1, ra), (11, n)]

def extTableWindows (sp t : BitVec 64) : List W :=
  [⟨nativeFrameBase sp 16, sp.toNat⟩, ⟨t.toNat, t.toNat + Layout.ext_table_bytes⟩]

theorem extTableLog_inside {sp ra s0 t n} (frame : NativeFrame sp 16) :
    LogInW (extTableWindows sp t) (extTableLog sp ra s0 t n) := by
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
  · unfold Layout.off_ext_table_size Layout.ext_table_bytes; omega
  · unfold Layout.off_ext_table_capacity Layout.ext_table_bytes; omega

theorem extTable_image_outside {sp ra s0 t n} (frame : NativeFrame sp 16) (site : ExtTableSite sp t) :
    ImageOutside (extTableLog sp ra s0 t n) := by
  have lower := frame.lower
  have image := site.image frame
  have bounds : Image.textBase + Image.textSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.rodataBase + Image.rodataSize ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows (extTableLog_inside frame)
  all_goals exact ⟨Or.inl (by change _ ≤ nativeFrameBase sp 16; unfold nativeFrameBase; omega), Or.inl (by dsimp only; omega), trivial⟩

theorem extTablePrefix_input {sp ra s0 t n c} (leaf : LeafInput ra c) (frame : NativeFrame sp 16)
    (site : ExtTableSite sp t) (regs : GHolds c.σ (extTableInput sp ra s0 t n)) :
    BlockInput extTablePrefixSave 0x80003db8#64 (extTableInput sp ra s0 t n) [] c where
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
    · exact (site.window 0 4 (by decide) (by decide) (by decide)).sw rfl rfl
    · exact (site.window 4 4 (by decide) (by decide) (by decide)).sw rfl rfl

local macro "ext_prefix_nf" : tactic =>
  `(tactic| simp only [extTablePrefixSave, evalBlocks, evalBlock, SegEvalState.init,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    extTableInput, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
    Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem extTablePrefix_log {sp ra s0 t n : BitVec 64} (site : ExtTableSite sp t) :
    (evalBlocks extTablePrefixSave (SegEvalState.init (extTableInput sp ra s0 t n) [])).log =
      extTableLog sp ra s0 t n := by
  ext_prefix_nf
  change [((nativeStack sp 16 + 0#64).toNat, 8, s0),
    ((nativeStack sp 16 + 8#64).toNat, 8, ra),
    ((t + 0#64).toNat, 4, 0#64),
    ((t + 4#64).toNat, 4, n)] = _
  rw [site.addr (k := 0) (by decide), site.addr (k := 4) (by decide)]
  rfl

theorem extTablePrefix_regs (sp ra s0 t n : BitVec 64) :
    (evalBlocks extTablePrefixSave (SegEvalState.init (extTableInput sp ra s0 t n) [])).regs =
      extTableRegs sp ra t n := by
  ext_prefix_nf
  change [(10, Sail.shift_bits_left n (3#6)), (8, t + 0#64),
    (2, nativeStack sp 16), (1, ra), (11, n)] = _
  rw [BitVec.add_zero]
  rfl

/-- Initialize an ext_table header at `t` with capacity `n`, save the caller
and request `n` pointer slots using the actual checked-allocation call seam. -/
theorem ext_table_prefix (c : Config) (sp ra s0 t n : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (site : ExtTableSite sp t) (regs : GHolds c.σ (extTableInput sp ra s0 t n)) :
    FnSummary 0x80003db8#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 10] (extTableLog sp ra s0 t n) c jal_80003dd4_call.pc (extTableRequest n)
        (extTableRegs sp ra t n)) := by
  apply registers_of_blocks leaf.image (extTable_image_outside frame site)
    (block_summary _ _ _ _ _ (extTablePrefix_input leaf frame site regs))
  · exact extTablePrefix_log site
  · rfl
  · exact extTablePrefix_regs sp ra s0 t n
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
