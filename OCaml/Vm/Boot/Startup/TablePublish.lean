import OCaml.Vm.Boot.Startup.MinorTablePublish0Normalized
import OCaml.Vm.Boot.Startup.MinorTablePublish1Normalized
import OCaml.Vm.Boot.Startup.MinorTablePublish2Normalized
import OCaml.Vm.Boot.Startup.TableReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The three source minor-table fields share one publication protocol. -/
inductive MinorTableSlot where
  | refs | ephemerons | customs
  deriving DecidableEq

def MinorTableSlot.offset : MinorTableSlot → Nat
  | .refs => Layout.off_ref_table
  | .ephemerons => Layout.off_ephe_ref_table
  | .customs => Layout.off_custom_table

def MinorTableSlot.entry : MinorTableSlot → BitVec 64
  | .refs => 0x8000982c#64
  | .ephemerons => 0x80009854#64
  | .customs => 0x8000987c#64

def MinorTableSlot.exit : MinorTableSlot → BitVec 64
  | .refs => 0x8000983c#64
  | .ephemerons => 0x80009864#64
  | .customs => 0x8000988c#64

def MinorTableSlot.blocks : MinorTableSlot → List BBlock
  | .refs => caml_alloc_minor_tablesX982cFSeg
  | .ephemerons => caml_alloc_minor_tablesX9854FSeg
  | .customs => caml_alloc_minor_tablesX987cFSeg

def MinorTableSlot.address (slot : MinorTableSlot) : BitVec 64 :=
  firstDomainPtr + BitVec.ofNat 64 slot.offset

def tablePublishInput (p : BitVec 64) : GRegs :=
  [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, p), (9, firstDomainPtr)]

def tablePublishLog (slot : MinorTableSlot) (p : BitVec 64) : List WEntry :=
  [(slot.address.toNat, 8, p)]

def tablePublishLoads (slot : MinorTableSlot) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :=
  [read8 m Layout.sym_Caml_state, read8 (writeLog m (tablePublishLog slot p)) slot.address.toNat]

def tablePublishRegs (p : BitVec 64) : GRegs :=
  [(10, p), (15, firstDomainPtr), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (9, firstDomainPtr)]

local macro "table_publish_nf" : tactic =>
  `(tactic| simp only [minortablepublish0_line_8000982c, minortablepublish0_line_80009830,
    minortablepublish0_line_80009834, minortablepublish1_line_80009854, minortablepublish1_line_80009858,
    minortablepublish1_line_8000985c, minortablepublish2_line_8000987c, minortablepublish2_line_80009880,
    minortablepublish2_line_80009884, MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, tablePublishInput, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

structure TablePublishInput (p ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  globalReg : gprGet c.σ 8 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  pointer : gprGet c.σ 10 = some p
  domain : gprGet c.σ 9 = some firstDomainPtr
  domainWord : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr
  nonzero : p ≠ 0#64

theorem tablePublish_input (slot : MinorTableSlot) {p ra c} (h : TablePublishInput p ra c) :
    BlockInput slot.blocks slot.entry (tablePublishInput p) (tablePublishLoads slot p c.σ.mem) c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.globalReg, h.pointer, h.domain, trivial⟩
  keys := by change KeysOK [8, 10, 9]; decide
  shape := by cases slot <;> change ChainOK _ [8, 10, 9] _ <;> decide
  tick := h.tick
  facts := by
    have code := minorTables_code h.image
    have domain : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = firstDomainPtr :=
      (read8_value _ _).trans h.domainWord
    have loaded : bytesVal .ld (read8 (writeLog c.σ.mem (tablePublishLog slot p)) slot.address.toNat) = p := by
      rw [read8_value]
      exact word_writeLog _ _ _
    cases slot <;> chain_facts code with "Vsa.Sim.Code.caml_alloc_minor_tables_at_"
    all_goals try table_publish_nf
    all_goals try simp only [tablePublishLoads, List.headD_cons, List.tail_cons, domain, loaded]
    all_goals first
      | (constructor; decide; exact read8_pins _ _)
      | decide
      | (change guardB bop.BEQ p 0#64 = false; simpa [guardB] using h.nonzero)
      | (constructor; decide; exact read8_pins _ _)

theorem tablePublish_log (slot : MinorTableSlot) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (domain : bytesT m Layout.sym_Caml_state 8 = firstDomainPtr) :
    (evalBlocks slot.blocks (SegEvalState.init (tablePublishInput p) (tablePublishLoads slot p m))).log =
      tablePublishLog slot p := by
  cases slot <;> simp only [MinorTableSlot.blocks, caml_alloc_minor_tablesX982cFSeg,
    caml_alloc_minor_tablesX9854FSeg, caml_alloc_minor_tablesX987cFSeg, evalBlocks, evalBlock, SegEvalState.init]
  all_goals table_publish_nf
  all_goals rfl

theorem tablePublish_regs (slot : MinorTableSlot) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (domain : bytesT m Layout.sym_Caml_state 8 = firstDomainPtr) :
    (evalBlocks slot.blocks (SegEvalState.init (tablePublishInput p) (tablePublishLoads slot p m))).regs =
      tablePublishRegs p := by
  have loaded : bytesVal .ld (read8 (writeLog m (tablePublishLog slot p)) slot.address.toNat) = p := by
    rw [read8_value]
    exact word_writeLog _ _ _
  cases slot <;> simp only [MinorTableSlot.blocks, caml_alloc_minor_tablesX982cFSeg,
    caml_alloc_minor_tablesX9854FSeg, caml_alloc_minor_tablesX987cFSeg, evalBlocks, evalBlock, SegEvalState.init]
  all_goals table_publish_nf
  all_goals simp only [tablePublishLoads, List.headD_cons, List.tail_cons, loaded, read8_value, domain]
  all_goals rfl

theorem tablePublish_image (slot : MinorTableSlot) (p : BitVec 64) : ImageOutside (tablePublishLog slot p) := by
  cases slot <;> constructor <;> change OutLRange _ _ _ <;>
    simp only [tablePublishLog, OutLRange] <;> decide

/-- Publish a successful allocation into any of the three source table fields
and reload it through the actual domain global. -/
theorem table_publish (c : Config) (slot : MinorTableSlot) (p ra : BitVec 64)
    (h : TablePublishInput p ra c) :
    FnSummary slot.entry (fun d => d = c)
      (WriteRegistersPost [15, 10] (tablePublishLog slot p) c slot.exit p (tablePublishRegs p)) := by
  apply registers_of_blocks h.image (tablePublish_image slot p)
    (block_summary _ _ _ _ _ (tablePublish_input slot h))
  · exact tablePublish_log _ _ _ h.domainWord
  · cases slot <;> rfl
  · exact tablePublish_regs _ _ _ h.domainWord
  · rfl
  · cases slot <;> decide
end OCaml.Vm.Boot.Startup
