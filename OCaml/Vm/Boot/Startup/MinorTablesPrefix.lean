import OCaml.Vm.Boot.Startup.MinorTablesNormalized
import OCaml.Vm.Boot.Startup.MinorTablesCallInterface
import OCaml.Vm.Boot.Startup.DomainHeap
import Vsa.Sim.ChainFactsTac
import OCaml.Vm.Primitives.AccessPlan
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def minorTablesInput (s0 s1 : BitVec 64) : GRegs :=
  caml_alloc_minor_tablesX9808L firstMallocStack s0 jal_8002a934_call.link s1

def minorTablesLog (s0 s1 : BitVec 64) : List WEntry :=
  [(firstMallocStack.toNat - 16, 8, s0),
   (firstMallocStack.toNat - 8, 8, jal_8002a934_call.link),
   (firstMallocStack.toNat - 24, 8, s1)]

def minorTablesLoads (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem Layout.sym_Caml_state]

def minorTablesRegs : GRegs :=
  [(9, firstDomainPtr), (10, 56#64), (8, BitVec.ofNat 64 Layout.sym_Caml_state),
   (2, firstMallocStack - 32#64), (1, jal_8002a934_call.link)]

local macro "minor_tables_nf" : tactic =>
  `(tactic| simp only [minorTablesInput, caml_alloc_minor_tablesX9808L,
    minortables_line_80009808, minortables_line_8000980c, minortables_line_80009810,
    minortables_line_80009814, minortables_line_80009818, minortables_line_8000981c,
    minortables_line_80009820, minortables_line_80009824,
    MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    wvalM, wentryM, widthOfM, imm20Of, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

structure MinorTablesInput (s0 s1 : BitVec 64) (c : Config) : Prop extends LeafInput jal_8002a934_call.link c where
  stack : gprGet c.σ 2 = some firstMallocStack
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr

/-- All stores in the table allocator's 32-byte prologue share one address rule. -/
theorem minorTables_stack_address (off : Nat) (bound : off ≤ 32) :
    (firstMallocStack + Functions.sign_extend (m := 64) 0xfe0#12 + BitVec.ofNat 64 off).toNat =
      firstMallocStack.toNat - 32 + off := by
  change (BitVec.ofNat 64 (Layout.sym_stack_top - 176) + BitVec.ofNat 64 off).toNat =
    Layout.sym_stack_top - 176 + off
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Layout.sym_stack_top, Nat.reduceSub]
  rw [Nat.mod_eq_of_lt (by omega : off < 18446744073709551616), Nat.mod_eq_of_lt (by omega)]

def minorTablesBody : List MInstr := (minorTablesSave.headD ⟨[], none⟩).body

theorem minorTables_code_facts {c : Config} (image : ExecutableImage c) :
    CodeFacts c.σ.mem minorTablesBody := by
  have code := minorTables_code image
  simp only [minorTablesBody, minorTablesSave, List.headD_cons, CodeFacts]
  chain_facts code with "Vsa.Sim.Code.caml_alloc_minor_tables_at_"

theorem minorTables_access (s0 s1 : BitVec 64) (c : Config) :
    AccessPlan c.σ.mem (minorTablesInput s0 s1) (minorTablesLoads c) minorTablesBody := by
  simp only [minorTablesBody, minorTablesSave, List.headD_cons, AccessPlan]
  chain_facts True.intro
  all_goals minor_tables_nf
  all_goals try decide
  constructor
  · decide
  · have a16 := minorTables_stack_address 16 (by decide)
    have a24 := minorTables_stack_address 24 (by decide)
    have a8 := minorTables_stack_address 8 (by decide)
    change (firstMallocStack + Functions.sign_extend (m := 64) 0xfe0#12 + Functions.sign_extend (m := 64) 0x010#12).toNat = firstMallocStack.toNat - 16 at a16
    change (firstMallocStack + Functions.sign_extend (m := 64) 0xfe0#12 + Functions.sign_extend (m := 64) 0x018#12).toNat = firstMallocStack.toNat - 8 at a24
    change (firstMallocStack + Functions.sign_extend (m := 64) 0xfe0#12 + Functions.sign_extend (m := 64) 0x008#12).toNat = firstMallocStack.toNat - 24 at a8
    rw [a16, a24, a8]
    have global : (0x80009818#64 + Functions.sign_extend (BitVec.extractLsb' 12 20 0x0005b417#32 +++ 0#12) +
        Functions.sign_extend (m := 64) 0x4f0#12 + Functions.sign_extend (m := 64) 0#12).toNat = Layout.sym_Caml_state := by decide
    rw [global]
    have pins := lpins8_writeLog (read8_pins c.σ.mem Layout.sym_Caml_state)
      (show OutLRange (minorTablesLog s0 s1) Layout.sym_Caml_state 8 from by
        simp only [minorTablesLog, OutLRange]; decide)
    simpa only [minorTablesLoads, List.headD_cons, minorTablesLog, writeLog, List.foldl_cons, List.foldl_nil] using pins

theorem minorTables_input {s0 s1 : BitVec 64} {c : Config} (h : MinorTablesInput s0 s1 c) :
    BlockInput caml_alloc_minor_tablesX9808Seg jal_8002a934_call.target
      (minorTablesInput s0 s1) (minorTablesLoads c) c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.stack, h.saved0, h.raReg, h.saved1, trivial⟩
  keys := by change KeysOK [2, 8, 1, 9]; decide
  shape := by change ChainOK _ [2, 8, 1, 9] _; decide
  tick := h.tick
  facts := by
    rw [← minorTablesSave_eq]
    apply singleton_chain_facts
      (accessPlan_facts (minorTables_code_facts h.image) (minorTables_access s0 s1 c))
    · trivial
    · trivial

theorem minorTables_log (s0 s1 : BitVec 64) (loads : List (List (BitVec 8))) :
    (evalBlocks caml_alloc_minor_tablesX9808Seg
      (SegEvalState.init (minorTablesInput s0 s1) loads)).log = minorTablesLog s0 s1 := by
  rw [← minorTablesSave_eq]
  simp only [minorTablesSave, evalBlocks, evalBlock, SegEvalState.init]
  minor_tables_nf
  rfl

theorem minorTables_regs {s0 s1 : BitVec 64} {c : Config}
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    (evalBlocks caml_alloc_minor_tablesX9808Seg
      (SegEvalState.init (minorTablesInput s0 s1) (minorTablesLoads c))).regs = minorTablesRegs := by
  rw [← minorTablesSave_eq]
  simp only [minorTablesSave, evalBlocks, evalBlock, SegEvalState.init]
  minor_tables_nf
  simp only [minorTablesLoads, List.headD_cons, read8_value, domain]
  rfl

theorem minorTables_image_outside (s0 s1 : BitVec 64) : ImageOutside (minorTablesLog s0 s1) := by
  constructor <;> simp only [minorTablesLog, OutLRange] <;> decide

/-- The table allocator saves its ABI frame and prepares its first 56-byte request. -/
theorem minorTables_prefix (s0 s1 : BitVec 64) (c : Config) (h : MinorTablesInput s0 s1 c) :
    FnSummary jal_8002a934_call.target (fun d => d = c)
      (WriteRegistersPost [2, 8, 10, 9] (minorTablesLog s0 s1) c jal_80009828_call.pc 56#64 minorTablesRegs) := by
  apply registers_of_blocks h.image (minorTables_image_outside s0 s1)
    (block_summary _ _ _ _ _ (minorTables_input h))
  · exact minorTables_log _ _ _
  · rfl
  · exact minorTables_regs h.domain
  · rfl
  · decide

def minorTablesCallRegs : GRegs := minorTablesRegs.take 4

theorem minorTables_allocate (s0 s1 : BitVec 64) (c : Config) (h : MinorTablesInput s0 s1 c) :
    FnSummary jal_8002a934_call.target (fun d => d = c)
      (WriteRegistersPost [2, 8, 10, 9, 1] (minorTablesLog s0 s1) c jal_80009828_call.target 56#64
        ((1, jal_80009828_call.link) :: minorTablesCallRegs)) := by
  apply summary_bind (minorTables_prefix s0 s1 c h) (fun _ post => post.pc)
  intro mid post
  have regs : GHolds mid.σ minorTablesCallRegs :=
    holds_project post.regs (by simp [minorTablesCallRegs, minorTablesRegs, lookupG])
  have call := call_registers_summary jal_80009828_call_shape jal_80009828_call_decode mid
    (jal_80009828_call_pins post.image) post.good post.image post.tick post.minstret _ regs
    (by change KeysOK [9, 10, 8, 2]; decide)
    (by simp [KeysAvoidRa, keysG, minorTablesCallRegs, minorTablesRegs]) (by rfl)
  apply call.weaken (fun _ eq => eq)
  intro after called
  exact prefix_call_post post called
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

theorem ResetMinorTables.prefixInput {initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config}
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    MinorTablesInput ((gprGet atTables.σ 8).getD 0) ((gprGet atTables.σ 9).getD 0) atTables where
  toLeafInput := ⟨w.post.good, w.post.image, w.post.minstret,
    gholds_lookup _ w.post.regs (by rfl), by decide, w.post.tick⟩
  stack := (w.post.frame .x2 (by decide) (by decide)).trans w.allocation.stack
  saved0 := library_gpr w.vsaOk (by decide) (by decide) (by rfl)
  saved1 := library_gpr w.vsaOk (by decide) (by decide) (by rfl)
  domain := by rw [w.post.memory]; exact domainInit_domain_word _

/-- Reset now reaches the first minor-table stat-allocation request. -/
structure ResetTableAlloc (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config) : Prop where
  tables : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables
  run : Steps (Vsa.Densify.fillZero initial) atRequest
  post : WriteRegistersPost [2, 8, 10, 9, 1]
    (minorTablesLog ((gprGet atTables.σ 8).getD 0) ((gprGet atTables.σ 9).getD 0)) atTables
    jal_80009828_call.target 56#64 ((1, jal_80009828_call.link) :: minorTablesCallRegs) atRequest

theorem reset_table_alloc_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest,
    ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, w⟩ := reset_minor_tables_exists
  obtain ⟨atRequest, run, post⟩ := (minorTables_allocate _ _ atTables w.prefixInput).run atTables ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, w, w.run.trans run, post⟩
end OCaml.Vm.Boot.WhileMinElfParse

