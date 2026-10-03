import OCaml.Vm.Boot.Startup.DomainInitNormalized
import OCaml.Vm.Boot.Startup.DomainInitCallInterface
import OCaml.Vm.Boot.Startup.MallocReturn
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
import OCaml.Vm.Gc.Readback
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives

def firstDomainPtr : BitVec 64 := BitVec.ofNat 64 (heapStart + 16)

def domainInitBlocks : List BBlock := caml_init_domainXa8ecFSeg ++ caml_init_domainXa8fcSeg

def domainInitInput : GRegs := [(10, firstDomainPtr)]

/-- The source publishes Caml_state, then clears its first field before reloading it. -/
def domainPublishLog : List WEntry :=
  [(Layout.sym_Caml_state, 8, firstDomainPtr), (firstDomainPtr.toNat, 8, 0#64)]

def domainInitLoads (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 (writeLog m domainPublishLog) Layout.sym_Caml_state]

/-- A later disjoint store preserves a just-published word. -/
theorem published_word (m : Std.ExtHashMap Nat (BitVec 8)) (a b : Nat) (v : BitVec 64)
    (outside : a + 8 ≤ b ∨ b + 8 ≤ a) :
    bytesT (writeLog m [(a, 8, v), (b, 8, 0#64)]) a 8 = v := by
  have log : [(a, 8, v), (b, 8, 0#64)] = [(a, 8, v)] ++ [(b, 8, 0#64)] := rfl
  rw [log, writeLog_append]
  rw [bytesT_writeLog_out (log := [(b, 8, 0#64)]) (a := a) (n := 8) _ ⟨outside, trivial⟩]
  exact word_writeLog _ _ _

theorem domainInit_loaded (m : Std.ExtHashMap Nat (BitVec 8)) :
    bytesVal .ld ((domainInitLoads m).headD []) = firstDomainPtr := by
  simp only [domainInitLoads, List.headD_cons, read8_value, domainPublishLog]
  exact published_word _ _ _ _ (by decide)


local macro "domain_init_nf" : tactic =>
  `(tactic| simp only [domaininit_line_8002a8ec, domaininit_line_8002a8f0, domaininit_line_8002a8f4, domaininit_line_8002a8fc, domaininit_line_8002a900, domaininit_line_8002a904, domaininit_line_8002a908, domaininit_line_8002a90c, domaininit_line_8002a910, domaininit_line_8002a914, domaininit_line_8002a918, domaininit_line_8002a91c, domaininit_line_8002a920, domaininit_line_8002a924, domaininit_line_8002a928, domaininit_line_8002a92c, domaininit_line_8002a930, MemFacts,
      runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
      domainInitInput, wvalM, wentryM, widthOfM, imm20Of,
      List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem domainInit_input {c : Config} (h : LeafInput jal_8002a8e8_call.link c)
    (pointer : gprGet c.σ 10 = some firstDomainPtr) :
    BlockInput domainInitBlocks jal_8002a8e8_call.link domainInitInput (domainInitLoads c.σ.mem) c where
  good := h.good
  minstret := h.minstret
  regs := ⟨pointer, trivial⟩
  keys := by decide
  shape := by decide
  tick := h.tick
  facts := by
    have code := domainInit_code h.image
    have value := domainInit_loaded c.σ.mem
    chain_facts code with "Vsa.Sim.Code.caml_init_domain_at_"
    all_goals domain_init_nf
    all_goals try simp only [value]
    all_goals try decide
    constructor
    · decide
    · change LPins8 (writeLog c.σ.mem domainPublishLog) Layout.sym_Caml_state
        (read8 (writeLog c.σ.mem domainPublishLog) Layout.sym_Caml_state)
      exact read8_pins _ _

/-- A bounded synthetic load list records only the just-stored pointer; its
value certificate is used to normalize the source-generated write log. -/
def domainPtrBytes : List (BitVec 8) :=
  List.ofFn (fun i : Fin 8 => firstDomainPtr.extractLsb' (8 * i.val) 8)

theorem domainPtrBytes_value : bytesVal .ld domainPtrBytes = firstDomainPtr := by decide

def domainInitLog : List WEntry :=
  (evalBlocks domainInitBlocks (SegEvalState.init domainInitInput [domainPtrBytes])).log

def domainInitRegs : GRegs :=
  [(15, firstDomainPtr), (14, BitVec.ofNat 64 Layout.sym_Caml_state), (10, firstDomainPtr)]

theorem domainInit_log (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks domainInitBlocks (SegEvalState.init domainInitInput (domainInitLoads m))).log =
      domainInitLog := by
  simp only [domainInitLog, domainInitBlocks, caml_init_domainXa8ecFSeg,
    caml_init_domainXa8fcSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
  domain_init_nf
  rw [domainInit_loaded, domainPtrBytes_value]

theorem domainInit_regs (m : Std.ExtHashMap Nat (BitVec 8)) :
    (evalBlocks domainInitBlocks (SegEvalState.init domainInitInput (domainInitLoads m))).regs =
      domainInitRegs := by
  simp only [domainInitBlocks, caml_init_domainXa8ecFSeg,
    caml_init_domainXa8fcSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
  domain_init_nf
  rw [domainInit_loaded]
  rfl

theorem domainInit_image_outside : ImageOutside domainInitLog := by
  constructor <;> change OutLRange _ _ _ <;>
    simp only [domainInitLog, domainInitBlocks, caml_init_domainXa8ecFSeg,
      caml_init_domainXa8fcSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
  all_goals domain_init_nf
  all_goals rw [domainPtrBytes_value]
  all_goals simp only [List.cons_append, List.nil_append, OutLRange]
  all_goals decide

/-- All initialization stores are confined to the domain publication word
and the allocated payload. This footprint protects allocator metadata. -/
def domainInitWindows : List W :=
  [⟨Layout.sym_Caml_state, Layout.sym_Caml_state + 8⟩,
   ⟨firstDomainPtr.toNat, firstDomainPtr.toNat + 928⟩]

theorem domainInit_log_inside : LogInW domainInitWindows domainInitLog := by
  simp only [domainInitLog, domainInitBlocks, caml_init_domainXa8ecFSeg,
    caml_init_domainXa8fcSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
  domain_init_nf
  rw [domainPtrBytes_value]
  simp only [List.cons_append, List.nil_append, LogInW, InsideW, domainInitWindows]
  repeat' apply And.intro
  all_goals decide

/-- Read back the published domain pointer after all payload stores. -/
theorem domainInit_domain_word (m : Std.ExtHashMap Nat (BitVec 8)) :
    bytesT (writeLog m domainInitLog) Layout.sym_Caml_state 8 = firstDomainPtr := by
  apply OCaml.Vm.Gc.word_writeLog_at (i := 0)
  · rfl
  · simp only [domainInitLog, domainInitBlocks, caml_init_domainXa8ecFSeg,
      caml_init_domainXa8fcSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
    domain_init_nf
    rw [domainPtrBytes_value]
    simp only [List.cons_append, List.nil_append, List.drop, OutLRange]
    repeat' apply And.intro
    all_goals decide

/-- Publish the first domain and clear its minor-heap fields, reaching the
minor-table allocation call with an exact source-derived write log. -/
theorem domain_initialize (c : Config) (h : LeafInput jal_8002a8e8_call.link c)
    (pointer : gprGet c.σ 10 = some firstDomainPtr) :
    FnSummary jal_8002a8e8_call.link (fun d => d = c)
      (WriteRegistersPost [14, 15] domainInitLog c jal_8002a934_call.pc firstDomainPtr domainInitRegs) := by
  apply registers_of_blocks h.image domainInit_image_outside
    (block_summary _ _ _ _ _ (domainInit_input h pointer))
  · exact domainInit_log _
  · rfl
  · exact domainInit_regs _
  · rfl
  · decide

/-- The generated call enters minor-table allocation with the initialized
first domain and its original caller stack. -/
theorem domain_init_tables (c : Config) (h : LeafInput jal_8002a8e8_call.link c)
    (pointer : gprGet c.σ 10 = some firstDomainPtr) :
    FnSummary jal_8002a8e8_call.link (fun d => d = c)
      (WriteRegistersPost [14, 15, 1] domainInitLog c jal_8002a934_call.target firstDomainPtr
        ((1, jal_8002a934_call.link) :: domainInitRegs)) := by
  apply summary_bind (domain_initialize c h pointer) (fun _ post => post.pc)
  intro mid post
  have call := call_registers_summary jal_8002a934_call_shape jal_8002a934_call_decode mid
    (jal_8002a934_call_pins post.image) post.good post.image post.tick post.minstret _ post.regs
    (by change KeysOK [15, 14, 10]; decide) (by simp [KeysAvoidRa, keysG, domainInitRegs]) (by rfl)
  apply call.weaken (fun _ eq => eq)
  intro after called
  exact prefix_call_post post called
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

/-- The reset execution has initialized the first domain's minor-heap fields
and reached the next runtime allocator. -/
structure ResetMinorTables (initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config) : Prop where
  allocation : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc afterMalloc
  run : Steps (Vsa.Densify.fillZero initial) atTables
  post : WriteRegistersPost [14, 15, 1] domainInitLog afterMalloc jal_8002a934_call.target firstDomainPtr
    ((1, jal_8002a934_call.link) :: domainInitRegs) atTables

theorem reset_minor_tables_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables,
    ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, w⟩ := reset_first_allocation_exists
  obtain ⟨atTables, run, post⟩ := (domain_init_tables afterMalloc w.leaf w.pointer).run afterMalloc ⟨w.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, w, w.run.trans run, post⟩
end OCaml.Vm.Boot.WhileMinElfParse

