import OCaml.Vm.Boot.Startup.DomainFieldsNormalized
import OCaml.Vm.Boot.Startup.DomainCaller
import OCaml.Vm.Primitives.AccessPlan
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def domainFieldsInput (p : BitVec 64) : GRegs := [(10, p)]
def domainFieldsLoads (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem Layout.sym_Caml_state]
def domainFieldsBody : List MInstr := (domainFieldsSave.headD ⟨[], none⟩).body

def domainFieldsLog : List WEntry :=
  (evalBlocks domainFieldsSave (SegEvalState.init (domainFieldsInput 0#64) [domainPtrBytes])).log

def domainFieldsRegs (p : BitVec 64) : GRegs := [(14, 1#64), (15, firstDomainPtr), (10, p)]

local macro "domain_fields_nf" : tactic =>
  `(tactic| simp only [MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, domainFieldsInput, domainFieldsLoads,
    wvalM, wentryM, widthOfM, imm20Of,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

structure DomainFieldsInput (p ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  pointer : gprGet c.σ 10 = some p
  domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr

theorem domainFields_code_facts {c : Config} (image : ExecutableImage c) :
    CodeFacts c.σ.mem domainFieldsBody := by
  have code := domainInit_code image
  simp only [domainFieldsBody, domainFieldsSave, List.headD_cons, CodeFacts]
  chain_facts code with "Vsa.Sim.Code.caml_init_domain_at_"

theorem domainFields_access {p ra c} (h : DomainFieldsInput p ra c) :
    AccessPlan c.σ.mem (domainFieldsInput p) (domainFieldsLoads c) domainFieldsBody := by
  simp only [domainFieldsBody, domainFieldsSave, List.headD_cons, AccessPlan]
  chain_facts True.intro
  all_goals domain_fields_nf
  all_goals try rw [read8_value, h.domain]
  all_goals first | decide | (constructor; decide; exact read8_pins _ _)

theorem domainFields_input {p ra c} (h : DomainFieldsInput p ra c) :
    BlockInput caml_init_domainXa938Seg 0x8002a938#64 (domainFieldsInput p) (domainFieldsLoads c) c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.pointer, trivial⟩
  keys := by change KeysOK [10]; decide
  shape := by change ChainOK _ [10] _; decide
  tick := h.tick
  facts := by
    rw [← domainFieldsSave_eq]
    exact singleton_chain_facts (accessPlan_facts (domainFields_code_facts h.image) (domainFields_access h)) trivial trivial

theorem domainFields_log {p ra c} (h : DomainFieldsInput p ra c) :
    (evalBlocks caml_init_domainXa938Seg (SegEvalState.init (domainFieldsInput p) (domainFieldsLoads c))).log = domainFieldsLog := by
  rw [← domainFieldsSave_eq]
  simp only [domainFieldsLog, domainFieldsSave, evalBlocks, evalBlock, SegEvalState.init]
  domain_fields_nf
  rw [read8_value, h.domain, domainPtrBytes_value]

theorem domainFields_regs {p ra c} (h : DomainFieldsInput p ra c) :
    (evalBlocks caml_init_domainXa938Seg (SegEvalState.init (domainFieldsInput p) (domainFieldsLoads c))).regs = domainFieldsRegs p := by
  rw [← domainFieldsSave_eq]
  simp only [domainFieldsSave, evalBlocks, evalBlock, SegEvalState.init]
  domain_fields_nf
  rw [read8_value, h.domain]
  rfl

theorem domainFields_image_outside : ImageOutside domainFieldsLog := by
  constructor <;> change OutLRange _ _ _
  all_goals simp only [domainFieldsLog, domainFieldsSave, evalBlocks, evalBlock, SegEvalState.init]
  all_goals domain_fields_nf
  all_goals rw [domainPtrBytes_value]
  all_goals simp only [List.nil_append, OutLRange]
  all_goals repeat' apply And.intro
  all_goals decide

def domainFieldsWindows : List W := [⟨firstDomainPtr.toNat, firstDomainPtr.toNat + 928⟩]

theorem domainFields_log_inside : LogInW domainFieldsWindows domainFieldsLog := by
  simp only [domainFieldsLog, domainFieldsSave, evalBlocks, evalBlock, SegEvalState.init]
  domain_fields_nf
  rw [domainPtrBytes_value]
  simp only [List.nil_append, LogInW, InsideW, domainFieldsWindows]
  repeat' apply And.intro
  all_goals decide

/-- The post-table domain initialization stores, compiled from domain.c. -/
theorem domain_fields (c : Config) (p ra : BitVec 64) (h : DomainFieldsInput p ra c) :
    FnSummary 0x8002a938#64 (fun d => d = c)
      (WriteRegistersPost [15, 14] domainFieldsLog c 0x8002a9d0#64 p (domainFieldsRegs p)) := by
  apply registers_of_blocks h.image domainFields_image_outside (block_summary _ _ _ _ _ (domainFields_input h))
  · exact domainFields_log h
  · rfl
  · exact domainFields_regs h
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
