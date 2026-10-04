import OCaml.Vm.Boot.Startup.DomainReturnNormalized
import OCaml.Vm.Boot.Startup.DomainCaller
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def domainReturnInput (p : BitVec 64) : GRegs := [(2, firstMallocStack), (10, p)]
def domainReturnLoads (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem domainCallerSlot]
def domainReturnRegs (p : BitVec 64) : GRegs :=
  [(2, firstMallocStack + 16#64), (1, jal_80004d94_call.link), (10, p)]

local macro "domain_return_nf" : tactic =>
  `(tactic| simp only [domainreturn_line_8002a9d0, domainreturn_line_8002a9d4,
    MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    domainReturnInput, domainReturnLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

structure DomainReturnInput (p ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  stack : gprGet c.σ 2 = some firstMallocStack
  pointer : gprGet c.σ 10 = some p
  caller : bytesT c.σ.mem domainCallerSlot 8 = jal_80004d94_call.link

theorem domainReturn_input {p ra c} (h : DomainReturnInput p ra c) :
    BlockInput caml_init_domainXa9d0Seg 0x8002a9d0#64 (domainReturnInput p) (domainReturnLoads c) c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.stack, h.pointer, trivial⟩
  keys := by change KeysOK [2, 10]; decide
  shape := by change ChainOK _ [2, 10] _; decide
  tick := h.tick
  facts := by
    have code := domainInit_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_init_domain_at_"
    all_goals domain_return_nf
    · constructor
      · decide
      · exact read8_pins _ _
    · rw [read8_value, h.caller]
      decide

/-- Restore the domain initializer's caller link from its saved stack word. -/
theorem domain_return (c : Config) (p ra : BitVec 64) (h : DomainReturnInput p ra c) :
    FnSummary 0x8002a9d0#64 (fun d => d = c)
      (WriteRegistersPost [1, 2] [] c jal_80004d94_call.link p (domainReturnRegs p)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (domainReturn_input h))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem domainCallerSlot) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, h.caller]
    rfl
  · simp only [caml_init_domainXa9d0Seg, evalBlocks, evalBlock, SegEvalState.init]
    domain_return_nf
    rw [read8_value, h.caller]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
