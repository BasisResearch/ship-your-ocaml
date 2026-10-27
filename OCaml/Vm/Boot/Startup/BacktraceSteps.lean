import OCaml.Vm.Boot.Startup.InitBacktraceNormalized
import OCaml.Vm.Boot.Startup.InitBacktraceImage
import OCaml.Vm.Boot.Startup.RegisterGlobalRootNormalized
import OCaml.Vm.Boot.Startup.RegisterGlobalRootImage
import OCaml.Vm.Boot.Startup.CamlInitBacktraceCallInterface
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Gc.SkiplistFirst

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

local macro "backtrace_nf" : tactic => `(tactic| simp only [
  initbacktrace_line_8000ef3c, initbacktrace_line_8000ef40, initbacktrace_line_8000ef44,
  registerglobalroot_line_8000c9e0, registerglobalroot_line_8000c9e4,
  registerglobalroot_line_8000c9e8, registerglobalroot_line_8000c9ec,
  runGM, stepGM, eraseG, wvalM, srcVal, lookupG, eaddrM, imm20Of,
  ldsRunM, stepLdsM, List.headD_cons, List.tail_cons,
  Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff])

/-- The ELF's backtrace initializer computes the domain key and tail-calls
its actual global-root registration entry. It performs no domain stores. -/
theorem init_backtrace (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x8000ef3c#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c 0x8000c9e0#64 Gc.SkiplistFirst.startupKey
        [(10, Gc.SkiplistFirst.startupKey)]) := by
  have BI : BlockInput caml_init_backtraceXef3cSeg 0x8000ef3c#64 []
      [read8 c.σ.mem Layout.sym_Caml_state] c := {
    good := leaf.good
    minstret := leaf.minstret
    tick := leaf.tick
    regs := trivial
    keys := by change KeysOK []; decide
    shape := by change ChainOK _ [] _; decide
    facts := by
      have code := initBacktrace_code leaf.image
      chain_facts code with "Vsa.Sim.Code.caml_init_backtrace_at_"
      · backtrace_nf
        constructor
        · decide
        · exact read8_pins _ _ }
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ BI)
  · rfl
  · rfl
  · simp only [caml_init_backtraceXef3cSeg, evalBlocks, evalBlock, SegEvalState.init]
    backtrace_nf
    rw [read8_value, domain]
    rfl
  · rfl
  · decide

/-- The real root-registration wrapper tail-calls skiplist insertion with
`caml_global_roots`, the supplied key and zero data. -/
theorem register_global_root (c : Config) (ra key : BitVec 64) (leaf : LeafInput ra c)
    (reg : gprGet c.σ 10 = some key) :
    FnSummary 0x8000c9e0#64 (fun d => d = c)
      (WriteRegistersPost [10,11,12] [] c Gc.Skiplist.insertPc Gc.SkiplistFirst.sk
        [(10, Gc.SkiplistFirst.sk), (12, 0), (11, key)]) := by
  have BI : BlockInput caml_register_global_rootXc9e0Seg 0x8000c9e0#64 [(10,key)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    tick := leaf.tick
    regs := ⟨reg, trivial⟩
    keys := by change KeysOK [10]; decide
    shape := by change ChainOK _ [10] _; decide
    facts := by
      have code := registerGlobalRoot_code leaf.image
      chain_facts code with "Vsa.Sim.Code.caml_register_global_root_at_" }
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ BI)
  · rfl
  · rfl
  · simp only [caml_register_global_rootXc9e0Seg, evalBlocks, evalBlock, SegEvalState.init]
    backtrace_nf
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
    simp only [BitVec.add_zero]
    rfl
  · rfl
  · decide

end OCaml.Vm.Boot.Startup
