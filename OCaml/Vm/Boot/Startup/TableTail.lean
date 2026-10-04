import OCaml.Vm.Boot.Startup.MinorTableTailNormalized
import OCaml.Vm.Boot.Startup.TableSaved
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def tableTailInput (p : BitVec 64) : GRegs := [(2, firstMallocStack - 32#64), (10, p)]
def tableTailLoads (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (firstMallocStack.toNat - 16), read8 c.σ.mem (firstMallocStack.toNat - 8),
   read8 c.σ.mem (firstMallocStack.toNat - 24)]
def tableTailRegs (p s0 s1 : BitVec 64) : GRegs :=
  [(2, firstMallocStack), (11, 0#64), (12, 56#64), (9, s1), (1, jal_8002a934_call.link), (8, s0), (10, p)]

local macro "table_tail_nf" : tactic =>
  `(tactic| simp only [minortabletail_line_8000988c, minortabletail_line_80009890,
    minortabletail_line_80009894, minortabletail_line_80009898, minortabletail_line_8000989c,
    minortabletail_line_800098a0, MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, tableTailInput, tableTailLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem tableTail_input {c p ra} (h : LeafInput ra c)
    (stack : gprGet c.σ 2 = some (firstMallocStack - 32#64)) (pointer : gprGet c.σ 10 = some p) :
    BlockInput caml_alloc_minor_tablesX988cSeg 0x8000988c#64 (tableTailInput p) (tableTailLoads c) c where
  good := h.good
  minstret := h.minstret
  regs := ⟨stack, pointer, trivial⟩
  keys := by change KeysOK [2, 10]; decide
  shape := by change ChainOK _ [2, 10] _; decide
  tick := h.tick
  facts := by
    have code := minorTables_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_alloc_minor_tables_at_"
    all_goals table_tail_nf
    all_goals first
      | decide
      | (constructor; decide; exact read8_pins _ _)

theorem tableTail_regs {c p s0 s1} (saved : TableSaved s0 s1 c) :
    (evalBlocks caml_alloc_minor_tablesX988cSeg (SegEvalState.init (tableTailInput p) (tableTailLoads c))).regs =
      tableTailRegs p s0 s1 := by
  simp only [caml_alloc_minor_tablesX988cSeg, evalBlocks, evalBlock, SegEvalState.init]
  table_tail_nf
  rw [read8_value, read8_value, read8_value, saved.saved0, saved.saved1, saved.returnAddress]
  rfl

/-- Restore the actual saved caller frame and tail-jump to memset with the
third table pointer. The return link comes from the certified stack word. -/
theorem table_tail_restore (c : Config) (p s0 s1 ra : BitVec 64) (h : LeafInput ra c)
    (stack : gprGet c.σ 2 = some (firstMallocStack - 32#64)) (pointer : gprGet c.σ 10 = some p)
    (saved : TableSaved s0 s1 c) :
    FnSummary 0x8000988c#64 (fun d => d = c)
      (WriteRegistersPost [8, 1, 9, 12, 11, 2] [] c 0x8004276c#64 p (tableTailRegs p s0 s1)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (tableTail_input h stack pointer))
  · rfl
  · rfl
  · exact tableTail_regs saved
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
