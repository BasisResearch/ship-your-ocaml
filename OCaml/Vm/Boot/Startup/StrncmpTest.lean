import OCaml.Vm.Boot.Startup.StrncmpTestNormalized
import OCaml.Vm.Boot.Startup.StrncmpTestImage
import OCaml.Vm.Boot.Startup.StrncmpNext
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def strncmpTestBlocks (finished : Bool) : List BBlock :=
  if finished then strncmpX0d68FSeg else strncmpX0d68TSeg

def strncmpTestInput (p q stop : BitVec 64) (b : BitVec 8) : GRegs :=
  [(10, p), (11, q), (12, stop), (15, nameByteWord b), (14, nameByteWord b)]
def strncmpTestRegs (p q stop : BitVec 64) (b : BitVec 8) : GRegs :=
  [(11, q + 1#64), (10, p), (12, stop), (15, nameByteWord b), (14, nameByteWord b)]

theorem strncmpTest_input {p q stop ra b finished c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpTestInput p q stop b)) (last : p = stop ↔ finished = true) :
    BlockInput (strncmpTestBlocks finished) 0x80040d68#64 (strncmpTestInput p q stop b) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 11, 12, 15, 14]; decide
  shape := by change ChainOK _ [10, 11, 12, 15, 14] _; cases finished <;> decide
  tick := leaf.tick
  facts := by
    have code := strncmpTest_code leaf.image
    cases finished with
    | false =>
      chain_facts code with "Vsa.Sim.Code.strncmp_at_"
      exact bne_iff_ne.mpr (fun eq => Bool.noConfusion (last.mp eq))
    | true =>
      chain_facts code with "Vsa.Sim.Code.strncmp_at_"
      exact (Bool.eq_false_iff).mpr (fun yes => (bne_iff_ne.mp yes) (last.mpr rfl))

/-- Advance the right cursor and test whether the bounded prefix is exhausted. -/
theorem strncmp_test (c : Config) (p q stop ra : BitVec 64) (b : BitVec 8) (finished : Bool)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (strncmpTestInput p q stop b))
    (last : p = stop ↔ finished = true) :
    FnSummary 0x80040d68#64 (fun d => d = c)
      (WriteRegistersPost [11] [] c (if finished then 0x80040d70#64 else 0x80040d54#64) p
        (strncmpTestRegs p q stop b)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (strncmpTest_input leaf regs last))
  · cases finished <;> rfl
  · cases finished <;> rfl
  · cases finished <;> rfl
  · rfl
  · cases finished <;> decide
end OCaml.Vm.Boot.Startup
