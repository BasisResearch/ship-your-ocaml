import OCaml.Vm.Boot.Startup.FindNameNormalized
import OCaml.Vm.Boot.Startup.FindNameImage
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def nameStepBlocks (finished : Bool) : List BBlock :=
  if finished then findenv_rX7490TSeg else findenv_rX7490FSeg ++ findenv_rX74a4TSeg

def nameStepInput (cursor value : BitVec 64) : GRegs := [(12, cursor), (10, value)]
def nameStepRegs (cursor value : BitVec 64) (b : BitVec 8) : GRegs :=
  [(15, nameSignedByte b + (-61#64)), (12, cursor + 1#64), (14, nameByteWord b), (10, value)]

structure NameStepInput (cursor value ra : BitVec 64) (b : BitVec 8) (finished : Bool) (c : Config) : Prop extends LeafInput ra c where
  cursorReg : gprGet c.σ 12 = some cursor
  valueReg : gprGet c.σ 10 = some value
  window : ReadWindow (cursor + 1#64) 1
  pin : (c.σ.mem[(cursor + 1#64).toNat]?).getD 0 = b
  zero : b = 0#8 ↔ finished = true
  notEquals : b ≠ 61#8

local macro "name_step_nf" : tactic =>
  `(tactic| simp only [findname_line_80037490, findname_line_80037494, findname_line_80037498, findname_line_8003749c,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    nameStepInput, wvalM, wentryM, widthOfM, name_lbu_value,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem nameStep_input {cursor value ra b finished c} (h : NameStepInput cursor value ra b finished c) :
    BlockInput (nameStepBlocks finished) 0x80037490#64 (nameStepInput cursor value) [[b]] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.cursorReg, h.valueReg, trivial⟩
  keys := by change KeysOK [12, 10]; decide
  shape := by change ChainOK _ [12, 10] _; cases finished <;> decide
  tick := h.tick
  facts := by
    have code := findName_code h.image
    cases finished with
    | false =>
      chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
      · exact h.window.lbu rfl rfl h.pin
      · name_step_nf
        exact nameByte_zero_guard h.zero
      · name_step_nf
        exact nameByte_equals_guard h.notEquals
    | true =>
      chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
      · exact h.window.lbu rfl rfl h.pin
      · name_step_nf
        exact nameByte_zero_guard h.zero

theorem nameStep_regs (cursor value : BitVec 64) (b : BitVec 8) (finished : Bool) :
    (evalBlocks (nameStepBlocks finished) (SegEvalState.init (nameStepInput cursor value) [[b]])).regs =
      nameStepRegs cursor value b := by
  cases finished <;> simp only [nameStepBlocks, Bool.false_eq_true, ite_false, ite_true,
    findenv_rX7490TSeg, findenv_rX7490FSeg, findenv_rX74a4TSeg, List.cons_append, List.nil_append,
    evalBlocks, evalBlock, SegEvalState.init]
  all_goals name_step_nf
  all_goals rfl

/-- One native environment-name scan iteration, including its zero/equal tests. -/
theorem name_step (c : Config) (cursor value ra : BitVec 64) (b : BitVec 8) (finished : Bool)
    (h : NameStepInput cursor value ra b finished c) :
    FnSummary 0x80037490#64 (fun d => d = c)
      (WriteRegistersPost [14, 12, 15] [] c (if finished then 0x800374a8#64 else 0x80037490#64)
        value (nameStepRegs cursor value b)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (nameStep_input h))
  · cases finished <;> rfl
  · cases finished <;> rfl
  · exact nameStep_regs cursor value b finished
  · rfl
  · cases finished <;> decide
end OCaml.Vm.Boot.Startup
