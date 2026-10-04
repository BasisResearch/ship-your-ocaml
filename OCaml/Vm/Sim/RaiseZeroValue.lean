import OCaml.Vm.Sim.RaiseZeroDivideRows
import OCaml.Vm.Sim.RaiseZeroDivideImage
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Read
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

def raiseZeroField (global : BitVec 64) : BitVec 64 := global + BitVec.ofNat 64 Layout.raiseZeroExceptionOffset

/-- Scalar readiness for the predefined Division_by_zero exception load. -/
structure RaiseZeroValueInput (global value : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  globalWord : word c Layout.sym_caml_global_data = global
  fieldRead : ReadWindow (raiseZeroField global) 8
  fieldWord : word c (raiseZeroField global).toNat = value

def raiseZeroLoads (c : Config) (global : BitVec 64) : List (List (BitVec 8)) :=
  [read8 c.σ.mem Layout.sym_caml_global_data, read8 c.σ.mem (raiseZeroField global).toNat]

theorem raise_zero_value_input {global value : BitVec 64} {c : Config} (h : RaiseZeroValueInput global value c) :
    BlockInput caml_raise_zero_divideXd1e8Seg 0x8000d1e8#64 [] (raiseZeroLoads c global) c := by
  have load : bytesVal .ld (read8 c.σ.mem Layout.sym_caml_global_data) = global := by
    rw [read8_value]; exact h.globalWord
  refine ⟨h.good, h.good.minstret, trivial, ?_, ?_, ?_, h.tick⟩
  · change KeysOK []; decide
  · have code := caml_raise_zero_divide_loaded h.image
    chain_facts code with "Vsa.Sim.Code.caml_raise_zero_divide_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_caml_global_data)
        (by constructor <;> decide) rfl
        (by change (0x8000d1e8#64 + sign_extend (m := 64) ((0x00057#20) +++ 0#12)) + sign_extend (m := 64) (0x600#12) = BitVec.ofNat 64 Layout.sym_caml_global_data; decide)
      change LPins8 c.σ.mem Layout.sym_caml_global_data (read8 c.σ.mem Layout.sym_caml_global_data)
      exact read8_pins _ _
    · apply h.fieldRead.ld rfl
        (by change bytesVal .ld (read8 c.σ.mem Layout.sym_caml_global_data) + sign_extend (m := 64) (0x028#12) = raiseZeroField global; rw [load]; rfl)
      change LPins8 c.σ.mem (raiseZeroField global).toNat (read8 c.σ.mem (raiseZeroField global).toNat)
      exact read8_pins _ _
  · change ChainOK 0x8000d1e8#64 [] caml_raise_zero_divideXd1e8Seg; decide

/-- The generated three-instruction suffix selects the predefined exception value. -/
theorem raise_zero_value {global value : BitVec 64} {c : Config} (h : RaiseZeroValueInput global value c) :
    FnSummary 0x8000d1e8#64 (fun start => start = c)
      (WriteRegistersPost [10, 15] [] c 0x8000d1f4#64 value [(10, value), (15, global)]) := by
  apply registers_of_blocks (log := []) h.image ⟨trivial, trivial⟩ (block_summary _ _ _ _ _ (raise_zero_value_input h))
  · rfl
  · rfl
  · change [(10, bytesVal .ld (read8 c.σ.mem (raiseZeroField global).toNat)),
      (15, bytesVal .ld (read8 c.σ.mem Layout.sym_caml_global_data))] = _
    rw [read8_value, read8_value]
    change [(10, word c (raiseZeroField global).toNat), (15, word c Layout.sym_caml_global_data)] = _
    rw [h.fieldWord, h.globalWord]
  · rfl
  · decide

end OCaml.Vm.Sim
