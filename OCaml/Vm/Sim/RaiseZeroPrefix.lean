import OCaml.Vm.Sim.RaiseZeroDivideRows
import OCaml.Vm.Sim.RaiseZeroDivideImage
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

def raiseZeroStack (sp : BitVec 64) : BitVec 64 := sp - BitVec.ofNat 64 Layout.raiseZeroFrameBytes

def raiseZeroRa (sp : BitVec 64) : BitVec 64 := raiseZeroStack sp + BitVec.ofNat 64 Layout.raiseZeroSaveRaOffset

def raiseZeroLog (sp ra : BitVec 64) : List WEntry := [((raiseZeroRa sp).toNat, 8, ra)]

/-- The zero-divisor helper installs its native frame before checking global data. -/
structure RaiseZeroPrefixMemory (sp ra : BitVec 64) : Prop where
  raWrite : WriteWindow (raiseZeroRa sp) 8
  imageOutside : ImageOutside (raiseZeroLog sp ra)

structure RaiseZeroPrefixInput (sp ra : BitVec 64) (c : Config) : Prop
    extends RaiseZeroPrefixMemory sp ra where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  stack : gpr c 2 = some sp
  returnReg : gpr c 1 = some ra

theorem raise_zero_stack (sp : BitVec 64) :
    sp + sign_extend (m := 64) (0xff0#12) = raiseZeroStack sp := by
  rw [show sign_extend (m := 64) (0xff0#12) = -(BitVec.ofNat 64 Layout.raiseZeroFrameBytes) from by decide]
  exact (BitVec.sub_eq_add_neg sp _).symm

theorem raise_zero_prefix_input {sp ra : BitVec 64} {c : Config} (h : RaiseZeroPrefixInput sp ra c) :
    BlockInput caml_raise_zero_divideXd1d4Seg 0x8000d1d4#64 [(2, sp), (1, ra)] [] c := by
  refine ⟨h.good, h.good.minstret, ⟨h.stack, h.returnReg, trivial⟩, ?_, ?_, ?_, h.tick⟩
  · change KeysOK [2, 1]; decide
  · have code := caml_raise_zero_divide_loaded h.image
    chain_facts code with "Vsa.Sim.Code.caml_raise_zero_divide_at_"
    apply h.raWrite.sd rfl
    change (sp + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x008#12) = raiseZeroRa sp
    rw [raise_zero_stack]; rfl
  · change ChainOK 0x8000d1d4#64 [2, 1] caml_raise_zero_divideXd1d4Seg; decide

/-- Native zero-divisor prologue and diagnostic argument from the pinned image. -/
theorem raise_zero_prefix {sp ra : BitVec 64} {c : Config} (h : RaiseZeroPrefixInput sp ra c) :
    FnSummary 0x8000d1d4#64 (fun start => start = c)
      (WriteRegistersPost [2, 10] (raiseZeroLog sp ra) c 0x8000d1e4#64 (BitVec.ofNat 64 Layout.raiseZeroMessage)
        [(10, BitVec.ofNat 64 Layout.raiseZeroMessage), (2, raiseZeroStack sp), (1, ra)]) := by
  apply registers_of_blocks h.image h.imageOutside (block_summary _ _ _ _ _ (raise_zero_prefix_input h))
  · change [(((sp + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x008#12)).toNat, 8, ra)] = _
    rw [raise_zero_stack]; rfl
  · rfl
  · change [(10, (0x8000d1d8#64 + sign_extend (m := 64) ((0x00049#20) +++ 0#12)) + sign_extend (m := 64) (0x330#12)),
      (2, sp + sign_extend (m := 64) (0xff0#12)), (1, ra)] = _
    rw [raise_zero_stack]; rfl
  · rfl
  · decide

end OCaml.Vm.Sim
