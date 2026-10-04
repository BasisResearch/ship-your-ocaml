import OCaml.Vm.Sim.RaiseRuntimeRows
import OCaml.Vm.Sim.RaiseRuntimeImage
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.Read
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

def raiseRuntimeStack (sp : BitVec 64) : BitVec 64 :=
  sp - BitVec.ofNat 64 Layout.raiseRuntimeFrameBytes

def raiseRuntimeRa (sp : BitVec 64) : BitVec 64 :=
  raiseRuntimeStack sp + BitVec.ofNat 64 Layout.raiseRuntimeSaveRaOffset

def raiseRuntimeLog (sp ra : BitVec 64) : List WEntry := [( (raiseRuntimeRa sp).toNat, 8, ra)]

/-- The disabled channel-unlock hook selects the direct pending-action call. -/
structure RaiseRuntimePrefixMemory (sp ra : BitVec 64) (c : Config) : Prop where
  hook : word c Layout.sym_caml_channel_mutex_unlock_exn = 0#64
  raWrite : WriteWindow (raiseRuntimeRa sp) 8
  imageOutside : ImageOutside (raiseRuntimeLog sp ra)

structure RaiseRuntimePrefixInput (sp ra value : BitVec 64) (c : Config) : Prop
    extends RaiseRuntimePrefixMemory sp ra c where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  stack : gpr c 2 = some sp
  returnReg : gpr c 1 = some ra
  argument : gpr c 10 = some value

theorem raise_runtime_stack (sp : BitVec 64) :
    sp + sign_extend (m := 64) (0xfe0#12) = raiseRuntimeStack sp := by
  rw [show sign_extend (m := 64) (0xfe0#12) = -(BitVec.ofNat 64 Layout.raiseRuntimeFrameBytes) from by decide]
  exact (BitVec.sub_eq_add_neg sp _).symm

theorem raise_runtime_prefix_input {sp ra value : BitVec 64} {c : Config}
    (h : RaiseRuntimePrefixInput sp ra value c) :
    BlockInput caml_raiseXce20TSeg 0x8000ce20#64 [(2, sp), (1, ra), (10, value)]
      [read8 c.σ.mem Layout.sym_caml_channel_mutex_unlock_exn] c := by
  refine ⟨h.good, h.good.minstret, ⟨h.stack, h.returnReg, h.argument, trivial⟩, ?_, ?_, ?_, h.tick⟩
  · change KeysOK [2, 1, 10]; decide
  · have code := caml_raise_loaded h.image
    chain_facts code with "Vsa.Sim.Code.caml_raise_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_caml_channel_mutex_unlock_exn)
        (by constructor <;> decide) rfl
        (by change (0x8000ce20#64 + sign_extend (m := 64) ((0x00058#20) +++ 0#12)) + sign_extend (m := 64) (0xd28#12) = BitVec.ofNat 64 Layout.sym_caml_channel_mutex_unlock_exn; decide)
      change LPins8 c.σ.mem Layout.sym_caml_channel_mutex_unlock_exn (read8 c.σ.mem Layout.sym_caml_channel_mutex_unlock_exn)
      exact read8_pins _ _
    · apply h.raWrite.sd rfl
      change (sp + sign_extend (m := 64) (0xfe0#12)) + sign_extend (m := 64) (0x018#12) = raiseRuntimeRa sp
      rw [raise_runtime_stack]; rfl
    · change (bytesVal .ld (read8 c.σ.mem Layout.sym_caml_channel_mutex_unlock_exn) == 0#64) = true
      rw [read8_value]
      change (word c Layout.sym_caml_channel_mutex_unlock_exn == 0#64) = true
      rw [h.hook]; decide
  · change ChainOK 0x8000ce20#64 [2, 1, 10] caml_raiseXce20TSeg; decide

/-- The generated five-instruction prefix saves the native caller and selects the pending-action call. -/
theorem raise_runtime_prefix {sp ra value : BitVec 64} {c : Config}
    (h : RaiseRuntimePrefixInput sp ra value c) :
    FnSummary 0x8000ce20#64 (fun start => start = c)
      (WriteRegistersPost [2, 15] (raiseRuntimeLog sp ra) c 0x8000ce40#64 value
        [(2, raiseRuntimeStack sp), (15, 0#64), (1, ra), (10, value)]) := by
  apply registers_of_blocks h.image h.imageOutside (block_summary _ _ _ _ _ (raise_runtime_prefix_input h))
  · change [(((sp + sign_extend (m := 64) (0xfe0#12)) + sign_extend (m := 64) (0x018#12)).toNat, 8, ra)] = _
    rw [raise_runtime_stack]; rfl
  · rfl
  · change [(2, sp + sign_extend (m := 64) (0xfe0#12)),
      (15, bytesVal .ld (read8 c.σ.mem Layout.sym_caml_channel_mutex_unlock_exn)), (1, ra), (10, value)] = _
    rw [raise_runtime_stack, read8_value]
    change [(2, raiseRuntimeStack sp), (15, word c Layout.sym_caml_channel_mutex_unlock_exn), (1, ra), (10, value)] = _
    rw [h.hook]
  · rfl
  · decide

end OCaml.Vm.Sim
