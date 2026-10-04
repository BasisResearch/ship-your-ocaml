import OCaml.Vm.Sim.RaiseRuntimeRows
import OCaml.Vm.Sim.RaiseRuntimeImage
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.Read
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

def raiseExternal (domain : BitVec 64) : BitVec 64 := domain + BitVec.ofNat 64 Layout.off_external_raise

def raiseBucket (domain : BitVec 64) : BitVec 64 := domain + BitVec.ofNat 64 Layout.off_exn_bucket

def raiseBucketLog (domain value : BitVec 64) : List WEntry := [((raiseBucket domain).toNat, 8, value)]

def raiseSuffixBlocks : List BBlock := caml_raiseXce44TSeg ++ caml_raiseXce58FSeg ++ caml_raiseXce6cSeg

/-- Ordinary exception values and an installed native exception handler select longjmp. -/
structure RaiseRuntimeSuffixInput (domain buffer value : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  argument : gpr c 10 = some value
  ordinary : value &&& 3#64 ≠ 2#64
  domainWord : word c Layout.sym_Caml_state = domain
  externalRead : ReadWindow (raiseExternal domain) 8
  externalWord : word c (raiseExternal domain).toNat = buffer
  nonzero : buffer ≠ 0#64
  bucketWrite : WriteWindow (raiseBucket domain) 8
  imageOutside : ImageOutside (raiseBucketLog domain value)

def raiseSuffixLoads (c : Config) (domain : BitVec 64) : List (List (BitVec 8)) :=
  [read8 c.σ.mem Layout.sym_Caml_state, read8 c.σ.mem (raiseExternal domain).toNat]

theorem raise_runtime_suffix_input {domain buffer value : BitVec 64} {c : Config}
    (h : RaiseRuntimeSuffixInput domain buffer value c) :
    BlockInput raiseSuffixBlocks 0x8000ce44#64 [(10, value)] (raiseSuffixLoads c domain) c := by
  have domainLoad : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = domain := by
    rw [read8_value]; exact h.domainWord
  have bufferLoad : bytesVal .ld (read8 c.σ.mem (raiseExternal domain).toNat) = buffer := by
    rw [read8_value]; exact h.externalWord
  refine ⟨h.good, h.good.minstret, ⟨h.argument, trivial⟩, ?_, ?_, ?_, h.tick⟩
  · change KeysOK [10]; decide
  · have code := caml_raise_loaded h.image
    chain_facts code with "Vsa.Sim.Code.caml_raise_at_"
    · change (value &&& 3#64 != 2#64) = true
      exact bne_iff_ne.mpr h.ordinary
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_Caml_state)
        (by constructor <;> decide) rfl
        (by change (0x8000ce58#64 + sign_extend (m := 64) ((0x00058#20) +++ 0#12)) + sign_extend (m := 64) (0xeb0#12) = BitVec.ofNat 64 Layout.sym_Caml_state; decide)
      change LPins8 c.σ.mem Layout.sym_Caml_state (read8 c.σ.mem Layout.sym_Caml_state)
      exact read8_pins _ _
    · apply h.externalRead.ld rfl
        (by change bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) + sign_extend (m := 64) (0x0b8#12) = raiseExternal domain; rw [domainLoad]; rfl)
      change LPins8 c.σ.mem (raiseExternal domain).toNat (read8 c.σ.mem (raiseExternal domain).toNat)
      exact read8_pins _ _
    · apply h.bucketWrite.sd rfl
      change bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) + sign_extend (m := 64) (0x0c0#12) = raiseBucket domain
      rw [domainLoad]; rfl
    · change (bytesVal .ld (read8 c.σ.mem (raiseExternal domain).toNat) == 0#64) = false
      rw [bufferLoad]
      exact beq_eq_false_iff_ne.mpr h.nonzero
  · change ChainOK 0x8000ce44#64 [10] raiseSuffixBlocks; decide

/-- Publish the exception and prepare the nonlocal return through the generated CFG. -/
theorem raise_runtime_suffix {domain buffer value : BitVec 64} {c : Config}
    (h : RaiseRuntimeSuffixInput domain buffer value c) :
    FnSummary 0x8000ce44#64 (fun start => start = c)
      (WriteRegistersPost [10, 11, 13, 14, 15] (raiseBucketLog domain value) c 0x8000ce70#64 buffer
        [(11, 1#64), (10, buffer), (14, domain), (15, value), (13, value &&& 3#64)]) := by
  have domainLoad : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = domain := by
    rw [read8_value]; exact h.domainWord
  have bufferLoad : bytesVal .ld (read8 c.σ.mem (raiseExternal domain).toNat) = buffer := by
    rw [read8_value]; exact h.externalWord
  apply registers_of_blocks h.image h.imageOutside (block_summary _ _ _ _ _ (raise_runtime_suffix_input h))
  · change [((bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) + sign_extend (m := 64) (0x0c0#12)).toNat, 8, value + 0#64)] = _
    rw [domainLoad, BitVec.add_zero]; rfl
  · rfl
  · change [(11, 1#64), (10, bytesVal .ld (read8 c.σ.mem (raiseExternal domain).toNat)),
      (14, bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state)), (15, value + 0#64), (13, value &&& 3#64)] = _
    rw [domainLoad, bufferLoad, BitVec.add_zero]
  · rfl
  · decide

end OCaml.Vm.Sim
