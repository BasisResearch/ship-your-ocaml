import OCaml.Vm.Sim.InterpReturnState
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The native ADDIW result; the subsequent SW retains its low 32 bits. -/
def stopDepth (c : Config) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb
    (sign_extend (m := 64) (bytesT4 c.σ.mem Layout.sym_caml_callback_depth) + sign_extend (m := 64) (0xfff#12)) 31 0)

/-- STOP decrements callback depth, publishes the VM stack and restores external_raise. -/
def stopLog (nativeSp : Nat) (vmSp : BitVec 64) (c : Config) : List WEntry :=
  [(Layout.sym_caml_callback_depth, 4, stopDepth c),
   ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp, 8, vmSp),
   ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise, 8, word c (nativeSp + 24))]

/-- Native invocation and memory separation supplied by the enclosing interpreter call. -/
structure StopInput (nativeSp : Nat) (saved : Nat → BitVec 64) (value vmSp : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x800032f4#64)
  tick : c.tick < 2
  frame : InterpSavedFrame nativeSp saved c
  stack : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  vmStack : gpr c Layout.reg_sp = some vmSp
  value : gpr c Layout.reg_accu = some value
  aligned : (saved 1).toNat % 4 = 0
  depthWrite : RamWriteAt Layout.sym_caml_callback_depth 4
  domainRead : RamReadAt Layout.sym_Caml_state 8
  savedRaiseRead : RamReadAt (nativeSp + 24) 8
  stackWrite : RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp) 8
  raiseWrite : RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8
  savedRaiseOutside : OutLRange [(Layout.sym_caml_callback_depth, 4, stopDepth c)] (nativeSp + 24) 8
  imageOutside : ImageOutside (stopLog nativeSp vmSp c)
  frameOutside : ∀ r ∈ Layout.interpSavedRegs, OutLRange (stopLog nativeSp vmSp c) (nativeSp + Layout.interpSaveOffset r) 8

/-- STOP's return preserves the ABI and records the three runtime stores explicitly. -/
structure StopReturnPost (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value vmSp : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (saved 1)
  stack : gpr after 2 = some (BitVec.ofNat 64 (nativeSp + Layout.interpFrameBytes))
  value : gpr after 10 = some value
  registers : ∀ r ∈ Layout.interpSavedRegs, gpr after r = some (saved r)
  memory : after.σ.mem = writeLog before.σ.mem (stopLog nativeSp vmSp before)
  output : after.σ.sailOutput = before.σ.sailOutput

end OCaml.Vm.Sim
