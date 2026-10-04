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

/-- Saved native invocation and store geometry, independent of the current PC.
The loop invariant must retain this state until the enclosing call returns. -/
structure StopInvocation (nativeSp : Nat) (saved : Nat → BitVec 64) (vmSp : BitVec 64) (c : Config) : Prop where
  frame : InterpSavedFrame nativeSp saved c
  stack : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  aligned : (saved 1).toNat % 4 = 0
  depthWrite : RamWriteAt Layout.sym_caml_callback_depth 4
  domainRead : RamReadAt Layout.sym_Caml_state 8
  savedRaiseRead : RamReadAt (nativeSp + 24) 8
  stackWrite : RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp) 8
  raiseWrite : RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8
  savedRaiseOutside : OutLRange [(Layout.sym_caml_callback_depth, 4, stopDepth c)] (nativeSp + 24) 8
  imageOutside : ImageOutside (stopLog nativeSp vmSp c)
  frameOutside : ∀ r ∈ Layout.interpSavedRegs, OutLRange (stopLog nativeSp vmSp c) (nativeSp + Layout.interpSaveOffset r) 8

/-- A read-only dispatch retains the native invocation and every store footprint. -/
theorem StopInvocation.frame_read {nativeSp : Nat} {saved : Nat → BitVec 64} {vmSp : BitVec 64}
    {c after : Config} (h : StopInvocation nativeSp saved vmSp c)
    (memory : after.σ.mem = c.σ.mem) (stack : gpr after 2 = gpr c 2) :
    StopInvocation nativeSp saved vmSp after := by
  refine ⟨h.frame.frame (log := []) (by intro r hr; trivial) memory,
    stack.trans h.stack, h.aligned, h.depthWrite, h.domainRead, h.savedRaiseRead, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [word, memory] using h.stackWrite
  · simpa only [word, memory] using h.raiseWrite
  · simpa only [stopDepth, memory] using h.savedRaiseOutside
  · simpa only [stopLog, stopDepth, word, memory] using h.imageOutside
  · simpa only [stopLog, stopDepth, word, memory] using h.frameOutside

/-- Entry to STOP with the enclosing invocation and represented result registers. -/
structure StopInput (nativeSp : Nat) (saved : Nat → BitVec 64) (value vmSp : BitVec 64) (c : Config) : Prop
    extends StopInvocation nativeSp saved vmSp c where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x800032f4#64)
  tick : c.tick < 2
  vmStack : gpr c Layout.reg_sp = some vmSp
  value : gpr c Layout.reg_accu = some value

/-- Shared interpreter return result after an explicit runtime-store log. -/
structure InterpRuntimeReturnPost (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value : BitVec 64) (log : List WEntry) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (saved 1)
  stack : gpr after 2 = some (BitVec.ofNat 64 (nativeSp + Layout.interpFrameBytes))
  value : gpr after 10 = some value
  registers : ∀ r ∈ Layout.interpSavedRegs, gpr after r = some (saved r)
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput

/-- Normal interpreter return with STOP's exact store order. -/
abbrev StopReturnPost (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value vmSp : BitVec 64) (after : Config) :=
  InterpRuntimeReturnPost before nativeSp saved value (stopLog nativeSp vmSp before) after

end OCaml.Vm.Sim
