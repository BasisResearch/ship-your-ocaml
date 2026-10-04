import OCaml.Vm.Primitives.Word32Access
import OCaml.Vm.Primitives.ImageFrame
import OCaml.Vm.Primitives.MemoryFrame
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def pendingRootStack (sp : BitVec 64) : BitVec 64 :=
  sp - BitVec.ofNat 64 Layout.pendingRootFrameBytes

def pendingRootRa (sp : BitVec 64) : BitVec 64 :=
  pendingRootStack sp + BitVec.ofNat 64 Layout.pendingRootSaveRaOffset

def pendingRootValue (sp : BitVec 64) : BitVec 64 :=
  pendingRootStack sp + BitVec.ofNat 64 Layout.pendingRootSaveValueOffset

/-- The fast pending-action check still saves its return address and argument. -/
def pendingRootLog (sp ra value : BitVec 64) : List WEntry :=
  [((pendingRootRa sp).toNat, 8, ra), ((pendingRootValue sp).toNat, 8, value)]

/-- Scalar memory and ABI conditions for the actual no-pending-action path. -/
structure PendingRootInput (sp ra value : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  stack : gpr c 2 = some sp
  returnReg : gpr c 1 = some ra
  argument : gpr c 10 = some value
  aligned : ra.toNat % 4 = 0
  pending : word32 c Layout.sym_caml_something_to_do = 0#32
  raWrite : WriteWindow (pendingRootRa sp) 8
  valueWrite : WriteWindow (pendingRootValue sp) 8
  raOutside : OutLRange [((pendingRootValue sp).toNat, 8, value)] (pendingRootRa sp).toNat 8
  imageOutside : ImageOutside (pendingRootLog sp ra value)

/-- The fast check returns its unchanged root and restores the caller stack. -/
structure PendingRootPost (sp ra value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some ra
  stack : gpr after 2 = some sp
  result : gpr after 10 = some value
  memory : after.σ.mem = writeLog before.σ.mem (pendingRootLog sp ra value)
  frame : StepFrameOut ([Register.x1, Register.x2, Register.x15] ++ noiseRegs) before.σ after.σ

/-- A later argument save does not overwrite the saved native return address. -/
theorem pending_root_return_word {sp ra value : BitVec 64} {c : Config}
    (h : PendingRootInput sp ra value c) :
    bytesT (writeLog c.σ.mem (pendingRootLog sp ra value)) (pendingRootRa sp).toNat 8 = ra := by
  rw [show pendingRootLog sp ra value =
    [((pendingRootRa sp).toNat, 8, ra)] ++ [((pendingRootValue sp).toNat, 8, value)] from rfl,
    writeLog_append, bytesT_writeLog_out _ h.raOutside]
  exact word_writeLog _ _ _

end OCaml.Vm.Sim
