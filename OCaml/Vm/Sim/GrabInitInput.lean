import OCaml.Vm.Sim.GrabNurseryInput
import OCaml.Vm.Sim.ClosureLayout
import OCaml.Vm.Sim.CursorCopy

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def grabInitLog (a extra : Nat) (env : BitVec 64) : List WEntry :=
  [(a - 8, 8, blockHeader (extra + 4) closureTag), (a + 16, 8, env)]

def grabSetupLog (domain a extra : Nat) (env : BitVec 64) : List WEntry :=
  grabReserveLog domain a ++ grabInitLog a extra env

/-- Static initializer and source-copy conditions, supplied by the nursery and
stack separation invariant. No machine transition is assumed. -/
structure GrabInitInput (sp extra a domain : Nat) (env : BitVec 64) (c : Config) : Prop where
  envWrite : RamWriteAt (a + 16) 8
  image : ImageOutside (grabInitLog a extra env)
  domainOutside : OutLRange (grabReserveLog domain a ++ [(a - 8, 8, blockHeader (extra + 4) closureTag)]) Layout.sym_Caml_state 8
  youngOutside : OutLRange [(a - 8, 8, blockHeader (extra + 4) closureTag)] (domain + Layout.off_young_ptr) 8
  copy : CursorCopyRegion sp (a + 24) (stackWords c sp (1 + extra)) c
  sourceOutside : OutLRange (grabSetupLog domain a extra env) sp (8 * (1 + extra))

def grabInitWrites : List Register :=
  [Register.x10, Register.x11, Register.x12, Register.x14, Register.x15, Register.x21] ++ noiseRegs

def grabSetupWrites : List Register :=
  [Register.x10, Register.x11, Register.x12, Register.x13, Register.x14, Register.x15,
   Register.x16, Register.x17, Register.x21, Register.x23] ++ noiseRegs

/-- Initializer observations carried across the saved-argument copy. -/
structure GrabCopyStart (before : Config) (sp extra a domain : Nat) (env : BitVec 64) (after : Config) : Prop where
  copy : CursorCopyAt sp (a + 24) (stackWords before sp (1 + extra)) after 0 after
  header : gpr after 11 = some (BitVec.ofNat 64 (a - 8))
  value : gpr after 10 = some (BitVec.ofNat 64 a)
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  bytes : gpr after 16 = some (BitVec.ofNat 64 (8 * (extra + 4)))
  memory : after.σ.mem = writeLog before.σ.mem (grabSetupLog domain a extra env)
  frame : StepFrameOut grabSetupWrites before.σ after.σ

/-- Reservation and initialization preserve the copy's original source words. -/
theorem GrabInitInput.copy_after {sp extra a domain : Nat} {env : BitVec 64} {c after : Config}
    (space : GrabInitInput sp extra a domain env c) (front : GrabCopyStart c sp extra a domain env after) :
    CursorCopyRegion sp (a + 24) (stackWords c sp (1 + extra)) after := by
  refine ⟨space.copy.upper, space.copy.reads, space.copy.writes, space.copy.image, space.copy.separate, ?_⟩
  intro i w selected
  have bound : i < 1 + extra := by
    have b := (List.getElem?_eq_some_iff.mp selected).1
    simpa only [stackWords, List.length_map, List.length_range] using b
  have outside := outLRange_subrange space.sourceOutside (show sp ≤ sp + 8 * i by omega)
    (show sp + 8 * i + 8 ≤ sp + 8 * (1 + extra) by omega)
  change bytesT after.σ.mem (sp + 8 * i) 8 = w
  rw [front.memory, bytesT_writeLog_out _ outside]
  exact space.copy.snapshot i w selected

end OCaml.Vm.Sim
