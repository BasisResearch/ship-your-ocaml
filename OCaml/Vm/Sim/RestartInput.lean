import OCaml.Vm.Sim.RestartRestore
import OCaml.Vm.Sim.ForwardCopy
import OCaml.Vm.Sim.RestartArithmetic
import OCaml.Vm.Sim.EnterFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Concrete native accesses for RESTART; the represented invariant supplies
geometry and stack capacity, while source words come from the live closure. -/
structure RestartInput (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high a : Nat) (fields : List Val) : Prop
    extends RestartWriteOk P s c pl cp sp high a fields where
  headerRoom : 8 ≤ a
  headerRead : RamReadAt (a - 8) 8
  envRead : RamReadAt (a + 16) 8
  lower : 3 ≤ fields.length
  small : fields.length < 2^31
  reads : ∀ i, i < fields.length - 3 → RamReadAt (a + 24 + 8 * i) 8
  writes : ∀ i, i < fields.length - 3 → RamWriteAt (restartStart sp fields + 8 * i) 8

def restartSetupWrites : List Register :=
  [Register.x9, Register.x11, Register.x12, Register.x13, Register.x14, Register.x15, Register.x23] ++ noiseRegs

/-- Native setup observations, including the empty-copy path. -/
structure RestartCopyStart (before : Config) (sp a code : Nat) (fields : List Val) (after : Config) : Prop where
  copy : ForwardCopyAt a (restartStart sp fields) (stackWords before (a + 24) (fields.length - 3)) after 0 after
  spReg : gpr after 9 = some (BitVec.ofNat 64 (restartStart sp fields))
  nextCode : gpr after 23 = some (BitVec.ofNat 64 code)
  extraCount : gpr after 11 = some (BitVec.ofNat 64 (fields.length - 3))
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut restartSetupWrites before.σ after.σ

/-- Live-object separation supplies the entire closure-field source window. -/
theorem RestartInput.copy_region {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a tag : Nat} {fields : List Val}
    (space : RestartInput P s c pl cp sp high a fields)
    (block : BlockSelection s.heap pl s.env l a tag fields) :
    ForwardCopyRegion a (restartStart sp fields) (stackWords c (a + 24) (fields.length - 3)) c := by
  have length : (stackWords c (a + 24) (fields.length - 3)).length = fields.length - 3 := by simp [stackWords]
  refine ⟨?_, ?_, ?_, space.image, ?_, ?_⟩
  all_goals simp only [restartCopyShape, IndexedCopyShape.sourceStart, IndexedCopyShape.targetStart, Bool.true_eq, ite_true, Nat.add_zero]
  · rw [length]; have low := space.lower; have small := space.small; omega
  · simpa only [length] using space.reads
  · simpa only [length] using space.writes
  · have whole := (space.payload.heap l a (.block tag fields)
      (block.live (by simp [roots])) block.placed block.object).payload
    rw [length]
    apply outLRange_subrange whole (by omega)
    change a + 24 + 8 * (fields.length - 3) ≤ a + 8 * fields.length
    have low := space.lower
    omega
  · intro i w selected
    have bound : i < fields.length - 3 := by
      have b := (List.getElem?_eq_some_iff.mp selected).1
      simpa only [length] using b
    simpa only [stackWords, List.getElem?_map, List.getElem?_range, bound, ite_true,
      Option.map_some, Option.some.injEq] using selected

/-- The memory-preserving prefix carries the same closure snapshot to the loop. -/
theorem RestartInput.copy_after {P : Prog} {s : St} {c after : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a tag : Nat} {fields : List Val}
    (space : RestartInput P s c pl cp sp high a fields)
    (block : BlockSelection s.heap pl s.env l a tag fields)
    {code : Nat} (front : RestartCopyStart c sp a code fields after) :
    ForwardCopyRegion a (restartStart sp fields) (stackWords c (a + 24) (fields.length - 3)) after := by
  have region := space.copy_region block
  refine ⟨region.small, region.reads, region.writes, region.image, region.separate, ?_⟩
  intro i w selected
  simpa only [word, front.memory] using region.snapshot i w selected

end OCaml.Vm.Sim
