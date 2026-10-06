import OCaml.Vm.Boot.WhileMinCaller
import OCaml.Vm.Gc.WhileMinNursery

/-! Closed `Loaded` witness for the captured while_min interpreter entry,
including caml_main's call (`interpCaller`) and the initial placement
(`stackGeometry`) from `WhileMinCaller.lean`. -/
namespace OCaml.Vm.Boot.WhileMin
open OCaml.Programs Vsa.Machine Vsa.Sim.Boot

/-- All remaining platform and call-register facts for the captured cut. -/
theorem control : WhileMinEntry.EntryControl cut where
  atEntry := atEntry
  argCode := argCode
  argSize := argSize
  console := console
  control := WhileMinRegisters.good_state memory
  image := WhileMinImage.executable (c := cut) memory_eq
  primitives := WhileMinPrimitives.bindings (c := cut) (initial := WhileMinImage.initialMem) memory_equiv
  caller := ⟨callerSp, callerRegs, mainSaved, interpCaller⟩
  geometry := ⟨stackGeometry, OCaml.Vm.Gc.whileMin_nurseryGeometry⟩

/-- The captured machine entry satisfies the complete loaded-state relation. -/
theorem loaded : Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) whileMin cut :=
  WhileMinEntry.loaded (c := cut) (initial := WhileMinImage.initialMem) memory_equiv control

/-- A0's closed densified-entry witness, with the concrete collector invariant. -/
theorem loaded_fillZero :
    Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) whileMin (Vsa.Densify.fillZero cut) :=
  WhileMinEntry.loaded_fillZero (c := cut) (initial := WhileMinImage.initialMem) memory_eq control

end OCaml.Vm.Boot.WhileMin
