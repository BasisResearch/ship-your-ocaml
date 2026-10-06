import OCaml.Vm.Boot.WhileMinCaller
import OCaml.Vm.Gc.WhileMinNursery

/-! Closed `Loaded` witness for the captured while_min interpreter entry,
including caml_main's call (`interpCaller`) and the initial placement
(`stackGeometry`) from `WhileMinCaller.lean`. -/
namespace OCaml.Vm.Boot.WhileMin
open OCaml.Programs OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.Boot

/-- No startup store writes `oo_last_id`: it keeps its `.data` initializer `Val_int(0)`. -/
theorem ooCounter : word cut Layout.sym_oo_last_id = tag64 (BitVec.ofNat 63 0) := by
  have absent : ∀ i, i < 8 → WhileMinLog.runs.fin (Layout.sym_oo_last_id + i) = none := by decide +kernel
  have image : bytesT WhileMinImage.initialMem Layout.sym_oo_last_id 8 = 1#64 :=
    (loaderMem_bytes WhileMinImage.pieces WhileMinImage.imageByte Layout.sym_oo_last_id 8).trans (by decide +kernel)
  unfold word
  rw [bytesT_memEqv memory_equiv, observedMem_bytes WhileMinLog.logOk]
  rw [viewBytes_congr (v' := fun x => WhileMinImage.initialMem[x]?) (fun i hi => by
    simp only [logView, absent i hi])]
  rw [← bytesT_view (fun _ => rfl), image]
  decide

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
  ooCounter := ooCounter

/-- The captured machine entry satisfies the complete loaded-state relation. -/
theorem loaded : Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) whileMin cut :=
  WhileMinEntry.loaded (c := cut) (initial := WhileMinImage.initialMem) memory_equiv control

/-- A0's closed densified-entry witness, with the concrete collector invariant. -/
theorem loaded_fillZero :
    Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) whileMin (Vsa.Densify.fillZero cut) :=
  WhileMinEntry.loaded_fillZero (c := cut) (initial := WhileMinImage.initialMem) memory_eq control

end OCaml.Vm.Boot.WhileMin
