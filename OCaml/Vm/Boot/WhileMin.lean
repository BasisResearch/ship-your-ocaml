import OCaml.Vm.Boot.WhileMinEntry
import OCaml.Vm.Boot.WhileMinImage
import OCaml.Vm.Boot.WhileMinRegisterData
import OCaml.Vm.Boot.WhileMinPrimitives

/-! Closed `Loaded` witness for the captured while_min interpreter entry.

The complete defined register table, counters and console are native
observations from `Vsa.setupElf` / `Vsa.stepOnce`. The native capture also
checks every candidate memory byte and the memory-map cardinality. Memory
is represented by the emulator's ELF loader image and the kernel-checked
store log. The theorems below check `Loaded` for this concrete snapshot;
they do not prove the 4,269,257-step startup run in the kernel.
-/
namespace OCaml.Vm.Boot.WhileMin
open OCaml.Programs Vsa.Machine Vsa.Sim.Boot

/-- Keep the large map behind its proved read interface during elaboration. -/
@[irreducible] def memory : Vsa.MemRepr.Mem :=
  observedMem WhileMinImage.initialMem WhileMinLog.log

theorem memory_eq : memory = observedMem WhileMinImage.initialMem WhileMinLog.log := by
  unfold memory
  rfl

/-- The complete captured cut configuration; no abstract heap was used to
construct its memory or registers. -/
def cut : Config :=
  ⟨WhileMinRegisters.state memory,
    WhileMinRegisters.tick, WhileMinRegisters.steps⟩

theorem memory_equiv : Vsa.Densify.MemEqv cut.σ.mem
    (observedMem WhileMinImage.initialMem WhileMinLog.log) := by
  rw [show cut.σ.mem = memory from rfl, memory_eq]
  exact Vsa.Densify.MemEqv.refl _

theorem atEntry : pcOf cut = some (BitVec.ofNat 64 Layout.sym_caml_interprete) :=
  WhileMinRegisters.get_PC

theorem argCode : gpr cut 10 = some (BitVec.ofNat 64 WhileMinHeap.place.codeBase) :=
  WhileMinRegisters.get_x10

theorem code_size : whileMin.code.size = 191 := by decide +kernel

theorem argSize : gpr cut 11 = some (BitVec.ofNat 64 (4 * whileMin.code.size)) := by
  rw [code_size]
  exact WhileMinRegisters.get_x11

theorem console : output cut.σ = "" := rfl

/-- All remaining platform and call-register facts for the captured cut. -/
theorem control : WhileMinEntry.EntryControl cut where
  atEntry := atEntry
  argCode := argCode
  argSize := argSize
  console := console
  control := WhileMinRegisters.good_state memory
  image := WhileMinImage.executable (c := cut) memory_eq
  primitives := WhileMinPrimitives.bindings (c := cut) (initial := WhileMinImage.initialMem) memory_equiv

/-- The captured machine entry satisfies the complete loaded-state relation. -/
theorem loaded : Loaded (runtimeLayout BestFitSingleton) whileMin cut :=
  WhileMinEntry.loaded (c := cut) (initial := WhileMinImage.initialMem) memory_equiv control

/-- A0's closed densified-entry witness, with the concrete collector invariant. -/
theorem loaded_fillZero :
    Loaded (runtimeLayout BestFitSingleton) whileMin (Vsa.Densify.fillZero cut) :=
  WhileMinEntry.loaded_fillZero (c := cut) (initial := WhileMinImage.initialMem) memory_eq control

end OCaml.Vm.Boot.WhileMin
