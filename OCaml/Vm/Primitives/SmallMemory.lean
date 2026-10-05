import OCaml.Vm.Primitives.SmallNursery
import OCaml.Vm.Primitives.WriteLogObservation
import Vsa.Sim.Boot.Bytes

namespace OCaml.Vm.Primitives.SmallAllocation
open Vsa.Machine Vsa.Sim

/-- The nursery's memory requirements use only total reads, even after the
header store, and therefore transport across observationally equal maps. -/
theorem NurseryMemory.observed_transport {ra size tag domain young limit before after}
    (h : NurseryMemory ra size tag domain young limit before)
    (memory : Vsa.Densify.MemEqv after.σ.mem before.σ.mem) :
    NurseryMemory ra size tag domain young limit after := by
  have read (x : Nat) : word after x = word before x :=
    Boot.bytesT_memEqv memory x 8
  have logged := memory.writeLog (constructorLog ra size tag domain young)
  exact { h with
    domainValue := (read _).trans h.domainValue
    youngValue := (read _).trans h.youngValue
    limitValue := (read _).trans h.limitValue
    domainAfterHeader := (Boot.bytesT_memEqv logged _ 8).trans h.domainAfterHeader
    youngAfterHeader := (Boot.bytesT_memEqv logged _ 8).trans h.youngAfterHeader }

/-- Attach machine-proved ABI facts to the static nursery obligations. -/
theorem NurseryMemory.input {ra size tag domain young limit c}
    (h : NurseryMemory ra size tag domain young limit c)
    (leaf : LeafInput ra c) (sizeReg : gpr c 10 = some size) (tagReg : gpr c 11 = some tag) :
    NurseryInput ra size tag domain young limit c :=
  { h with toLeafInput := leaf, sizeReg := sizeReg, tagReg := tagReg }

end OCaml.Vm.Primitives.SmallAllocation
