import OCaml.Vm.Gc.G1RoomDefs
import OCaml.Vm.Boot.WhileMinRuntime
import OCaml.Programs.WhileMin

/-! G1 room for any configuration holding the certified `whileMin` cut memory
(low enough for the boot entry to cite). -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot OCaml.Vm.Boot

theorem whileMin_init_words : whileMin.init.heap.words = 100 := by decide +kernel

/-- Room for any configuration whose memory is the certified cut memory. -/
theorem whileMin_g1Room_of {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial WhileMinLog.log)) :
    G1Room g1Budget whileMin.init c := by
  constructor
  rw [WhileMinRuntime.fields memory, whileMin_init_words]
  decide +kernel

end OCaml.Vm.Gc
