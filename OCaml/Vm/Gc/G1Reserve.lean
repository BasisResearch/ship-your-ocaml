import OCaml.Vm.Gc.G1Room
import OCaml.Vm.Sim.ArmGeometry

/-! The allocating arms' `Sim.NurseryReserve` from the G1 room: capacity from
`G1Room` and the successor state's budget, alignment from the nursery
geometry; the arm supplies its own `young_ptr` facts. -/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Sim

/-- **`NurseryReserve` from the G1 room.** An object of `size ≤ count` fields
reserved below `young_ptr = a + 8 * count`, where the successor state stays
within the budget (`s.heap.words + (count + 1) ≤ B.heapWords`, from `Fits`). -/
theorem NurseryReserve.of_room {B : Budget} {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} {log : List WEntry} {a size count : Nat}
    (room : G1Room B s c) (g : NurseryGeometry P s c pl cp high)
    (before : (runtimeFields c).youngPtr = a + 8 * count) (fieldCount : size ≤ count)
    (fits : s.heap.words + (count + 1) ≤ B.heapWords)
    (after : ∀ c' : Config, c'.σ.mem = writeLog c.σ.mem log →
      (runtimeFields c').youngPtr = a - 8 ∧ (runtimeFields c').youngLimit = (runtimeFields c).youngLimit) :
    NurseryReserve c log a size count := by
  have capacity := room.alloc_capacity fits
  have aligned := g.aligned
  rw [before] at capacity aligned
  exact ⟨before, fieldCount, by omega, by omega, by omega, after⟩

end OCaml.Vm.Gc
