import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def grabReserveLog (domain a : Nat) : List WEntry :=
  [(domain + Layout.off_young_ptr, 8, BitVec.ofNat 64 (a - 8))]

/-- Scalar G1 nursery observations. These are memory and capacity conditions,
not an assumption about the allocating arm's execution. -/
structure NurseryInput (count a domain limit : Nat) (c : Config) : Prop where
  small : count < 2^31
  room : 8 ≤ a
  domainValue : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain
  youngValue : word c (domain + Layout.off_young_ptr) = BitVec.ofNat 64 (a + 8 * (count))
  limitValue : word c (domain + Layout.off_young_limit) = BitVec.ofNat 64 limit
  youngWrite : RamWriteAt (domain + Layout.off_young_ptr) 8
  limitRead : RamReadAt (domain + Layout.off_young_limit) 8
  headerWrite : RamWriteAt (a - 8) 8
  capacity : limit ≤ a - 8
  image : ImageOutside (grabReserveLog domain a)

/-- A prefix disjoint from the three nursery observations preserves its scalar input. -/
theorem NurseryInput.frame {count a domain limit : Nat} {before after : Config} {log : List WEntry}
    (space : NurseryInput count a domain limit before)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (domainOutside : OutLRange log Layout.sym_Caml_state 8)
    (youngOutside : OutLRange log (domain + Layout.off_young_ptr) 8)
    (limitOutside : OutLRange log (domain + Layout.off_young_limit) 8) :
    NurseryInput count a domain limit after := by
  have preserved (address : Nat) (outside : OutLRange log address 8) : word after address = word before address := by
    change bytesT after.σ.mem address 8 = bytesT before.σ.mem address 8
    rw [memory, bytesT_writeLog_out _ outside]
  exact ⟨space.small, space.room, (preserved _ domainOutside).trans space.domainValue,
    (preserved _ youngOutside).trans space.youngValue, (preserved _ limitOutside).trans space.limitValue,
    space.youngWrite, space.limitRead, space.headerWrite, space.capacity, space.image⟩

end OCaml.Vm.Sim
