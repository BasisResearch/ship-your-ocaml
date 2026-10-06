import OCaml.Vm.Gc.G1RoomDefs
import OCaml.Vm.Gc.G1RoomTransport

/-!
# G1: the allocation fast path never reaches the limit

Under G1 (PLAN.md §GC strategy) no minor collection happens after the cut:
`Fits B P` bounds `s.heap.words`, and the machine's remaining nursery covers
what the budget still allows. `G1Room` is that relation between a `BcSem`
state and a machine configuration. An allocating arm consumes it through
`G1Room.nursery_capacity` (the `capacity` field of `Sim.NurseryInput`) and
re-establishes it through `G1Room.step`/`reserve`, or through `frame`/`same`
for non-allocating arms. It sits below `OCaml/Refinement.lean` so the loop-head
witness can carry it; stack capacity is the arms' `StackCapacity`.
-/

namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine

/-- Room for `w` more words whenever the budget allows them. -/
theorem G1Room.alloc_capacity {B : Budget} {s : St} {c : Config} (room : G1Room B s c) {w : Nat}
    (fits : s.heap.words + w ≤ B.heapWords) :
    (runtimeFields c).youngLimit + 8 * w ≤ (runtimeFields c).youngPtr := by
  have := room.nursery
  omega

/-- The `capacity` field of `Sim.NurseryInput`: an arm allocating `count + 1`
words (header included) below `young_ptr = a + 8 * count` stays above
`young_limit`, given that the successor state is within the budget. -/
theorem G1Room.nursery_capacity {B : Budget} {s : St} {c : Config} (room : G1Room B s c)
    {count a domain limit : Nat}
    (domainValue : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain)
    (youngValue : word c (domain + Layout.off_young_ptr) = BitVec.ofNat 64 (a + 8 * count))
    (limitValue : word c (domain + Layout.off_young_limit) = BitVec.ofNat 64 limit)
    (domainRange : domain < 2 ^ 64) (youngRange : a + 8 * count < 2 ^ 64) (limitRange : limit < 2 ^ 64)
    (fits : s.heap.words + (count + 1) ≤ B.heapWords) : limit ≤ a - 8 := by
  have capacity := room.alloc_capacity fits
  have dom : (word c Layout.sym_Caml_state).toNat = domain := by
    rw [domainValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt domainRange]
  have ptr : (runtimeFields c).youngPtr = a + 8 * count := by
    simp only [runtimeFields, domainWord, dom, youngValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt youngRange]
  have lim : (runtimeFields c).youngLimit = limit := by
    simp only [runtimeFields, domainWord, dom, limitValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt limitRange]
  rw [ptr, lim] at capacity
  omega

end OCaml.Vm.Gc
