import OCaml.Vm.Gc.G1Room
import OCaml.Vm.Primitives.SmallNursery
import OCaml.Vm.Primitives.StringNursery
import OCaml.Vm.Primitives.StringAllocationArithmetic
import OCaml.Vm.Primitives.Int64FloatFast

/-!
# G1 room as the primitives' nursery guards

The C allocation fast paths (`caml_alloc_small`, `caml_alloc_string`, boxed
doubles) test `young_ptr - bytes <u young_limit` and fall to the collector
when it holds. `G1Room` excludes that branch whenever the successor state is
within the budget: `G1Room.young_room` reads the room from the same machine
words the fast path loads, and `bltu_room` turns it into the `room` field of
`SmallAllocation.NurseryMemory`, `StringAllocation.NurseryGeometry` and
`DoubleAllocation.FastMemory`.
-/

namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The unsigned guard `young - d <u limit` fails when `d` bytes fit above the limit. -/
theorem bltu_room {young limit d : BitVec 64} (h : limit.toNat + d.toNat ≤ young.toNat) :
    guardB .BLTU (young - d) limit = false := by
  simp only [guardB]
  apply bltu_false_of_ge
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  omega

/-- The room in bytes between the loaded `young_limit` and `young_ptr`, for
the slots the fast paths address (`DoubleAllocation.youngSlot`/`limitSlot`). -/
theorem G1Room.young_room {B : Budget} {s : St} {c : Config} (room : G1Room B s c)
    {domain young limit : BitVec 64}
    (domainValue : word c DoubleAllocation.domainGlobal.toNat = domain)
    (youngValue : word c (DoubleAllocation.youngSlot domain).toNat = young)
    (limitValue : word c (DoubleAllocation.limitSlot domain).toNat = limit)
    (noWrap : domain.toNat + Layout.off_young_ptr < 2 ^ 64)
    {w : Nat} (fits : s.heap.words + w ≤ B.heapWords) : limit.toNat + 8 * w ≤ young.toNat := by
  have capacity := room.alloc_capacity fits
  have global : DoubleAllocation.domainGlobal.toNat = Layout.sym_Caml_state := by
    simp only [DoubleAllocation.domainGlobal, BitVec.toNat_ofNat, Layout.sym_Caml_state]
  have dom : (word c Layout.sym_Caml_state).toNat = domain.toNat := by rw [← global, domainValue]
  have youngSlot : (DoubleAllocation.youngSlot domain).toNat = domain.toNat + Layout.off_young_ptr := by
    simp only [DoubleAllocation.youngSlot, BitVec.toNat_add, BitVec.toNat_ofNat, Layout.off_young_ptr] at noWrap ⊢
    omega
  have limitSlot : (DoubleAllocation.limitSlot domain).toNat = domain.toNat + Layout.off_young_limit := by
    simp only [DoubleAllocation.limitSlot, BitVec.toNat_add, BitVec.toNat_ofNat, Layout.off_young_limit] at noWrap ⊢
    omega
  have ptr : (runtimeFields c).youngPtr = young.toNat := by
    simp only [runtimeFields, domainWord, dom, ← youngSlot, youngValue]
  have lim : (runtimeFields c).youngLimit = limit.toNat := by
    simp only [runtimeFields, domainWord, dom, ← limitSlot, limitValue]
  rw [ptr, lim] at capacity
  exact capacity

/-- `DoubleAllocation.FastMemory.room`: a boxed double is two words. -/
theorem G1Room.double_room {B : Budget} {s : St} {c : Config} (room : G1Room B s c)
    {domain young limit : BitVec 64}
    (domainValue : word c DoubleAllocation.domainGlobal.toNat = domain)
    (youngValue : word c (DoubleAllocation.youngSlot domain).toNat = young)
    (limitValue : word c (DoubleAllocation.limitSlot domain).toNat = limit)
    (noWrap : domain.toNat + Layout.off_young_ptr < 2 ^ 64)
    (fits : s.heap.words + 2 ≤ B.heapWords) :
    guardB .BLTU (young - 16#64) limit = false :=
  bltu_room (by have := room.young_room domainValue youngValue limitValue noWrap fits; simp; omega)

/-- `SmallAllocation.NurseryMemory.room`: `size` fields plus the header. -/
theorem G1Room.small_room {B : Budget} {s : St} {c : Config} (room : G1Room B s c)
    {domain young limit size : BitVec 64}
    (domainValue : word c DoubleAllocation.domainGlobal.toNat = domain)
    (youngValue : word c (DoubleAllocation.youngSlot domain).toNat = young)
    (limitValue : word c (DoubleAllocation.limitSlot domain).toNat = limit)
    (noWrap : domain.toNat + Layout.off_young_ptr < 2 ^ 64) (small : size.toNat < 2 ^ 32)
    (fits : s.heap.words + (size.toNat + 1) ≤ B.heapWords) :
    guardB .BLTU (SmallAllocation.nurseryHeader young size) limit = false := by
  have bytes := room.young_room domainValue youngValue limitValue noWrap fits
  have shifted : (size <<< 3).toNat = 8 * size.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  have total : (8#64 + (size <<< 3)).toNat = 8 * (size.toNat + 1) := by
    simp only [BitVec.toNat_add, shifted]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [SmallAllocation.nurseryHeader, BitVec.sub_sub]
  exact bltu_room (by rw [total]; omega)

/-- `StringAllocation.NurseryGeometry.room`: a byte string of `n` bytes takes
`n / 8 + 1` payload words (`Obj.wosize` of `.bytes`) plus the header. -/
theorem G1Room.string_room {B : Budget} {s : St} {c : Config} (room : G1Room B s c)
    {domain young limit : BitVec 64} {n : Nat}
    (domainValue : word c DoubleAllocation.domainGlobal.toNat = domain)
    (youngValue : word c (DoubleAllocation.youngSlot domain).toNat = young)
    (limitValue : word c (DoubleAllocation.limitSlot domain).toNat = limit)
    (noWrap : domain.toNat + Layout.off_young_ptr < 2 ^ 64) (small : n < 2 ^ 32)
    (fits : s.heap.words + (n / 8 + 2) ≤ B.heapWords) :
    guardB .BLTU (StringAllocation.nurseryHeader young (BitVec.ofNat 64 n)) limit = false := by
  have bytes := room.young_room domainValue youngValue limitValue noWrap fits
  have span := StringAllocation.stringSpan_toNat n small
  have total : (8#64 + StringAllocation.stringSpan (BitVec.ofNat 64 n)).toNat = 8 * (n / 8 + 2) := by
    simp only [BitVec.toNat_add, span, BitVec.toNat_ofNat]
    omega
  rw [StringAllocation.nurseryHeader, BitVec.sub_sub]
  exact bltu_room (by rw [total]; omega)

end OCaml.Vm.Gc
