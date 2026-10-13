import OCaml.Vm.Sim.Ccall
import OCaml.Vm.Sim.PlacePut

/-! The fresh placements of the allocating F1 primitives (`allocPlaces`) are
placeable: fresh, distinct locations at word-aligned nursery addresses. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

theorem mask8_aligned (x : BitVec 64) : (x &&& (-8#64)).toNat % 8 = 0 := by
  rw [BitVec.toNat_and, show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_assoc, show (-8#64).toNat &&& (2 ^ 3 - 1) = 0 by decide, Nat.and_zero]

theorem stringSpan_aligned (n : BitVec 64) : (StringAllocation.stringSpan n).toNat % 8 = 0 :=
  mask8_aligned _

theorem resultWord_aligned (young : BitVec 64) (len : Nat) (al : young.toNat % 8 = 0) :
    (StringCopy.resultWord young len).toNat % 8 = 0 := by
  have sp := stringSpan_aligned (BitVec.ofNat 64 len)
  unfold StringCopy.resultWord StringAllocation.nurseryHeader
  generalize StringAllocation.stringSpan (BitVec.ofNat 64 len) = k at sp
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sub8_aligned (x : BitVec 64) (al : x.toNat % 8 = 0) : (x - 8#64).toNat % 8 = 0 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem tupleWord_aligned (b : BitVec 64) (al : b.toNat % 8 = 0) : (ArgvTuple.tupleWord b).toNat % 8 = 0 := by
  unfold ArgvTuple.tupleWord SmallAllocation.nurseryHeader
  rw [show (2#64 <<< (3 : Nat)) = 16#64 by decide]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem tripleWord_aligned (b : BitVec 64) (al : b.toNat % 8 = 0) : (ConfigTuple.tripleWord b).toNat % 8 = 0 := by
  unfold ConfigTuple.tripleWord SmallAllocation.nurseryHeader
  rw [show (3#64 <<< (3 : Nat)) = 24#64 by decide]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem alloc_alloc_absent (h : Heap) (o o' : Obj) : h.get? ((h.alloc o).1.alloc o').2 = none := by
  simp [Heap.alloc, Heap.get?]

theorem alloc_alloc_ne (h : Heap) (o o' : Obj) : (h.alloc o).2 ≠ ((h.alloc o).1.alloc o').2 := by
  simp [Heap.alloc]

/-- **`allocPlaces` is placeable** for every primitive, state and aligned
young pointer. -/
theorem allocPlaces_ok (name : String) (s : St) (young : BitVec 64) (al : young.toNat % 8 = 0) :
    AllocPlacesOk name s young := by
  unfold AllocPlacesOk allocPlaces
  split
  · split
    · split
      · next bits _ =>
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.mem_singleton]; rintro p rfl; simp [Heap.alloc, Heap.get?]
        · simp only [List.mem_singleton]; rintro p rfl
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
        · simp
      · exact .nil _
    · exact .nil _
  · split
    · refine ⟨?_, ?_, ?_⟩
      · simp only [List.mem_singleton]; rintro p rfl; simp [Heap.alloc, Heap.get?]
      · simp only [List.mem_singleton]; rintro p rfl
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · simp
    · exact .nil _
  · split
    · refine ⟨?_, ?_, ?_⟩
      · simp only [List.mem_singleton]; rintro p rfl; simp [Heap.alloc, Heap.get?]
      · simp only [List.mem_singleton]; rintro p rfl
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · simp
    · exact .nil _
  · refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_singleton]; rintro p rfl; simp [Heap.alloc, Heap.get?]
    · simp only [List.mem_singleton]; rintro p rfl; exact resultWord_aligned _ _ al
    · simp
  · refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · simp [Heap.alloc, Heap.get?]
      · simp [Heap.alloc, Heap.get?, ArgvTuple.afterName, ConfigTuple.afterOsType]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact resultWord_aligned _ _ al
      · exact tupleWord_aligned _ (sub8_aligned _ (resultWord_aligned _ _ al))
    · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact alloc_alloc_ne _ _ _
  · refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · simp [Heap.alloc, Heap.get?]
      · simp [Heap.alloc, Heap.get?, ArgvTuple.afterName, ConfigTuple.afterOsType]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact resultWord_aligned _ _ al
      · exact tripleWord_aligned _ (sub8_aligned _ (resultWord_aligned _ _ al))
    · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact alloc_alloc_ne _ _ _
  · exact .nil _

end OCaml.Vm.Sim
