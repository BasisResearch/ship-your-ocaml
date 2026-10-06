import OCaml.Vm.Gc.NurseryGeometry
import OCaml.Vm.Boot.WhileMin

/-! Nursery geometry at the captured `whileMin` cut. The free nursery is
`[0x80082000, 0x80281ce0)`; `Caml_state` and `.bss` lie below it, and the VM
stack, code, atom table, primitive table and every placed object above it
(the two nursery objects sit above `young_ptr`, the globals above the major
free block). -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim Boot

theorem whileMin_addresses_high : ∀ a ∈ WhileMinHeap.addresses, 0x80281ce8 ≤ a := by decide

/-- Placed cut objects miss the private free block: globals lie above it, the
two nursery objects below it. -/
theorem whileMin_heapPrivate {l a : Nat} {o : Obj} (placed : WhileMinHeap.place.φ l = some a)
    (object : whileMin.init.heap.get? l = some o) :
    OutWRange [privateRegion] (a - 8) (8 * o.wosize + 8) := by
  have bound : l < 29 := by
    have := (List.getElem?_eq_some_iff.1 placed).1
    simpa [WhileMinHeap.addresses] using this
  have check : ∀ l : Fin 29,
      (match WhileMinHeap.addresses[l.val]?, whileMin.init.heap.get? l.val with
        | some a, some o => decide (a - 8 + (8 * o.wosize + 8) ≤ 0x80283000 ∨ 0x8037ad00 ≤ a - 8)
        | _, _ => true) = true := by
    decide +kernel
  have placed' : WhileMinHeap.addresses[l]? = some a := placed
  have h := check ⟨l, bound⟩
  simp only [placed', object, decide_eq_true_eq] at h
  exact ⟨by simpa only [privateRegion] using h, trivial⟩

/-- **`NurseryGeometry` at the cut.** -/
theorem whileMin_nurseryGeometry :
    NurseryGeometry whileMin whileMin.init WhileMin.cut WhileMinHeap.place (fun _ => none) WhileMinEntry.high := by
  have rf := WhileMinRuntime.fields WhileMin.memory_equiv
  have dom := WhileMinRuntime.read_domain WhileMin.memory_equiv
  have prims := WhileMinPrimitives.read_table WhileMin.memory_equiv
  have free : nurseryFree WhileMin.cut = ⟨0x80082000, 0x80281ce0⟩ := by
    simp only [nurseryFree, rf, WhileMinObservation.observed]
  have domNat : (word WhileMin.cut Layout.sym_Caml_state).toNat = 0x8007d150 := by rw [dom]; rfl
  have above : ∀ x n, 0x80281ce0 ≤ x → OutWRange [nurseryFree WhileMin.cut] x n := fun x n h => by
    rw [free]; exact ⟨Or.inr h, trivial⟩
  exact {
    statics := by rw [free]; decide
    domain := by rw [free, domNat]; exact ⟨Or.inl (by decide), trivial⟩
    stack := above _ _ (by simp [WhileMinEntry.high, Layout.stackBytes])
    code := fun i v _ => above _ _ (by simp [WhileMinHeap.place]; omega)
    heap := fun l a o placed _ => by
      have member : a ∈ WhileMinHeap.addresses := List.mem_of_getElem? placed
      have := whileMin_addresses_high a member
      exact above _ _ (by omega)
    channels := fun id ch a _ none => by cases none
    channelsPrivate := fun id ch a _ none => by cases none
    primitives := fun i name _ => above _ _ (by rw [prims]; simp; omega)
    top := by rw [rf]; decide
    aligned := by rw [rf]; decide
    domainLow := by rw [domNat]; decide
    domainHigh := by rw [domNat]; decide
    domainAligned := by rw [domNat]
    codeRange := above _ _ (by simp [WhileMinHeap.place])
    atoms := above _ _ (by simp [WhileMinHeap.place])
    arena := by rw [rf]; decide
    heapDomain := fun l a o placed _ => by
      have member : a ∈ WhileMinHeap.addresses := List.mem_of_getElem? placed
      have := whileMin_addresses_high a member
      rw [domNat]; exact ⟨Or.inr (by dsimp only; simp only [Layout.domainStateBytes]; omega), trivial⟩
    heapPrivate := fun l a o placed object => whileMin_heapPrivate placed object
    belowPrivate := by rw [rf]; decide
    stackAbove := by rw [rf]; simp [WhileMinEntry.high, Layout.stackBytes, WhileMinObservation.observed] }

end OCaml.Vm.Gc
