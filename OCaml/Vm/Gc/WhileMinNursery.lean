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
    primitives := fun i name _ => above _ _ (by rw [prims]; simp; omega)
    top := by rw [rf]; decide
    aligned := by rw [rf]; decide
    domainLow := by rw [domNat]; decide
    domainHigh := by rw [domNat]; decide
    domainAligned := by rw [domNat]
    codeRange := above _ _ (by simp [WhileMinHeap.place])
    atoms := above _ _ (by simp [WhileMinHeap.place])
    arena := by rw [rf]; decide }

end OCaml.Vm.Gc
