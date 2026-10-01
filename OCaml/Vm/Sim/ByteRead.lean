import OCaml.Vm.Sim.FieldRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- A successful string-byte selection and placement, independent of register
assignment and of the memory geometry required by the native load. -/
structure ByteSelection (heap : Heap) (pl : Place) (source : Val) (i : Nat)
    (b : UInt8) (l a : Nat) (bs : List UInt8) : Prop where
  pointer : source = .ptr l 0
  placed : pl.φ l = some a
  object : heap.get? l = some (.bytes bs)
  selected : bs[i]? = some b

theorem ByteSelection.sourceWord {heap : Heap} {pl : Place} {source : Val}
    {i l a : Nat} {b : UInt8} {bs : List UInt8}
    (h : ByteSelection heap pl source i b l a bs) :
    valWord pl source = some (BitVec.ofNat 64 a) := by
  simp only [h.pointer, valWord, h.placed, Option.map_some, Nat.mul_zero, Nat.add_zero]

/-- Resolve the total byte observation from the represented live bytes object. -/
theorem ByteSelection.read {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i l a : Nat} {source : Val} {b : UInt8} {bs : List UInt8}
    (h : VmReprAt P s c pl cp sp high) (member : source ∈ roots P s)
    (f : ByteSelection s.heap pl source i b l a bs) :
    byte c (a + i) = BitVec.ofNat 8 b.toNat := by
  have live : Live s.heap (roots P s) l := Live.root member (by simp [f.pointer, Val.loc?])
  have object := (payload_of_repr h).object_at live f.placed f.object
  exact object.2.1 i b f.selected

end OCaml.Vm.Sim
