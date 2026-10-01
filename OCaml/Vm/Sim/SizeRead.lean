import OCaml.Vm.Sim.ImmediateArithmetic
import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Primitives.ScanArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- A semantic size and the header word used by VECTLENGTH. Ordinary allocation
bases supply this from ObjAt. Atoms and infix pointers need their own header
invariant; no machine execution is assumed by this observation. -/
structure SizeSelection (s : St) (pl : Place) (c : Config) (a n : Nat) : Prop where
  word : valWord pl s.accu = some (BitVec.ofNat 64 a)
  size : size? s.heap s.accu = some n
  header : (OCaml.Vm.word c (a - 8)).toNat / 1024 = n

/-- At an ordinary allocation base, the represented object provides its size. -/
theorem SizeSelection.of_object {P : Prog} {s : St} {pl : Place} {c : Config} {cp : ChanPlace}
    {sp high l a : Nat} {o : Obj} (h : VmReprAt P s c pl cp sp high)
    (accu : s.accu = .ptr l 0) (placed : pl.φ l = some a) (object : s.heap.get? l = some o) :
    SizeSelection s pl c a o.wosize := by
  have live : Live s.heap (roots P s) l :=
    Live.root (v := s.accu) (by simp [roots]) (by simp [accu, Val.loc?])
  have represented := (payload_of_repr h).object_at live placed object
  refine ⟨?_, ?_, represented.1.2⟩
  · simp [accu, valWord, placed]
  · simp [size?, accu, object]

/-- Header decoding followed by tagging gives the represented payload size. -/
theorem header_size_tag (header : BitVec 64) (n : Nat)
    (size : header.toNat / 1024 = n) :
    ((header >>> (10 : Nat)) <<< (1 : Nat)) + 1#64 = tag64 (BitVec.ofNat 63 n) := by
  rw [header_words header n size]
  apply BitVec.eq_of_toNat_eq
  rw [tag_toNat]
  have bound := header.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Sim
