import OCaml.Vm.Boot.Startup.EqualPrefixFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Vm.Primitives

/-- The character bytes of a nonempty name agree with the beginning of a
name-and-suffix environment string. Both facts are ordinary CStr representations. -/
theorem equalPrefix_of_cstr {p q : BitVec 64} {cs suffix : List Char} {c : Config}
    (left : CStr c.σ.mem p.toNat (cs ++ suffix)) (right : CStr c.σ.mem q.toNat cs)
    (positive : 0 < cs.length) (leftWindow : ReadWindow p cs.length) (rightWindow : ReadWindow q cs.length) :
    EqualPrefix p q (cs.length - 1) (fun k => BitVec.ofNat 8 (byteVal cs k)) c := by
  have extent : cs.length - 1 + 1 = cs.length := by omega
  have value {k : Nat} (less : k < cs.length) : byteVal (cs ++ suffix) k = byteVal cs k := by
    unfold byteVal
    rw [List.getElem?_append_left less]
  constructor
  · simpa only [extent] using leftWindow
  · simpa only [extent] using rightWindow
  · intro k bound
    have less : k < cs.length := by omega
    obtain ⟨b, pin, _, byte⟩ := cstr_byte_val _ _ _ left k (by simp only [List.length_append]; omega)
    rw [value less] at byte
    rw [pin, Option.getD_some, ← byte]
    exact (BitVec.ofNat_toNat 8 b).symm
  · intro k bound
    obtain ⟨b, pin, _, byte⟩ := cstr_byte_val _ _ _ right k (by omega)
    rw [pin, Option.getD_some, ← byte]
    exact (BitVec.ofNat_toNat 8 b).symm
  · intro k bound eq
    obtain ⟨b, _, zero, byte⟩ := cstr_byte_val _ _ _ right k (by omega)
    rw [← byte, BitVec.ofNat_toNat] at eq
    have := zero.mp eq
    omega
end OCaml.Vm.Boot.Startup
