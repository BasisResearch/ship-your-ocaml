import OCaml.Vm.Sim.Immediate

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine
open LeanRV64DExecutable.Functions

/-- Signed displacement within an existing represented closure allocation.
The semantic nonnegative result supplies `target`; no new heap object is introduced. -/
structure ClosureOffset (s : St) (pl : Place) (ofs : Int) (l a k dest : Nat) : Prop where
  env : s.env = .ptr l k
  placed : pl.φ l = some a
  target : (dest : Int) = k + ofs

/-- Mapping an abstract signed field offset into modular native pointer arithmetic. -/
theorem pointer_offset_word (a k dest : Nat) (ofs : Int)
    (target : (dest : Int) = k + ofs) :
    BitVec.ofNat 64 (a + 8 * k) + BitVec.ofInt 64 (8 * ofs) =
      BitVec.ofNat 64 (a + 8 * dest) := by
  change BitVec.ofInt 64 (↑(a + 8 * k)) + BitVec.ofInt 64 (8 * ofs) =
    BitVec.ofInt 64 (↑(a + 8 * dest))
  rw [← BitVec.ofInt_add]
  apply congrArg (BitVec.ofInt 64)
  omega

/-- The exact signed scaling used by the variable closure-offset arm. -/
theorem signed_index_word (w : BitVec 32) :
    Sail.shift_bits_left (sign_extend (m := 64) w) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofInt 64 (8 * w.toInt) := by
  change (BitVec.ofInt 64 w.toInt <<< (3 : Nat)) = _
  rw [BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 3 = BitVec.ofInt 64 8 from by decide,
    ← BitVec.ofInt_mul, Int.mul_comm]

/-- Offsetting a pointer preserves its represented location identity. -/
theorem ClosureOffset.root {P : Prog} {s : St} {pl : Place} {ofs : Int} {l a k dest : Nat}
    (h : ClosureOffset s pl ofs l a k dest) :
    ∀ l', (Val.ptr l dest).loc? = some l' → Live s.heap (roots P s) l' := by
  intro l' loc
  have eq : l = l' := Option.some.inj loc
  subst l'
  exact Live.root (v := s.env) (by simp [roots]) (by simp [h.env, Val.loc?])

theorem ClosureOffset.sourceWord {s : St} {pl : Place} {ofs : Int} {l a k dest : Nat}
    (h : ClosureOffset s pl ofs l a k dest) :
    valWord pl s.env = some (BitVec.ofNat 64 (a + 8 * k)) := by
  simp only [h.env, valWord, h.placed, Option.map_some]

theorem ClosureOffset.resultWord {s : St} {pl : Place} {ofs : Int} {l a k dest : Nat}
    (h : ClosureOffset s pl ofs l a k dest) :
    valWord pl (.ptr l dest) = some (BitVec.ofNat 64 (a + 8 * dest)) := by
  simp only [valWord, h.placed, Option.map_some]

end OCaml.Vm.Sim
