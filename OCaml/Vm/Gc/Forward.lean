import OCaml.Vm.Reloc

/-! Forward_tag short-circuiting is not strict relocation. These are checked
obstructions and a candidate lax value relation, not a machine GC proof.
The C branch is `runtime/minor_gc.c:276-283`. Adopting the lax relation also
requires restricting observations: the current ISINT can distinguish it. -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine Reloc

/-- Candidate transparent-Forward interpretation. A production version must
also encode the C short-circuit guard (Lazy/Forward/Double/value-area tests).
Used here only to expose why transparency alone is insufficient. -/
inductive ForwardValue (heap : Heap) (pl : Place) : Val → BitVec 64 → Prop where
  | exact {v w} : valWord pl v = some w → ForwardValue heap pl v w
  | shortcut {l v w} : heap.get? l = some (.block forwardTag [v]) →
      ForwardValue heap pl v w → ForwardValue heap pl (.ptr l 0) w

/-- The immediate payload is allowed by the C short-circuit guard. -/
theorem forwardValue_int (pl : Place) :
    ForwardValue ⟨#[.block forwardTag [.int 42]]⟩ pl (.ptr 0 0) 85 :=
  .shortcut rfl (.exact rfl)

/-- No observation-preserving ISINT rule exists for this lax relation on
all current abstract values. A semantic safety restriction is necessary. -/
theorem forwardValue_not_isInt (pl : Place) :
    ¬ (∀ (h : Heap) (v : Val) (w : BitVec 64), ForwardValue h pl v w →
      v.isInt = (w &&& 1 == 1)) := by
  intro preserves
  have bad := preserves _ _ _ (forwardValue_int pl)
  contradiction

/-- A strict ScanCoherent pointer clause cannot short-circuit a Forward
block to integer 42 when relocated object addresses are aligned/in range.
The machine oldify summary would supply `shortcuts`; allocation supplies
alignment and the address bound. They cannot establish this strict bridge. -/
theorem scanCoherent_forward_int_obstruction {gcAct μ pl visited l a}
    (coherent : ScanCoherent gcAct μ pl visited)
    (hv : visited (.ptr l 0)) (ha : pl.φ l = some a)
    (shortcuts : gcAct (BitVec.ofNat 64 a) = 85)
    (aligned : μ a % 8 = 0) (bounded : μ a < 2^64) : False := by
  have eq := coherent.ptr l 0 a hv ha
  simp only [Nat.mul_zero, Nat.add_zero] at eq
  rw [shortcuts] at eq
  have hn := congrArg BitVec.toNat eq
  change 85 = μ a % 2^64 at hn
  rw [Nat.mod_eq_of_lt bounded] at hn
  omega

/-- Strict ObjAt cannot describe a Forward block at the immediate payload
address in a memory whose preceding word is zero. -/
theorem forward_objAt_obstruction {c : Config} {pl cp}
    (unmapped : word c 77 = 0) :
    ¬ ObjAt c pl cp 85 (.block forwardTag [.int 42]) := by
  intro h
  have hh := h.1.1
  change (word c 77).toNat % 256 = 250 at hh
  rw [unmapped] at hh
  contradiction

end OCaml.Vm.Gc
