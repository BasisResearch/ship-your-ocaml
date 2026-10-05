import OCaml.Vm.Sim.WordEquality
import OCaml.Vm.Sim.IsintArithmetic
import OCaml.Bytecode.PtrOffsets

/-!
# Physical equality from placement

Distinct in-range live values have distinct words: integers are odd and the
rest even (`EvenPlace`); a pointer's word lies inside its block, a code
value's inside the code buffer, an atom's inside the atom table; these
regions are pairwise apart (`StackGeometry`), distinct live blocks are
separated (`HeapRepr`), and everything lies below the arena end, so no word
wraps. Hence `WordEquality` for any two roots (`WordEquality.of_place`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm Vsa.Sim Vsa.Machine

/-- Where the word of a placed non-integer value lies. -/
inductive Lies (P : Prog) (s : St) (pl : Place) : Val → Nat → Prop
  | ptr {l k a : Nat} {o : Obj} : Live s.heap (roots P s) l → pl.φ l = some a →
      s.heap.get? l = some o → k < o.wosize → Lies P s pl (.ptr l k) (a + 8 * k)
  | code {pc : Nat} : pc < P.code.size → Lies P s pl (.code pc) (pl.codeBase + 4 * pc)
  | atom {t : Nat} : t < 256 → Lies P s pl (.atom t) (pl.atomBase + 8 * t + 8)

theorem ofNat_inj {A B : Nat} (ha : A < 2 ^ 64) (hb : B < 2 ^ 64)
    (h : BitVec.ofNat 64 A = BitVec.ofNat 64 B) : A = B := by
  have := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- An in-range root that is not an integer lies in its region. -/
theorem Lies.of_root {P : Prog} {s : St} {pl : Place} {v : Val} {x : BitVec 64}
    (root : v ∈ roots P s) (range : v.inRange P.code.size s.heap = true)
    (repr : valWord pl v = some x) (notInt : v.isInt = false) :
    ∃ A, Lies P s pl v A ∧ x = BitVec.ofNat 64 A := by
  cases v with
  | int n => simp [Val.isInt] at notInt
  | raw w => simp [Val.inRange] at range
  | ptr l k =>
    simp only [valWord, Option.map_eq_some_iff] at repr
    obtain ⟨a, placed, rfl⟩ := repr
    simp only [Val.inRange] at range
    split at range
    · rename_i o found
      exact ⟨_, .ptr (.root root rfl) placed found (of_decide_eq_true range), rfl⟩
    · cases range
  | code pc =>
    simp only [valWord, Option.some.injEq] at repr
    exact ⟨_, .code (of_decide_eq_true range), repr.symm⟩
  | atom t =>
    simp only [valWord, Option.some.injEq] at repr
    exact ⟨_, .atom (of_decide_eq_true range), repr.symm⟩

/-- Every region lies below the arena end. -/
theorem Lies.below {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    (g : StackGeometry P s c pl cp high) {v : Val} {A : Nat} (h : Lies P s pl v A) :
    A < DlHeap.heapEnd := by
  cases h with
  | ptr _ placed found bound => have := g.heapArena _ _ _ placed found; omega
  | code bound => have := g.codeArena; omega
  | atom bound => have := g.atomArena; simp only [atomTableBytes] at this; omega

/-- Distinct in-region values have distinct words. -/
theorem Lies.inj {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    (g : StackGeometry P s c pl cp high) (heap : HeapRepr c pl cp P s)
    {v v' : Val} {A B : Nat} (h : Lies P s pl v A) (h' : Lies P s pl v' B) (same : A = B) :
    v = v' := by
  cases h with
  | @ptr l k a o live placed found bound =>
    have low := g.heapLow _ _ _ placed found
    have code := g.heapCode _ _ _ placed found
    have atoms := g.heapAtoms _ _ _ placed found
    simp only [OutWRange] at code atoms
    cases h' with
    | @ptr l' k' a' o' live' placed' found' bound' =>
      by_cases same : l = l'
      · subst same
        rw [placed] at placed'; cases placed'
        congr 1; omega
      · have low' := g.heapLow _ _ _ placed' found'
        rcases heap.2 l l' a a' o o' live live' same placed placed' found found' with sep | sep <;> omega
    | code pc' => have := g.codeArena; omega
    | atom t' => simp only [atomTableBytes] at atoms; omega
  | @code pc bound =>
    cases h' with
    | @ptr l' k' a' o' live' placed' found' bound' =>
      have low := g.heapLow _ _ _ placed' found'
      have code := g.heapCode _ _ _ placed' found'
      simp only [OutWRange] at code; omega
    | code pc' => congr 1; omega
    | atom t' => have := g.codeAtoms; simp only [atomTableBytes] at this; omega
  | @atom t bound =>
    cases h' with
    | @ptr l' k' a' o' live' placed' found' bound' =>
      have low := g.heapLow _ _ _ placed' found'
      have atoms := g.heapAtoms _ _ _ placed' found'
      simp only [OutWRange, atomTableBytes] at atoms; omega
    | code pc' => have := g.codeAtoms; simp only [atomTableBytes] at this; omega
    | atom t' => congr 1; omega

/-- **Physical equality reflects word equality** for two in-range roots. -/
theorem WordEquality.of_place {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (repr : VmReprAt P s c pl cp sp high) (g : StackGeometry P s c pl cp high)
    {a b : Val} (rootA : a ∈ roots P s) (rootB : b ∈ roots P s)
    (rangeA : a.inRange P.code.size s.heap = true) (rangeB : b.inRange P.code.size s.heap = true) :
    WordEquality pl a b := by
  constructor
  intro x y hx hy
  have notRawA := Val.inRange_notRaw rangeA
  have notRawB := Val.inRange_notRaw rangeB
  have phys : physEq? a b = some (a == b) := by
    cases a <;> cases b <;> first | rfl | exact absurd rfl (notRawA _) | exact absurd rfl (notRawB _)
  rw [phys]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · rintro rfl; rw [hx] at hy; exact Option.some.inj hy
  · intro same
    subst same
    have parA := valWord_parity g.even hx notRawA
    have parB := valWord_parity g.even hy notRawB
    cases ia : a.isInt <;> cases ib : b.isInt <;> simp [ia, ib] at parA parB
    · obtain ⟨A, la, ra⟩ := Lies.of_root rootA rangeA hx ia
      obtain ⟨B, lb, rb⟩ := Lies.of_root rootB rangeB hy ib
      exact la.inj g repr.heap lb (ofNat_inj
        (by have := la.below g; simp only [DlHeap.heapEnd] at this; omega)
        (by have := lb.below g; simp only [DlHeap.heapEnd] at this; omega) (ra.symm.trans rb))
    · omega
    · omega
    · cases a with
      | int m =>
        cases b with
        | int n =>
          have := (WordEquality.ints pl m n).reflects x x hx hy
          simp only [physEq?, beq_self_eq_true, Option.some.injEq] at this
          simpa [physEq?] using this
        | _ => simp [Val.isInt] at ib
      | _ => simp [Val.isInt] at ia

end OCaml.Vm.Sim
