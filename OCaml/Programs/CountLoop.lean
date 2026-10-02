import OCaml.Logic.Symbolic

/-!
# A counting loop, specified for any bound (model for `OCaml/Logic/Symbolic.lean`)

`while i < N do i := i + 1 done; accu := i` on the stack top: from any state
with `i ≤ N` on the stack top, the program reaches `STOP` with `accu = N`.
The proof has one symbolic body run, one symbolic exit run and
`loop_rule`; nothing is enumerated. (The round-1 held-out case H9 is
`loopN_reaches 10`.)
-/

namespace OCaml.Programs.CountLoop

open OCaml.Bytecode

/-- Encode instructions as code words (opcode, then operands). -/
def enc (is : List (Opcode × List Int)) : Code :=
  (is.flatMap fun (o, args) => BitVec.ofNat 32 o.toNat :: args.map (BitVec.ofInt 32)).toArray

/-- The counting loop of `H9` with bound `N` (`BLEINT N`). -/
def loopN (N : Nat) : Prog :=
  ⟨enc [(.ACC0, []), (.BLEINT, [(N : Int), 8]), (.ACC0, []), (.OFFSETINT, [1]), (.ASSIGN, [0]),
        (.BRANCH, [-10]), (.ACC0, []), (.STOP, [])],
   #[], ⟨#[]⟩, .atom 0, [], .atom 0, [], []⟩

/-- A code operand read back (`Code.arg` of `BitVec.ofInt 32 N`). -/
theorem arg_natCast (N : Nat) (hN : N < 2^31) : (BitVec.ofInt 32 (N : Int)).toInt = N := by
  rw [BitVec.ofInt_natCast, BitVec.toInt_eq_toNat_cond]
  simp; split <;> omega

/-- The `BLEINT N` test on counter `i`, normalised. -/
theorem bleint_loop (N i : Nat) (hN : N < 2^31) (hi : i < 2^62) :
    (BitVec.ofInt 64 (BitVec.ofInt 32 (N : Int)).toInt).sle (longVal (BitVec.ofNat 63 i)) = decide (N ≤ i) := by
  rw [arg_natCast N hN, sle_ofNat i N hi (by omega)]

/-- The loop body: one symbolic run `pc 0 → pc 0`, `i ↦ i + 1`. -/
theorem loopN_body (N : Nat) (hN : N < 2^31) (i : Nat) (hi : i < N) (a e : Val) (x t : Nat) (h : Heap)
    (w : World) (rest : List Val) :
    Run.iter (bcK (loopN N)) 6 ⟨0, a, .int (BitVec.ofNat 63 i) :: rest, e, x, t, h, w⟩ =
      .ok ⟨0, .unit, .int (BitVec.ofNat 63 (i + 1)) :: rest, e, x, t, h, w⟩ := by
  have hb := bleint_loop N i hN (by omega)
  rw [sym_step rfl, sym_step (step_br_fall (n := (BitVec.ofInt 32 (N : Int)).toInt) (o := 8) (f := fun a b => a.sle b)
    (a := BitVec.ofNat 63 i) rfl rfl (by rw [hb]; simp; omega)), ← offsetInt_ofNat i (by omega)]
  rfl

/-- The loop exit: `i = N` branches to `11`, `ACC0`, stops at `12`. -/
theorem loopN_exit (N : Nat) (hN : N < 2^31) (a e : Val) (x t : Nat) (h : Heap) (w : World) (rest : List Val) :
    Run.iter (bcK (loopN N)) 3 ⟨0, a, .int (BitVec.ofNat 63 N) :: rest, e, x, t, h, w⟩ =
      .ok ⟨12, .int (BitVec.ofNat 63 N), .int (BitVec.ofNat 63 N) :: rest, e, x, t, h, w⟩ := by
  have hb := bleint_loop N N hN (by omega)
  rw [sym_step rfl, sym_step (step_br_taken (n := (BitVec.ofInt 32 (N : Int)).toInt) (o := 8) (f := fun a b => a.sle b)
    (a := BitVec.ofNat 63 N) (t := 11) rfl rfl (by rw [hb]; simp) rfl)]
  rfl

/-- The counting loop for any bound `N < 2^31`: `loop_rule` on the section
"`pc = 0`, counter `i ≤ N` on the stack top", rank `N - i`. -/
theorem loopN_reaches (N : Nat) (hN : N < 2^31) :
    ∀ (n : Nat) (rest : List Val) (s : St), n ≤ N → s.pc = 0 → s.stack = .int (BitVec.ofNat 63 n) :: rest →
      ∃ k s', StepsN (loopN N) k s s' ∧ s'.pc = 12 ∧ s'.accu = .int (BitVec.ofNat 63 N) := by
  intro n rest s hn hpc hstk
  have := loop_rule (P := loopN N)
    (fun s => s.pc = 0 ∧ ∃ i, i ≤ N ∧ s.stack = .int (BitVec.ofNat 63 i) :: rest)
    (fun s => s.pc = 12 ∧ s.accu = .int (BitVec.ofNat 63 N)) (fun s => N - headNat s) (fun s => headNat s = N)
    (by
      rintro ⟨pc, a, stk, e, x, t, h, w⟩ ⟨hpc, i, hi, hs⟩ hne
      cases hpc; cases hs
      simp only [headNat, BitVec.toNat_ofNat] at hne
      refine ⟨6, _, loopN_body N hN i (by omega) a e x t h w rest, ⟨rfl, i + 1, by omega, rfl⟩, ?_⟩
      simp only [headNat, BitVec.toNat_ofNat]; omega)
    (by
      rintro ⟨pc, a, stk, e, x, t, h, w⟩ ⟨hpc, i, hi, hs⟩ hex
      cases hpc; cases hs
      simp only [headNat, BitVec.toNat_ofNat] at hex
      obtain rfl : i = N := by omega
      exact ⟨3, _, loopN_exit i hN a e x t h w rest, rfl, rfl⟩)
    s ⟨hpc, n, hn, hstk⟩
  obtain ⟨k, s', hr, hp⟩ := this
  exact ⟨k, s', sym_sound hr, hp⟩

end OCaml.Programs.CountLoop
