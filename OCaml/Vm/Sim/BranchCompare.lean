import OCaml.Vm.Sim.ComparisonArithmetic
import OCaml.Vm.Sim.BranchArithmetic
import OCaml.Vm.Sim.Immediate

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives
open LeanRV64DExecutable.Functions

/-- Native arithmetic untagging agrees with the semantic full-width Long_val. -/
theorem longVal_native (n : BitVec 63) :
    shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0) = longVal n := by
  change (tag64 n).sshiftRight 1 = n.signExtend 64
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, tag_toInt, BitVec.toInt_signExtend_of_le (by decide : 63 ≤ 64)]
  rw [Int.shiftRight_eq_div_pow]
  change (2 * n.toInt + 1) / 2 = n.toInt
  omega

/-- Comparison branches use operand 2 as their relative PC base. -/
theorem compare_code_word (pl : Place) {pc dest : Nat} {ofs : Int}
    (targetOk : target pc 1 ofs = some dest) :
    BitVec.ofNat 64 (pl.codeBase + 4 * pc) + ((BitVec.ofInt 64 ofs <<< (2 : Nat)) + 8#64) =
      BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
  have rel := relative_code_word pl targetOk
  have base : BitVec.ofNat 64 (pl.codeBase + 4 * pc) + 8#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 1 + 1)) := by
    simpa only [Nat.add_assoc] using codePc_add pl pc 2
  rw [← base] at rel
  exact (by ac_rfl : _ = (BitVec.ofNat 64 (pl.codeBase + 4 * pc) + 8#64) +
    (BitVec.ofInt 64 ofs <<< (2 : Nat))).trans rel

/-- Successful immediate comparison branches require a represented integer accumulator. -/
theorem brOp_accu {s s' : St} {imm ofs : Int} {f : BitVec 64 → BitVec 64 → Bool}
    (step : brOp s imm ofs f = .next s') : ∃ n, s.accu = .int n := by
  cases ha : s.accu <;> simp [brOp, ha] at step
  exact ⟨_, rfl⟩

/-- A pointer in architectural RAM can pass the native BEQ integer guard.
The current abstract non-integer branch instead treats it as unequal. This
is a word-level witness, not a complete Loaded/run counterexample. -/
theorem beq_pointer_guard_obstruction :
    ((sign_extend (m := 64) (0x40000000#32)) ==
      shift_bits_right_arith (0x80000000#64) (Sail.BitVec.extractLsb (0x01#6) 5 0)) = true ∧
    physEq? (.int (BitVec.ofInt 63 1073741824)) (.ptr 0 0) = some false := by
  decide +kernel

/-- BcSem's side of the discrepancy: on a pointer with an immediate `≥ 2^30`
the native result depends on the address, and the step is outside the model. -/
theorem beq_pointer_unsupported (P : Prog) (s : St) (l k : Nat) :
    stepI P {s with accu := .ptr l k} ⟨.BEQ, [1073741824, 2]⟩ = .unsupported := by
  simp [stepI]

/-- **A high word never matches a small immediate** under the native
`n == Long_val(w)` test: an address in `[2^31, 2^63)` halves to at least
`2^30`, and every immediate below `2^30` (negative ones included) differs. -/
theorem imm_ne_high {x : BitVec 64} {i : Int} (low : 2 ^ 31 ≤ x.toNat) (high : x.toNat < 2 ^ 63)
    (small : i < 2 ^ 30) (wide : -2 ^ 31 ≤ i) :
    ((BitVec.ofInt 64 i) == shift_bits_right_arith x (Sail.BitVec.extractLsb (0x01#6) 5 0)) = false := by
  change ((BitVec.ofInt 64 i) == x.sshiftRight 1) = false
  rw [beq_eq_false_iff_ne]
  intro e
  have t := congrArg BitVec.toInt e
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, BitVec.toInt_ofInt] at t
  have xi : x.toInt = x.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [xi] at t
  rw [Int.bmod_def] at t
  split at t <;> omega

/-- **Placed block and atom words are high**: above `.bss` (hence RAM's base
`0x80000000`) and below the allocator arena's end. -/
theorem StackGeometry.word_high {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : StackGeometry P s c pl cp high) {v : Val} {w : BitVec 64}
    (ranged : v.inRange P.code.size s.heap = true) (pointer : (∃ l k, v = .ptr l k) ∨ ∃ t, v = .atom t)
    (value : valWord pl v = some w) : 2 ^ 31 ≤ w.toNat ∧ w.toNat < 2 ^ 63 := by
  have bss : 2 ^ 31 ≤ Layout.sym_bss_end := by decide
  have arena : Vsa.Sim.DlHeap.heapEnd < 2 ^ 63 := by decide
  rcases pointer with ⟨l, k, rfl⟩ | ⟨t, rfl⟩
  · simp only [Val.inRange] at ranged
    cases got : s.heap.get? l with
    | none => simp [got] at ranged
    | some o =>
      simp only [got, decide_eq_true_eq] at ranged
      simp only [valWord, Option.map_eq_some_iff] at value
      obtain ⟨a, placed, rfl⟩ := value
      have hi := g.heapArena l a o placed got
      have lo := g.heapLow l a o placed got
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · simp only [Val.inRange, decide_eq_true_eq] at ranged
    simp only [valWord, Option.some.injEq] at value
    subst value
    have hi := g.atomArena
    have lo := g.atomLow
    simp only [atomTableBytes] at hi
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The native immediate test on an integer accumulator is its semantic test. -/
theorem imm_test_int {pl : Place} {s : St} {n : BitVec 63} {imm : BitVec 32} {b : Bool}
    (accu : s.accu = .int n) (test : ((BitVec.ofInt 64 imm.toInt) == longVal n) = b) :
    ∀ w, valWord pl s.accu = some w →
      ((BitVec.ofInt 64 imm.toInt) == shift_bits_right_arith w (Sail.BitVec.extractLsb (0x01#6) 5 0)) = b := by
  intro w value
  rw [accu] at value
  cases Option.some.inj value
  rw [longVal_native]
  exact test

/-- The native immediate test on an in-range pointer or atom is "not equal"
for an immediate below `2^30`. -/
theorem imm_test_pointer {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    {imm : BitVec 32} (g : StackGeometry P s c pl cp high)
    (ranged : s.accu.inRange P.code.size s.heap = true)
    (pointer : (∃ l k, s.accu = .ptr l k) ∨ ∃ t, s.accu = .atom t) (small : imm.toInt < 2 ^ 30) :
    ∀ w, valWord pl s.accu = some w →
      ((BitVec.ofInt 64 imm.toInt) == shift_bits_right_arith w (Sail.BitVec.extractLsb (0x01#6) 5 0)) = false := by
  intro w value
  obtain ⟨low, high⟩ := g.word_high ranged pointer value
  exact imm_ne_high low high small (by have := BitVec.le_toInt imm; omega)

/-- BEQ on a pointer or atom: BcSem's guard holds and the branch falls through. -/
theorem beq_pointer_step {P : Prog} {s s' : St} {imm ofs : BitVec 32}
    (pointer : (∃ l k, s.accu = .ptr l k) ∨ ∃ t, s.accu = .atom t)
    (step : stepI P s ⟨.BEQ, [imm.toInt, ofs.toInt]⟩ = .next s') :
    imm.toInt < 2 ^ 30 ∧ s.accu.inRange P.code.size s.heap = true ∧ {s with pc := s.pc + 3} = s' := by
  have shape : stepI P s ⟨.BEQ, [imm.toInt, ofs.toInt]⟩ =
      if 2 ^ 30 ≤ imm.toInt ∨ s.accu.inRange P.code.size s.heap = false then .unsupported
      else .next (s.adv 3) := by
    rcases pointer with ⟨l, k, hv⟩ | ⟨t, hv⟩ <;> simp [stepI, hv]
  rw [shape] at step
  have ok := Res.guard_ok step
  refine ⟨by omega, (by simpa using ok : _ ∧ _).2, Res.next.inj (Res.unguard step)⟩

/-- BNEQ on a pointer or atom: BcSem's guard holds and the branch jumps. -/
theorem bneq_pointer_step {P : Prog} {s s' : St} {imm ofs : BitVec 32}
    (pointer : (∃ l k, s.accu = .ptr l k) ∨ ∃ t, s.accu = .atom t)
    (step : stepI P s ⟨.BNEQ, [imm.toInt, ofs.toInt]⟩ = .next s') :
    imm.toInt < 2 ^ 30 ∧ s.accu.inRange P.code.size s.heap = true ∧
      ∃ dest, target s.pc 1 ofs.toInt = some dest ∧ {s with pc := dest} = s' := by
  have shape : stepI P s ⟨.BNEQ, [imm.toInt, ofs.toInt]⟩ =
      if 2 ^ 30 ≤ imm.toInt ∨ s.accu.inRange P.code.size s.heap = false then .unsupported
      else opt (target s.pc 1 ofs.toInt) fun t => .next { s with pc := t } := by
    rcases pointer with ⟨l, k, hv⟩ | ⟨t, hv⟩ <;> simp [stepI, hv]
  rw [shape] at step
  have ok := Res.guard_ok step
  have body := Res.unguard step
  cases ht : target s.pc 1 ofs.toInt with
  | none => simp [ht, opt] at body
  | some dest =>
    simp only [ht, opt] at body
    exact ⟨by omega, (by simpa using ok : _ ∧ _).2, dest, rfl, Res.next.inj body⟩

end OCaml.Vm.Sim
