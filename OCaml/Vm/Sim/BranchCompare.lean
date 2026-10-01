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

end OCaml.Vm.Sim
