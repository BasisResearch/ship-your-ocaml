import OCaml.Vm.Sim.ClosurePrefixInput
import OCaml.Vm.Sim.BranchArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode LeanRV64DExecutable.Functions

/-- Consuming captures undoes the temporary push and drops the old stack prefix. -/
theorem closure_capture_end (sp count : Nat) (room : 0 < count → 8 ≤ sp) :
    BitVec.ofNat 64 (closureSource sp count) +
      Sail.shift_bits_left (BitVec.ofNat 64 count) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (sp + 8 * (count - 1)) := by
  change BitVec.ofNat 64 (closureSource sp count) + (BitVec.ofNat 64 count <<< (3 : Nat)) = _
  rw [nat_shift_word, ← BitVec.ofNat_add]
  congr 1
  by_cases positive : 0 < count
  · simp only [closureSource, positive, ite_true]
    have enough := room positive
    omega
  · simp only [closureSource, positive, ite_false]
    omega

/-- The closure offset is relative to its second operand, exactly as in interp.c. -/
theorem closure_code_address (pl : Place) {pc dest : Nat} {ofs : BitVec 32}
    (jump : target pc 1 ofs.toInt = some dest) :
    BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 2)) +
      Sail.shift_bits_left (sign_extend (m := 64) ofs) (Sail.BitVec.extractLsb (0x02#6) 5 0) =
      BitVec.ofNat 64 (pl.codeBase + 4 * dest) :=
  relative_code_word pl jump

theorem closure_capture_stack (s : St) (count : Nat) :
    (if 0 < count then s.accu :: s.stack else s.stack).take count = closureCaptures s count := by
  cases count with
  | zero => simp [closureCaptures]
  | succ n => simp [closureCaptures]

theorem closure_stack_remaining (s : St) (count : Nat) :
    (if 0 < count then s.accu :: s.stack else s.stack).drop count = s.stack.drop (count - 1) := by
  cases count with
  | zero => simp
  | succ n => simp

/-- A successful bytecode closure step selects exactly the represented capture state. -/
theorem closure_state_of_step {P : Prog} {s s' : St} {nv ofs : Int} {dest : Nat}
    (bound : nv.toNat - 1 ≤ s.stack.length) (jump : target s.pc 1 ofs = some dest)
    (step : stepI P s ⟨.CLOSURE, [nv, ofs]⟩ = .next s') :
    closureState s nv.toNat dest = s' := by
  have enough : ¬ (if 0 < nv.toNat then s.accu :: s.stack else s.stack).length < nv.toNat := by
    split
    · simp only [List.length_cons]; omega
    · omega
  simpa only [stepI, enough, ite_false, jump, opt, closure_capture_stack, closure_stack_remaining,
    closureState, closureObject, St.adv, List.cons_append, List.nil_append, Res.next.injEq] using step

end OCaml.Vm.Sim
