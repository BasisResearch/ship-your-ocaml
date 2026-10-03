import OCaml.Vm.Sim.StackPayload
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A checked store immediately below sp adds one represented stack word. -/
theorem stack_push {c : Config} {pl : Place} {sp high : Nat} {stk : List Val} {v : Val}
    (h : StackRepr c pl sp high stk) (room : 8 ≤ sp)
    (value : valWord pl v = some (word c (sp - 8))) :
    StackRepr c pl (sp - 8) high (v :: stk) := by
  constructor
  · simp only [List.length_cons]
    have shape := h.1
    omega
  · intro i x hx
    cases i with
    | zero =>
      have eq : v = x := Option.some.inj hx
      subst x
      simpa only [Nat.mul_zero, Nat.add_zero] using value
    | succ i =>
      have addr : sp - 8 + 8 * (i + 1) = sp + 8 * i := by omega
      simpa only [addr] using h.2 i x hx

/-- PUSH duplicates an existing root; the remaining memory payload is unchanged. -/
theorem payload_stack_push {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (room : 8 ≤ sp)
    (value : valWord pl s.accu = some (word c (sp - 8))) :
    VmPayload P {s with stack := s.accu :: s.stack} c pl cp (sp - 8) high := by
  apply payload_stack_of_root h ?_ (stack_push h.stack room value)
  intro v hv l hl
  apply Live.root ?_ hl
  rcases List.mem_cons.mp hv with rfl | hv
  · simp [roots]
  · simp [roots, hv]

/-- Duplicating the accumulator on the stack preserves every previously live root. -/
theorem live_stack_push {P : Prog} {s : St} {l : Nat}
    (h : Live s.heap (roots P s) l) :
    Live s.heap (roots P {s with stack := s.accu :: s.stack}) l := by
  apply live_of_roots h
  intro v loc hv hl
  apply Live.root ?_ hl
  simpa only [roots, List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm,
    or_self, or_self_left] using hv

/-- Signed native stack decrements share one non-wrapping address identity. -/
theorem stack_decrement {sp n : Nat} {offset : BitVec 12}
    (room : n ≤ sp) (small : n < 2^64)
    (encoded : LeanRV64DExecutable.Functions.sign_extend (m := 64) offset =
      -BitVec.ofNat 64 n) :
    BitVec.ofNat 64 sp + LeanRV64DExecutable.Functions.sign_extend (m := 64) offset =
      BitVec.ofNat 64 (sp - n) := by
  rw [encoded, ← BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le sp n small room

/-- The native decrement agrees with natural stack arithmetic when space exists. -/
theorem push_address {sp : Nat} (room : 8 ≤ sp)
    :
    BitVec.ofNat 64 sp + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 (sp - 8) :=
  stack_decrement room (by decide) (by decide)

end OCaml.Vm.Sim
