import OCaml.Vm.Sim.ReturnRead
import OCaml.Vm.Sim.TrapArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- The caught-exception branch's innermost represented trap frame. -/
structure RaiseFrame (s : St) (dest : Nat) (link : BitVec 63) (env : Val)
    (extra : BitVec 63) (rest : List Val) : Prop where
  active : 0 < s.trap
  bound : s.trap ≤ s.stack.length
  stack : s.stack.drop (s.stack.length - s.trap) = .code dest :: .int link :: env :: .int extra :: rest
  linkBound : link.toNat ≤ s.trap

/-- A complete trap frame fits within the live logical stack. -/
theorem RaiseFrame.count_bound {s : St} {dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    (h : RaiseFrame s dest link env extra rest) : s.stack.length - s.trap + 4 ≤ s.stack.length := by
  have length := congrArg List.length h.stack
  simp only [List.length_drop, List.length_cons] at length
  omega

/-- Unwinding discards the prefix above the trap and all four trap words. -/
theorem RaiseFrame.drop_rest {s : St} {dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    (h : RaiseFrame s dest link env extra rest) : s.stack.drop (s.stack.length - s.trap + 4) = rest := by
  rw [← List.drop_drop, h.stack]
  rfl

/-- The saved frame starts at the domain's absolute trap pointer. -/
theorem RaiseFrame.stack_repr {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    (h : RaiseFrame s dest link env extra rest) (data : VmPayload P s c pl cp sp high) :
    StackRepr c pl (high - 8 * s.trap) high (.code dest :: .int link :: env :: .int extra :: rest) := by
  have address : sp + 8 * (s.stack.length - s.trap) = high - 8 * s.trap := by
    have shape := data.stack.1
    have bound := h.bound
    omega
  have words := stack_drop data.stack (Nat.sub_le s.stack.length s.trap)
  simpa only [address, h.stack] using words

/-- Saved handler observations extracted from represented memory. -/
structure RaiseFrameValues (P : Prog) (s : St) (c : Config) (pl : Place) (base dest : Nat)
    (link : BitVec 63) (env : Val) (extra : BitVec 63) : Prop where
  code : word c base = BitVec.ofNat 64 (pl.codeBase + 4 * dest)
  link : word c (base + 8) = tag64 link
  environment : valWord pl env = some (word c (base + 16))
  extraArgs : word c (base + 24) = tag64 extra
  root : ∀ l, env.loc? = some l → Live s.heap (roots P s) l

/-- Read all four handler words through the common stack representation. -/
theorem RaiseFrame.values {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    (h : RaiseFrame s dest link env extra rest) (data : VmPayload P s c pl cp sp high) :
    RaiseFrameValues P s c pl (high - 8 * s.trap) dest link env extra := by
  have words := h.stack_repr data
  refine ⟨(Option.some.inj (words.2 0 (.code dest) rfl)).symm,
    (Option.some.inj (words.2 1 (.int link) rfl)).symm, words.2 2 env rfl,
    (Option.some.inj (words.2 3 (.int extra) rfl)).symm, ?_⟩
  have selected : s.stack[s.stack.length - s.trap + 2]? = some env := by
    rw [← List.getElem?_drop, h.stack]
    rfl
  exact stack_value_root selected

/-- The represented handler state is the actual raiseTo result. -/
theorem RaiseFrame.state_of_step {P : Prog} {s s' : St} {dest : Nat} {link extra : BitVec 63}
    {env : Val} {rest : List Val} (h : RaiseFrame s dest link env extra rest)
    (step : raiseTo P s s.accu = .next s') :
    {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat} = s' := by
  have active : s.trap ≠ 0 := by have := h.active; omega
  have bound : ¬ s.stack.length < s.trap := Nat.not_lt.mpr h.bound
  have linkBound : ¬ link.toNat > s.trap := Nat.not_lt.mpr h.linkBound
  simp only [raiseTo, active, ite_false, bound, h.stack, linkBound] at step
  exact Res.next.inj (Res.unguard step)

/-- The handler frame's saved extra count is nonnegative (BcSem's `raiseTo` guard). -/
theorem RaiseFrame.saved_of_step {P : Prog} {s s' : St} {dest : Nat} {link extra : BitVec 63}
    {env : Val} {rest : List Val} (h : RaiseFrame s dest link env extra rest)
    (step : raiseTo P s s.accu = .next s') : 0 ≤ extra.toInt := by
  have active : s.trap ≠ 0 := by have := h.active; omega
  have bound : ¬ s.stack.length < s.trap := Nat.not_lt.mpr h.bound
  have linkBound : ¬ link.toNat > s.trap := Nat.not_lt.mpr h.linkBound
  simp only [raiseTo, active, ite_false, bound, h.stack, linkBound] at step
  exact Int.not_lt.mp (Res.guard_ok step)

end OCaml.Vm.Sim
