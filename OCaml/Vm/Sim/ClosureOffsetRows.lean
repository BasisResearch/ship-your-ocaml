import OCaml.Vm.Sim.ClosureOffset
import OCaml.Vm.Sim.StackRows
import OCaml.Vm.Sim.StackRows

/-!
# Shared loop-head simulations of OFFSETCLOSURE / PUSHOFFSETCLOSURE

`ClosureOffset` is derived from the step: the environment pointer, its
placement (from the represented environment register) and the in-block
target (`k + d ≥ 0`, checked by the semantics).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The semantic closure-offset step yields the `ClosureOffset` observation. -/
theorem closure_offset_of_step {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {d : Int} {s1 s' : St} {width : Nat} (repr : VmReprAt P s c pl cp sp high)
    (step : (match s.env with
      | .ptr l k => if (k : Int) + d < 0 then Res.wrong else
          .next { (s1.adv width) with accu := .ptr l ((k : Int) + d).toNat }
      | _ => .wrong) = .next s') :
    ∃ l a k dest, ClosureOffset s pl d l a k dest ∧
      s' = { (s1.adv width) with accu := .ptr l dest } := by
  cases henv : s.env with
  | ptr l k =>
    rw [henv] at step
    by_cases neg : (k : Int) + d < 0
    · simp only [neg, ↓reduceIte, reduceCtorEq] at step
    · simp only [neg, ↓reduceIte, Res.next.injEq] at step
      subst step
      obtain ⟨w, -, value⟩ := repr.env
      rw [henv] at value
      simp only [valWord] at value
      cases placed : pl.φ l with
      | none => rw [placed] at value; cases value
      | some a => exact ⟨l, a, k, ((k : Int) + d).toNat, ⟨henv, placed, by omega⟩, rfl⟩
  | _ => rw [henv] at step; cases step

/-- Shared simulation of a non-pushing closure offset from the loop head. -/
theorem closure_offset_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {op : Opcode} {d : Int} {width : Nat}
    (arm : ∀ pl cp sp high l a k dest, ArmInput L P s op c pl cp sp high →
      ClosureOffset s pl d l a k dest →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P { (s.adv width) with accu := .ptr l dest } c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (step : (match s.env with
      | .ptr l k => if (k : Int) + d < 0 then Res.wrong else
          .next { (s.adv width) with accu := .ptr l ((k : Int) + d).toNat }
      | _ => .wrong) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, dest, sel, rfl⟩ := closure_offset_of_step input.toVmReprAt step
  obtain ⟨c', run, running⟩ := arm pl cp sp high l a k dest input sel
  exact ⟨c', run, h.of_plus run running⟩

/-- Shared simulation of a pushing closure offset from the loop head. -/
theorem push_closure_offset_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {op : Opcode} {d : Int} {width high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (arm : ∀ pl cp sp high l a k dest w, WindowStable L.runtimeOk [⟨sp - 8, sp⟩] →
      ArmInput L P s op c pl cp sp high → PushWriteOk P s c pl cp sp w →
      ClosureOffset s pl d l a k dest → valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P
        { ((pushAccu s).adv width) with accu := .ptr l dest } c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : (match s.env with
      | .ptr l k => if (k : Int) + d < 0 then Res.wrong else
          .next { ((pushAccu s).adv width) with accu := .ptr l ((k : Int) + d).toNat }
      | _ => .wrong) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨w, -, pushed⟩ := input.accu
  obtain ⟨l, a, k, dest, sel, rfl⟩ := closure_offset_of_step input.toVmReprAt step
  obtain ⟨c', run, running⟩ := arm pl cp sp high l a k dest w
    (by simpa only [Nat.mul_one] using rf.push input space) input
    (PushWriteOk.of_geometry input.geometry input.stack space) sel pushed
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
