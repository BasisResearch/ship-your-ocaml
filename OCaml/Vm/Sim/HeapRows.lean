import OCaml.Vm.Sim.ImmediateRows
import OCaml.Vm.Sim.AccRows
import OCaml.Vm.Sim.Offsetref

/-!
# Unconditional rows: in-place heap updates

OFFSETREF adds to an integer field of the accumulator's block. The
semantic inversion and the represented field (block, placement, selected
integer, room above `.bss`) come from the step and the loop-head witness.
The field write's framing is the named `FieldWriteReady`: the geometry does
not yet separate placed blocks from the `Caml_state` record, channel buffers
and the primitive table, and `RuntimeFrame` has no heap windows (owner:
a1-arms' invariant).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **Field-write readiness** (named obligation, a1-arms' invariant): one-word
writes to a field of a placed block are runtime-stable and miss the rest of
the represented payload. -/
structure FieldWriteReady (L : OCaml.Layout) (P : Prog) (s : St) (c : Config) : Prop where
  ready : ∀ (pl : Place) (cp : ChanPlace) (sp high l a k tag : Nat) (fields : List Val)
    (w : BitVec 64), VmReprAt P s c pl cp sp high → StackGeometry P s c pl cp high →
    pl.φ l = some a → s.heap.get? l = some (.block tag fields) → k < fields.length →
    WindowStable L.runtimeOk [⟨a + 8 * k, a + 8 * k + 8⟩] ∧ FieldWriteOk P s c pl cp sp a k w

/-- A selected field 0 of a value: the value is a pointer into a block. -/
theorem field_zero {h : Heap} {v x : Val} (sel : field? h v 0 = some x) :
    ∃ l k tag fields, v = .ptr l k ∧ h.get? l = some (.block tag fields) ∧ fields[k]? = some x := by
  cases v with
  | ptr l k =>
    simp only [field?] at sel
    split at sel
    · rename_i tag fields found
      exact ⟨l, k, tag, fields, rfl, found, by simpa using sel⟩
    · cases sel
  | int | code | atom | raw => simp [field?] at sel

/-- **OFFSETREF from the loop head.** -/
theorem offsetref_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .OFFSETREF)
    (fetch : P.code[s.pc + 1]? = some w) (field : FieldWriteReady L P s c)
    (step : stepI P s ⟨.OFFSETREF, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, sel, rest⟩ := opt_next step
  obtain ⟨l, k, tag, fields, pointer, object, selected⟩ := field_zero sel
  cases v with
  | int n =>
    obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
    obtain ⟨x, -, word⟩ := input.accu
    rw [pointer] at word
    simp only [valWord, Option.map_eq_some_iff] at word
    obtain ⟨a, placed, -⟩ := word
    have low := input.geometry.heapLow l a _ placed object
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    obtain ⟨stable, space⟩ := field.ready pl cp sp high l a k tag fields
      (tag64 n + offsetintOperand w) input.toVmReprAt input.geometry placed object bound
    obtain ⟨c', run, running⟩ := offsetref_step_arm stable input
      (OperandAt.of_fetch input.geometry fetch) pointer placed object selected (by omega) space step
    exact ⟨c', run, h.of_plus run running⟩
  | ptr | code | atom | raw => cases rest

end OCaml.Vm.Sim
