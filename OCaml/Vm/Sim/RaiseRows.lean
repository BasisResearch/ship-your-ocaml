import OCaml.Vm.Sim.RaiseQuiet
import OCaml.Vm.Sim.RaiseNotraceQuiet
import OCaml.Vm.Sim.ReraiseQuiet
import OCaml.Vm.Sim.TrapRows
import OCaml.Vm.Sim.ControlRows
import OCaml.Vm.Gc.NurseryGeometry
import OCaml.Bytecode.ExtraBound

/-!
# F1 table rows for the caught raise family (RAISE, RERAISE, RAISE_NOTRACE)

Every premise of the quiet caught-raise arms comes from the loop head:
* the trap frame from the step itself (`RaiseFrame.of_step`);
* the trap barrier and backtrace flag from the runtime frame
  (`RuntimeFrame.barrier`/`backtrace`), with domain reads from the nursery
  geometry;
* the root invocation's saved slots from `NativeValid.rootSaved`;
* the saved extra count from `ExtraBounded.trapSaved`;
* the trap-pointer store from `TrapWriteOk.of_geometry`.

An uncaught raise leaves the interpreter (no loop head follows), so the rows
take the named premise `RaisesCaught P`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The raising opcodes. -/
def raiseOps : List Opcode := [.RAISE, .RERAISE, .RAISE_NOTRACE]

/-- **Every reachable raise is caught** (named per-program obligation: an
uncaught exception ends the program outside the interpreter loop). -/
structure RaisesCaught (P : Prog) : Prop where
  caught : ∀ s op, Reach P s → op ∈ raiseOps → DispatchCode P s op → s.trap ≠ 0

/-- A continuing caught raise selects a complete trap frame. -/
theorem RaiseFrame.of_step {P : Prog} {s s' : St} (step : raiseTo P s s.accu = .next s')
    (caught : s.trap ≠ 0) : ∃ dest link env extra rest, RaiseFrame s dest link env extra rest := by
  unfold raiseTo at step
  simp only [caught, ite_false] at step
  split at step
  · cases step
  · rename_i bound
    split at step
    · rename_i dest link env ex rest frame
      split at step
      · cases step
      · rename_i linkOk
        exact ⟨dest, link, env, ex, rest, ⟨by omega, by omega, frame, by omega⟩⟩
    · cases step

/-- An aligned `Caml_state` word is readable RAM. -/
theorem ArmGeometry.domain_read {P s c pl cp high} (g : ArmGeometry P s c pl cp high) {off : Nat}
    (fits : off + 8 ≤ Layout.domainStateBytes := by decide) (aligned : off % 8 = 0 := by decide) :
    RamReadAt ((word c Layout.sym_Caml_state).toNat + off) 8 :=
  (g.nursery.domain_write fits aligned).read

/-- The quiet-raise readiness at a loop head. -/
theorem RaiseQuietReady.of_frame {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (h : ArmInput L P s op c pl cp sp high) : RaiseQuietReady high c := by
  have same : high = high0 := h.stackHigh.symm.trans (rf.stackHigh c h.runtime)
  subst same
  exact ⟨rf.barrier c h.runtime, rf.backtrace c h.runtime, h.geometry.domain_read,
    h.geometry.domain_read, h.geometry.domain_read, h.geometry.domain_read⟩

/-- The root invocation's saved `stack_high`/`extern_sp` slots, at a loop head. -/
theorem NativePlaced.raise {c : Config} (n : NativePlaced c) : ∃ nativeSp, RaiseStackFrame nativeSp c := by
  obtain ⟨D, inv, valid⟩ := n
  have low := valid.low
  have high := valid.high
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top, Layout.interpFrameBytes,
    Layout.camlMainFrameBytes] at low high
  have ht : Layout.sym_tohost + 8 ≤ 0x80283000 := by decide
  exact ⟨D.nativeSp, inv.stack, valid.rootSaved c inv, ⟨by omega, by omega, Or.inr (by omega)⟩,
    ⟨by omega, by omega, Or.inr (by omega)⟩⟩

/-- Shared simulation of a caught raise from the loop head, given the
generated quiet step arm of the opcode. -/
theorem raise_family_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {high0 dom0 : Nat} (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (arm : ∀ pl cp sp high dest nativeSp link env extra rest, ArmInput L P s op c pl cp sp high →
      RaiseFrame s dest link env extra rest → RaiseQuietReady high c → MemoryStable L.runtimeOk →
      RaiseStackFrame nativeSp c → 0 ≤ extra.toInt →
      WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
        (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩] →
      RaiseFrameReads (high - 8 * s.trap) → TrapWriteOk P s c pl cp sp high (s.trap - link.toNat) →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (trapSaved : ∀ n dest link env (ex : BitVec 63) rest,
      s.stack.drop n = .code dest :: .int link :: env :: .int ex :: rest → 0 ≤ ex.toInt)
    (caught : s.trap ≠ 0) (step : raiseTo P s s.accu = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨dest, link, env, extra, rest, frame⟩ := RaiseFrame.of_step step caught
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨nativeSp, saved⟩ := input.native.raise
  have dom := rf.domainWord c input.runtime
  have hs := input.stack.1
  have bound := frame.count_bound
  have trapBound := frame.bound
  have rd : ∀ j, j < 4 → RamReadAt (high - 8 * s.trap + 8 * j) 8 := fun j hj => by
    have r := input.geometry.read input.stack (stack_space input.stack space)
      (i := s.stack.length - s.trap + j) (by omega)
    have e : sp + 8 * (s.stack.length - s.trap + j) = high - 8 * s.trap + 8 * j := by omega
    rwa [e] at r
  obtain ⟨c', run, running⟩ := arm pl cp sp high dest nativeSp link env extra rest input frame
    (.of_frame rf input) stable saved (trapSaved _ _ _ _ _ _ frame.stack)
    (rf.windows _ fun w hw => by
      simp only [List.mem_singleton] at hw
      subst hw
      rw [dom]
      exact Or.inr ⟨Layout.off_trapsp, by simp [vmDomainOffsets], rfl⟩)
    ⟨by simpa using rd 0 (by decide), rd 1 (by decide), rd 2 (by decide), rd 3 (by decide)⟩
    (TrapWriteOk.of_geometry input.geometry input.stack space)
  exact ⟨c', run, h.of_plus run running⟩

/-- A raise never halts the bytecode machine. -/
theorem raiseTo_not_halt {P : Prog} {s : St} {v : Val} {e : Nat} {w : World} :
    raiseTo P s v ≠ .halt e w := by
  intro step
  unfold raiseTo at step
  by_cases t : s.trap = 0
  · simp only [t, ite_true] at step; cases step
  · simp only [t, ite_false] at step
    by_cases b : s.stack.length < s.trap
    · simp only [b, ite_true] at step; cases step
    · simp only [b, ite_false] at step
      split at step
      · split at step <;> cases step
      · cases step

/-- The three raise rows share one adapter. -/
theorem raise_row_of {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {op : Opcode}
    (member : op ∈ raiseOps) (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (extraBounded : ExtraBounded P) (raises : RaisesCaught P)
    (semantics : ∀ s, stepI P s ⟨op, []⟩ = raiseTo P s s.accu)
    (shape : ∀ s args, args ≠ [] → stepI P s ⟨op, args⟩ = .unsupported)
    (next : ∀ s s' c, Reach P s → OCaml.LoopAt L P s c → DispatchCode P s op →
      8 * s.stack.length ≤ Layout.stackBytes →
      (∀ n dest link env (ex : BitVec 63) rest,
        s.stack.drop n = .code dest :: .int link :: env :: .int ex :: rest → 0 ≤ ex.toInt) →
      s.trap ≠ 0 → raiseTo P s s.accu = .next s' → ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c') :
    OCaml.OpArm P (OCaml.LoopAt L P) op :=
  opArm_of_next0 (fun s s' c reach _ h code step =>
      next s s' c reach h code (by simpa using stack_fits fits capacity reach (k := 0))
        (fun n dest link env ex rest drop => extraBounded.trapSaved s n dest link env ex rest reach drop)
        (raises.caught s op reach member code) (by rw [← semantics]; exact step))
    (fun s args ne => Or.inr (shape s args ne))
    (fun s e w step => raiseTo_not_halt (by rw [← semantics]; exact step))

/-- **The RAISE row.** -/
theorem raise_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (extraBounded : ExtraBounded P) (raises : RaisesCaught P) :
    OCaml.OpArm P (OCaml.LoopAt L P) .RAISE :=
  raise_row_of (by simp [raiseOps]) fits capacity extraBounded raises (fun _ => rfl)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => rfl)
    (fun _ _ _ _ h code space trapSaved caught step =>
      raise_family_next stable rf
        (fun _ _ _ _ _ _ _ _ _ _ input frame quiet stable saved nonnegative writeStable reads space =>
          raise_quiet_step_arm input frame quiet stable saved nonnegative writeStable reads space
            (by simpa only [stepI] using step))
        h code space trapSaved caught step)

/-- **The RERAISE row.** -/
theorem reraise_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (extraBounded : ExtraBounded P) (raises : RaisesCaught P) :
    OCaml.OpArm P (OCaml.LoopAt L P) .RERAISE :=
  raise_row_of (by simp [raiseOps]) fits capacity extraBounded raises (fun _ => rfl)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => rfl)
    (fun _ _ _ _ h code space trapSaved caught step =>
      raise_family_next stable rf
        (fun _ _ _ _ _ _ _ _ _ _ input frame quiet stable saved nonnegative writeStable reads space =>
          reraise_quiet_step_arm input frame quiet stable saved nonnegative writeStable reads space
            (by simpa only [stepI] using step))
        h code space trapSaved caught step)

/-- **The RAISE_NOTRACE row.** -/
theorem raise_notrace_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (extraBounded : ExtraBounded P) (raises : RaisesCaught P) :
    OCaml.OpArm P (OCaml.LoopAt L P) .RAISE_NOTRACE :=
  raise_row_of (by simp [raiseOps]) fits capacity extraBounded raises (fun _ => rfl)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => rfl)
    (fun _ _ _ _ h code space trapSaved caught step =>
      raise_family_next stable rf
        (fun _ _ _ _ _ _ _ _ _ _ input frame quiet stable saved nonnegative writeStable reads space =>
          raise_notrace_quiet_step_arm input frame quiet stable saved nonnegative writeStable reads space
            (by simpa only [stepI] using step))
        h code space trapSaved caught step)

end OCaml.Vm.Sim
