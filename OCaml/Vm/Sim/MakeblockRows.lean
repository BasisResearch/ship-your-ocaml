import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.Makeblock1
import OCaml.Vm.Sim.Makeblock2
import OCaml.Vm.Sim.Makeblock3
import OCaml.Vm.Sim.OperandTableRows
import OCaml.Vm.Gc.F1Runtime

/-!
# MAKEBLOCK1..3 from the loop head

The fresh block is placed at `young_ptr - 8 * count` (`ArmInput.put`), its
capacity comes from the G1 room and the budget at the successor state, and
the arm's input is `MakeblockInput.of_input`. The tag bound comes from the
step (`makeBlock` makes a tag of 256 or more `.unsupported`). One named
premise remains:
* `AllocFrame L`: the layout's runtime invariant survives a nursery
  reservation (a6-gc, `Gc.f1_allocation` for F1).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **A nursery reservation keeps the layout's runtime invariant** (named
obligation, a6-gc): the young-pointer store followed by stores into the free
nursery, with the new `young_ptr` within the old free window. -/
structure AllocFrame (L : OCaml.Layout) : Prop where
  alloc : ∀ (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (high a : Nat) (log : List WEntry),
    L.runtimeOk c → Gc.NurseryGeometry P s c pl cp high → LogInW [Gc.nurseryFree c] log →
    (runtimeFields c).youngLimit ≤ a - 8 → a - 8 ≤ (runtimeFields c).youngPtr → (a - 8) % 8 = 0 →
    AllocationRuntime L.runtimeOk c (grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ log)

/-- `AllocFrame` for the pinned F1 layout (a6-gc's `f1_allocFrame_core`). -/
theorem f1_allocFrame : AllocFrame Gc.f1Layout :=
  ⟨fun _ _ _ _ _ _ _ _ ok g inside low below aligned => Gc.f1_allocFrame_core ok g inside low below aligned⟩

/-- A continuing `makeBlock` had a header-sized tag and its fields on the stack. -/
theorem makeBlock_next {s s' : St} {len size tag : Nat} (step : makeBlock s len size tag = .next s') :
    tag < 256 ∧ 0 < size ∧ size - 1 ≤ s.stack.length ∧ makeblockState s len size tag = s' := by
  have small : tag < 256 := Nat.not_le.mp (Res.guard_ok step)
  refine ⟨small, ?_⟩
  replace step := Res.unguard step
  by_cases zero : size = 0
  · simp [zero] at step
  · by_cases short : s.stack.length < size - 1
    · simp [zero, short] at step
    · simp only [zero, short, ite_false, Res.next.injEq] at step
      exact ⟨by omega, by omega, by simpa [makeblockState, makeblockObject] using step⟩

/-- The shared MAKEBLOCKk row adapter. -/
theorem makeblock_fixed_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {k : Nat} {w : BitVec 32} (allocFrame : AllocFrame L)
    (arm : ∀ pl cp sp high a domain limit accu,
      AllocationRuntime L.runtimeOk c (makeblockLog c sp k w.toInt.toNat a domain accu) →
      ArmInput L P s op c pl cp sp high → OperandAt P pl (s.pc + 1) w → 0 ≤ w.toInt →
      valWord pl s.accu = some accu →
      MakeblockInput P s c pl cp sp high k w.toInt.toNat a domain limit accu →
      ∃ after, OCaml.Plus c after ∧ OCaml.Running L P s' after)
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op) (fetch : P.code[s.pc + 1]? = some w)
    (nonnegative : 0 ≤ w.toInt) (tagBound : w.toInt.toNat < 256) (positive : 0 < k) (small : k < 2^31)
    (bound : k - 1 ≤ s.stack.length) (fits : s.heap.words + (k + 1) ≤ L.budget.heapWords)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl0, cp, sp, high, input0⟩ := ArmInput.of_loop h code
  have reserve : Reservation L s c k := ⟨input0.geometry.room, fits⟩
  have capacityAll := reserve.capacity
  have alignedPtr := input0.geometry.nursery.aligned
  have aligned : ((runtimeFields c).youngPtr - 8 * k) % 8 = 0 := by omega
  have input := input0.put (alloc_absent s.heap (makeblockObject s k w.toInt.toNat)) aligned
  obtain ⟨accu, -, value⟩ := input.accu
  have mk := MakeblockInput.of_input input put_self reserve positive bound small tagBound value space
  have young' : (runtimeFields c).youngPtr = ((runtimeFields c).youngPtr - 8 * k) + 8 * k := by omega
  have cap : (runtimeFields c).youngLimit ≤ ((runtimeFields c).youngPtr - 8 * k) - 8 := by omega
  have roomA : 8 ≤ (runtimeFields c).youngPtr - 8 * k := by omega
  have blk : LogInW [⟨((runtimeFields c).youngPtr - 8 * k) - 8, ((runtimeFields c).youngPtr - 8 * k) + 8 * k⟩]
      (blockLog ((runtimeFields c).youngPtr - 8 * k) w.toInt.toNat (makeblockWords c sp k accu)) := by
    have hin := blockLog_in (a := (runtimeFields c).youngPtr - 8 * k) (tag := w.toInt.toNat)
      (words := makeblockWords c sp k accu) roomA (by rw [makeblockWords_length positive]; omega)
    rwa [makeblockWords_length positive] at hin
  have free := block_in_free young' cap blk
  have runtime : AllocationRuntime L.runtimeOk c (makeblockLog c sp k w.toInt.toNat _ _ accu) :=
    allocFrame.alloc P s c _ cp high _ _ input.runtime input.geometry.nursery free cap
      (by omega) (by omega)
  obtain ⟨after, run, running⟩ := arm _ cp sp high _ _ _ accu runtime input
    (OperandAt.of_fetch input.geometry.toArmGeometry fetch) nonnegative value mk
  exact ⟨after, run, h.of_plus run running⟩

/-- **The MAKEBLOCK1 row.** -/
theorem makeblock1_row {L : OCaml.Layout} {P : Prog} (allocFrame : AllocFrame L)
    (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget) :
    OCaml.OpArm P (OCaml.LoopAt L P) .MAKEBLOCK1 :=
  opArm_of_next1 (fun s s' c w reach reach' h code fetch step => by
      have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
      have body := Res.unguard step
      obtain ⟨tagBound, positive, bound, state⟩ := makeBlock_next body
      have budget := (fits s' reach').2
      rw [← state] at budget
      simp only [makeblockState, Heap.words_alloc, makeblockObject_wosize positive bound] at budget
      exact makeblock_fixed_next allocFrame
        (fun _ _ _ _ _ _ _ _ runtime input operand nonnegative value mk =>
          makeblock1_step_arm runtime input operand nonnegative value mk step)
        h code fetch nonnegative tagBound positive (by decide) bound (by omega)
        (by simpa using stack_fits fits capacity reach (k := 0)))
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl))
    (fun s a e w step => by
      simp only [stepI] at step
      split at step
      · cases step
      · unfold makeBlock at step
        repeat' split at step
        all_goals cases step)

/-- **The MAKEBLOCK2 row.** -/
theorem makeblock2_row {L : OCaml.Layout} {P : Prog} (allocFrame : AllocFrame L)
    (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget) :
    OCaml.OpArm P (OCaml.LoopAt L P) .MAKEBLOCK2 :=
  opArm_of_next1 (fun s s' c w reach reach' h code fetch step => by
      have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
      have body := Res.unguard step
      obtain ⟨tagBound, positive, bound, state⟩ := makeBlock_next body
      have budget := (fits s' reach').2
      rw [← state] at budget
      simp only [makeblockState, Heap.words_alloc, makeblockObject_wosize positive bound] at budget
      exact makeblock_fixed_next allocFrame
        (fun _ _ _ _ _ _ _ _ runtime input operand nonnegative value mk =>
          makeblock2_step_arm runtime input operand nonnegative value mk step)
        h code fetch nonnegative tagBound positive (by decide) bound (by omega)
        (by simpa using stack_fits fits capacity reach (k := 0)))
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl))
    (fun s a e w step => by
      simp only [stepI] at step
      split at step
      · cases step
      · unfold makeBlock at step
        repeat' split at step
        all_goals cases step)

/-- **The MAKEBLOCK3 row.** -/
theorem makeblock3_row {L : OCaml.Layout} {P : Prog} (allocFrame : AllocFrame L)
    (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget) :
    OCaml.OpArm P (OCaml.LoopAt L P) .MAKEBLOCK3 :=
  opArm_of_next1 (fun s s' c w reach reach' h code fetch step => by
      have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
      have body := Res.unguard step
      obtain ⟨tagBound, positive, bound, state⟩ := makeBlock_next body
      have budget := (fits s' reach').2
      rw [← state] at budget
      simp only [makeblockState, Heap.words_alloc, makeblockObject_wosize positive bound] at budget
      exact makeblock_fixed_next allocFrame
        (fun _ _ _ _ _ _ _ _ runtime input operand nonnegative value mk =>
          makeblock3_step_arm runtime input operand nonnegative value mk step)
        h code fetch nonnegative tagBound positive (by decide) bound (by omega)
        (by simpa using stack_fits fits capacity reach (k := 0)))
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl))
    (fun s a e w step => by
      simp only [stepI] at step
      split at step
      · cases step
      · unfold makeBlock at step
        repeat' split at step
        all_goals cases step)

end OCaml.Vm.Sim
