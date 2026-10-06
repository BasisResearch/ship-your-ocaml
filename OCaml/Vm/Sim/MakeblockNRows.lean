import OCaml.Vm.Sim.ClosureAllocRows
import OCaml.Vm.Sim.Makeblock

/-!
# MAKEBLOCK n from the loop head

The general constructor reserves `size` words, writes the header and the
accumulator field, then copies `size - 1` stack values (`MakeblockInitInput`).
Its size operand is bounded by the minor heap's limit (`BlockSizes`, a named
per-program fact under G1).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **Every reachable MAKEBLOCK's size fits the minor heap** (named per-program
code fact under G1: larger blocks go to the major heap). -/
structure BlockSizes (P : Prog) : Prop where
  small : ∀ s (w : BitVec 32), Reach P s → DispatchCode P s .MAKEBLOCK → P.code[s.pc + 1]? = some w →
    w.toInt.toNat ≤ 256

/-- MAKEBLOCK's field copy at the loop head. -/
theorem MakeblockInitInput.of_block {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high a k tag : Nat} {accu : BitVec 64} (b : ReservedBlock c a k)
    (g : Gc.NurseryGeometry P s c pl cp high) (sg : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (positive : 0 < k) (bound : k - 1 ≤ s.stack.length) :
    MakeblockInitInput sp k tag a (word c Layout.sym_Caml_state).toNat accu c := by
  have hs := stack.1
  have stat := sg.statics
  have top := sg.top
  have spSpace : high - Layout.stackBytes ≤ sp := by omega
  have room := b.room
  have apartStack := b.stackApart g
  have hd := sg.domain.1
  simp only [stackWindow] at hd
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have len : (stackWords c sp (k - 1)).length = k - 1 := by simp [stackWords]
  have copyIn : LogInW [⟨a - 8, a + 8 * k⟩] (valueLog (a + 8) (stackWords c sp (k - 1))) :=
    logInW_widen (value_log_in (a + 8) _) fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; dsimp only; rw [len]; omega
  have setupIn : LogInW [⟨a - 8, a + 8 * k⟩] [(a - 8, 8, blockHeader k tag), (a, 8, accu)] :=
    ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
      trivial⟩
  have blockMiss : ∀ {log : List WEntry}, LogInW [⟨a - 8, a + 8 * k⟩] log → OutLRange log sp (8 * (k - 1)) :=
    fun inside => outLRange_of_windows inside ⟨by dsimp only; omega, trivial⟩
  refine ⟨⟨?_, fun i hi => sg.read stack spSpace (by rw [len] at hi; omega),
    fun i hi => b.write (by omega) (by rw [len] at hi; omega) (by have := b.aligned; omega),
    g.toWindowSeparated.image (b.free copyIn), by rw [len]; exact blockMiss copyIn,
    fun i w hw => stackWords_get hw⟩,
    outLRange_append (grab_out (by omega)) (blockMiss setupIn)⟩
  simp only [PointerCopyShape.counterBase, cursorCopyShape, Bool.false_eq_true, ite_false, len]
  omega

/-- **The MAKEBLOCK n row.** -/
theorem makeblock_row {L : OCaml.Layout} {P : Prog} (allocFrame : AllocFrame L)
    (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget)
    (budgetSmall : L.budget.heapWords < 2^31) (sizes : BlockSizes P) :
    OCaml.OpArm P (OCaml.LoopAt L P) .MAKEBLOCK :=
  opArm_of_next2 (fun s s' c sz t reach reach' h code fetchS fetchT step => by
      have guard := Res.guard_ok step
      have sizeNonnegative : 0 ≤ sz.toInt := by omega
      have tagNonnegative : 0 ≤ t.toInt := by omega
      obtain ⟨tagSmall, positive, bound, state⟩ := makeBlock_next (Res.unguard step)
      have nursery := sizes.small s sz reach code fetchS
      have budget := (fits s' reach').2
      rw [← state] at budget
      simp only [makeblockState, Heap.words_alloc, makeblockObject_wosize positive bound] at budget
      have space := stack_fits fits capacity reach (k := 0)
      simp only [Nat.add_zero] at space
      obtain ⟨pl0, cp, sp, high, input0⟩ := ArmInput.of_loop h code
      have reserve : Reservation L s c sz.toInt.toNat := ⟨input0.geometry.room, by omega⟩
      have b := ReservedBlock.of_reservation input0.geometry.nursery reserve
      have input := input0.put (alloc_absent s.heap (makeblockObject s sz.toInt.toNat t.toInt.toNat)) b.aligned
      obtain ⟨accu, -, value⟩ := input.accu
      have mk := MakeblockInput.of_input input put_self reserve positive bound (by omega) tagSmall value space
      have init := MakeblockInitInput.of_block (tag := t.toInt.toNat) (accu := accu) b input.geometry.nursery
        input.geometry.toStackGeometry input.stack space positive bound
      have blk : LogInW [⟨((runtimeFields c).youngPtr - 8 * sz.toInt.toNat) - 8,
          ((runtimeFields c).youngPtr - 8 * sz.toInt.toNat) + 8 * sz.toInt.toNat⟩]
          (blockLog ((runtimeFields c).youngPtr - 8 * sz.toInt.toNat) t.toInt.toNat
            (makeblockWords c sp sz.toInt.toNat accu)) := by
        have hin := blockLog_in (a := (runtimeFields c).youngPtr - 8 * sz.toInt.toNat) (tag := t.toInt.toNat)
          (words := makeblockWords c sp sz.toInt.toNat accu) b.room
          (by rw [makeblockWords_length positive]; omega)
        rwa [makeblockWords_length positive] at hin
      have runtime : AllocationRuntime L.runtimeOk c (makeblockLog c sp sz.toInt.toNat t.toInt.toNat _ _ accu) :=
        allocFrame.alloc P s c _ cp high _ _ input.runtime input.geometry.nursery (b.free blk) b.capacity
          (by have := b.young; omega) (by have := b.aligned; omega)
      obtain ⟨after, run, running⟩ := makeblock_step_arm runtime input
        (OperandAt.of_fetch input.geometry.toArmGeometry fetchS) (OperandAt.of_fetch input.geometry.toArmGeometry fetchT)
        sizeNonnegative tagNonnegative nursery value mk init step
      exact ⟨after, run, h.of_plus run running⟩)
    (shape2 (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
    (fun s a b e w step => by
      simp only [stepI] at step
      split at step
      · cases step
      · unfold makeBlock at step
        repeat' split at step
        all_goals cases step)

end OCaml.Vm.Sim
