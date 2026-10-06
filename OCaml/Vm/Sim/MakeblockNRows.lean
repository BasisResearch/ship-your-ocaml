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

end OCaml.Vm.Sim
