import OCaml.Vm.Sim.Invariant
import OCaml.Vm.Sim.LogWindow
import OCaml.Vm.Sim.ReadGeometry
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.ImageFrame
import OCaml.Vm.Primitives.Write

/-!
# Consuming the stack geometry

Every write an arm makes to the VM stack lies in `[high - stackBytes, sp)`,
the free part of the stack allocation. `StackGeometry.outside` turns that one
window fact into the complete `PayloadOutside`/`ImageOutside`/`BindingsOutside`
certificates. `stack_read` and `stack_write` give the read and write windows
of stack words.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The free part of the stack allocation, below the live words. -/
def freeWindow (sp high : Nat) : W := ⟨high - Layout.stackBytes, sp⟩

theorem OutWRange.narrow {high sp a n : Nat} (h : OutWRange [stackWindow high] a n)
    (below : sp ≤ high) : OutWRange [freeWindow sp high] a n := by
  obtain ⟨h, -⟩ := h
  exact ⟨by simp only [stackWindow, freeWindow] at h ⊢; omega, trivial⟩

/-- A static range (below `.bss`'s end) is outside the free window. -/
theorem freeWindow_static {sp high a n : Nat} (g : Layout.sym_bss_end + Layout.stackBytes ≤ high)
    (static : a + n ≤ Layout.sym_bss_end) : OutWRange [freeWindow sp high] a n :=
  ⟨Or.inl (by simp only [freeWindow]; omega), trivial⟩

/-- **Stack writes are separated from the rest of the payload.** -/
theorem StackGeometry.payload {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (inside : LogInW [freeWindow sp high] log) : PayloadOutside log P s c pl cp sp := by
  have below : sp ≤ high := by have := stack.1; omega
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 :=
    fun a ha => outLRange_of_windows inside (freeWindow_static g.statics ha)
  have domainField : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := by
    intro off hoff
    apply outLRange_of_windows inside
    have hd := (OutWRange.narrow g.domain below).1
    exact ⟨by simp only [freeWindow] at hd ⊢; omega, trivial⟩
  refine ⟨static _ (by decide), domainField _ (by decide), domainField _ (by decide),
    static _ (by decide), static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩
  · exact fun i w hw => outLRange_of_windows inside (OutWRange.narrow (g.code i w hw) below)
  · intro i v _
    exact outLRange_of_windows inside ⟨Or.inr (by simp only [freeWindow]; omega), trivial⟩
  · intro l a o live placed object
    have ho := (OutWRange.narrow (g.heap l a o live placed object) below).1
    refine ⟨outLRange_of_windows inside ⟨?_, trivial⟩, outLRange_of_windows inside ⟨?_, trivial⟩⟩
    · simp only [freeWindow] at ho ⊢; omega
    · simp only [freeWindow] at ho ⊢; omega
  · exact fun id ch a hch hcp =>
      outLRange_of_windows inside (OutWRange.narrow (g.channels id ch a hch hcp) below)

theorem StackGeometry.image {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (inside : LogInW [freeWindow sp high] log) :
    ImageOutside log :=
  ⟨outLRange_of_windows inside (freeWindow_static g.statics (by decide)),
   outLRange_of_windows inside (freeWindow_static g.statics (by decide))⟩

theorem StackGeometry.bindings {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (inside : LogInW [freeWindow sp high] log) : BindingsOutside log P c := by
  have below : sp ≤ high := by have := stack.1; omega
  exact ⟨outLRange_of_windows inside (freeWindow_static g.statics (by decide)),
    fun i name h => outLRange_of_windows inside (OutWRange.narrow (g.primitives i name h) below)⟩

/-- The live stack fits the allocation when its length fits the budget
(`Fits`, with `8 * B.stackWords ≤ Layout.stackBytes`). -/
theorem stack_space {c pl sp high} {stk : List Val} (stack : StackRepr c pl sp high stk)
    (fits : 8 * stk.length ≤ Layout.stackBytes) : high - Layout.stackBytes ≤ sp := by
  have := stack.1
  omega

/-- Every live stack word is readable. -/
theorem StackGeometry.read {P s c pl cp sp high} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (space : high - Layout.stackBytes ≤ sp)
    {i : Nat} (hi : i < s.stack.length) : RamReadAt (sp + 8 * i) 8 := by
  have hs := stack.1
  have hb : Layout.sym_tohost + 8 ≤ Layout.sym_bss_end := by decide
  have ht := g.top
  have hg := g.statics
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega

/-- A word in the free window is writable. -/
theorem StackGeometry.write {P s c pl cp sp high} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) {k : Nat} (pos : 0 < k)
    (space : high - Layout.stackBytes + 8 * k ≤ sp) :
    WriteWindow (BitVec.ofNat 64 (sp - 8 * k)) 8 := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have ha := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hn : (BitVec.ofNat 64 (sp - 8 * k)).toNat = sp - 8 * k :=
    Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hn] <;> simp only [Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega

end OCaml.Vm.Sim
