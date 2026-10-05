import OCaml.Vm.Gc.G1Room
import OCaml.Vm.Gc.NurseryDefs
import OCaml.Vm.Gc.NurseryTransport
import OCaml.Vm.Sim.InvariantUse
import OCaml.Vm.Sim.NurseryInput

/-!
# The running invariant: nursery geometry (G1 allocation fast path)

The nursery counterpart of a1-arms' `StackGeometry`. An allocating arm
reserves its block in the free part of the nursery, `[young_limit, young_ptr)`
(`nurseryFree`), and initializes it there. `WindowSeparated w` says a window
misses every observed part of the represented payload (statics, `Caml_state`,
code, the live stack, live heap objects, channels, primitive entries);
`WindowSeparated.payload`/`image`/`bindings` turn a log inside `w` into the
`PayloadOutside`/`ImageOutside`/`BindingsOutside` certificates, for any window.
`NurseryGeometry` instantiates it with `nurseryFree` and adds the RAM bounds
from which `header_write`, `young_write`, `limit_read` give the RAM-access
fields of `Sim.NurseryInput`. `reserve` re-establishes the geometry after a
reservation: the free window shrinks, and the new block lies outside it.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Sim OCaml.Vm.Primitives

theorem window_static {w : W} {a n : Nat} (g : Layout.sym_bss_end ≤ w.lo)
    (static : a + n ≤ Layout.sym_bss_end) : OutWRange [w] a n :=
  ⟨Or.inl (by omega), trivial⟩

/-- A subrange of a separated range is separated. -/
theorem outW_sub {w : W} {a n b k : Nat} (h : OutWRange [w] a n) (low : a ≤ b) (high : b + k ≤ a + n) :
    OutWRange [w] b k := by
  obtain ⟨h, -⟩ := h
  exact ⟨by omega, trivial⟩

/-- **Writes inside a separated window miss the represented payload.** -/
theorem WindowSeparated.payload {w : W} {P s c pl cp sp high} {log : List WEntry}
    (g : WindowSeparated w P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (space : high - Layout.stackBytes ≤ sp) (inside : LogInW [w] log) : PayloadOutside log P s c pl cp sp := by
  have hs := stack.1
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 :=
    fun a ha => outLRange_of_windows inside (window_static g.statics ha)
  have domainField : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 :=
    fun off hoff => outLRange_of_windows inside (outW_sub g.domain (by omega) (by omega))
  refine ⟨static _ (by decide), domainField _ (by decide), domainField _ (by decide),
    static _ (by decide), static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩
  · exact fun i v hv => outLRange_of_windows inside (g.code i v hv)
  · intro i v hv
    have bound : i < s.stack.length := (List.getElem?_eq_some_iff.1 hv).1
    exact outLRange_of_windows inside (outW_sub g.stack (by omega) (by omega))
  · intro l a o live placed object
    have ho := g.heap l a o placed object
    exact ⟨outLRange_of_windows inside (outW_sub ho (by omega) (by omega)),
      outLRange_of_windows inside (outW_sub ho (by omega) (by omega))⟩
  · exact fun id ch a hch hcp => outLRange_of_windows inside (g.channels id ch a hch hcp)

theorem WindowSeparated.image {w : W} {P s c pl cp high} {log : List WEntry}
    (g : WindowSeparated w P s c pl cp high) (inside : LogInW [w] log) : ImageOutside log :=
  ⟨outLRange_of_windows inside (window_static g.statics (by decide)),
   outLRange_of_windows inside (window_static g.statics (by decide))⟩

theorem WindowSeparated.bindings {w : W} {P s c pl cp high} {log : List WEntry}
    (g : WindowSeparated w P s c pl cp high) (inside : LogInW [w] log) : BindingsOutside log P c :=
  ⟨outLRange_of_windows inside (window_static g.statics (by decide)),
    fun i name h => outLRange_of_windows inside (g.primitives i name h)⟩

/-- An aligned `Caml_state` word is writable RAM. -/
theorem NurseryGeometry.domain_write {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {off : Nat} (fits : off + 8 ≤ Layout.domainStateBytes) (offAligned : off % 8 = 0) :
    RamWriteAt ((word c Layout.sym_Caml_state).toNat + off) 8 := by
  have hl := g.domainLow
  have hh := g.domainHigh
  have ha := g.domainAligned
  have hb : 0x80000000 ≤ Layout.sym_tohost := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, ← mailbox_layout] at * <;> omega

/-- `NurseryInput.youngWrite`. -/
theorem NurseryGeometry.young_write {P s c pl cp high} (g : NurseryGeometry P s c pl cp high) :
    RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) 8 :=
  g.domain_write (by decide) (by decide)

/-- `NurseryInput.limitRead`. -/
theorem NurseryGeometry.limit_read {P s c pl cp high} (g : NurseryGeometry P s c pl cp high) :
    RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8 :=
  (g.domain_write (by decide) (by decide)).read

/-- `NurseryInput.headerWrite`: the header of a block reserved below
`young_ptr = a + 8 * count`, within capacity, is writable RAM. -/
theorem NurseryGeometry.header_write {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {count a : Nat} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) (room : 8 ≤ a) : RamWriteAt (a - 8) 8 := by
  have hs := g.statics
  have ht := g.top
  have hal := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hr : 0x80000000 ≤ Layout.sym_tohost := by decide
  simp only [nurseryFree] at hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, ← mailbox_layout] at * <;> omega

/-- The reserved block `[a - 8, a + 8 * count)` lies in the free nursery, so
its initializing writes miss the payload (`WindowSeparated.payload`). -/
theorem reserved_inside {c : Config} {count a : Nat} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) {b k : Nat}
    (low : a - 8 ≤ b) (high : b + k ≤ a + 8 * count) : InsideW [nurseryFree c] b k :=
  Or.inl ⟨by simp only [nurseryFree]; omega, by simp only [nurseryFree]; omega⟩

/-- A range inside the free nursery misses any range separated from it. -/
theorem apart_of_inside {c : Config} {x n y k : Nat} (outside : OutWRange [nurseryFree c] x n)
    (low : (runtimeFields c).youngLimit ≤ y) (high : y + k ≤ (runtimeFields c).youngPtr) :
    y + k ≤ x ∨ x + n ≤ y := by
  obtain ⟨h, -⟩ := outside
  simp only [nurseryFree] at h
  omega

/-- **`NurseryPlacement` for a nursery reservation**: an object of at most
`count` fields reserved below `young_ptr = a + 8 * count`, within capacity. -/
theorem NurseryGeometry.placement {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {count a : Nat} {o : Obj} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) (room : 8 ≤ a) (size : o.wosize ≤ count) :
    NurseryPlacement P pl high a o := by
  have statics := g.statics
  have arena := g.arena
  simp only [nurseryFree] at statics
  have low : (runtimeFields c).youngLimit ≤ a - 8 := capacity
  have high' : a - 8 + (8 * o.wosize + 8) ≤ (runtimeFields c).youngPtr := by omega
  refine ⟨⟨?_, trivial⟩, by omega, by omega, ⟨?_, trivial⟩, ⟨?_, trivial⟩⟩
  · have := apart_of_inside g.stack low high'
    simp only [stackWindow]
    omega
  · have := apart_of_inside g.codeRange low high'
    omega
  · have := apart_of_inside g.atoms low high'
    omega

end OCaml.Vm.Gc
