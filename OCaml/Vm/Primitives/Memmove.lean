import OCaml.Vm.Primitives.LibraryStrlen
import VsaIris.Vsa.SnpMove

/-!
# newlib `memmove` as a machine summary

The retargeted library proof `memmove_nw` (`VsaIris/Vsa/SnpMove.lean`, at
ocamlrun's `memmove`, `0x80042644`) covers the non-overlapping copy of `len`
bytes from `src` to `d` (`MoveGeom.disj`). It is bridged here to the
function-summary API exactly as `LibraryStrlen` bridges `strlen_nw`: the
copied bytes equal the source image, every other owned byte keeps its value,
`a0` still holds the destination, and every register outside memmove's
scratch set is kept.
-/

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The registers `memmove` may clobber (`MMFrame`). -/
def memmoveScratch : List Nat := [6, 11, 12, 13, 14, 15, 16, 17, 28]

/-- `memmove` returns to its caller with the destination in `a0`, the copy
done, the rest of its owned bytes unchanged, and its non-scratch registers. -/
structure MemmoveResult (S : Nat → Prop) (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem)
    (d src len : Nat) (g : Nat → BitVec 8) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = R 1
  result : rv 10 = R 10
  registers : ∀ r ∈ nRegs, r ≠ VsaIris.PC → r ∉ memmoveScratch → rv r = R r
  copied : ∀ i, i < len → mv (d + i) = g (src + i)
  rest : ∀ a, S a → (a < d ∨ d + len ≤ a) → mv a = imgM Mt a

/-- Close the landed memmove continuation with its concrete return facts. -/
theorem memmove_symbolic {live Dt DA s dst n} (codeLive : ∀ p ∈ snpText, live p.1)
    (d src len : Nat) (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem)
    (geometry : MoveGeom s dst n d src len)
    (destination : R 10 = BitVec.ofNat 64 d) (source : R 11 = BitVec.ofNat 64 src)
    (length : R 12 = BitVec.ofNat 64 len) (aligned : (R 1).toNat % 4 = 0)
    (window : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g) :
    SnpW live Dt DA (snpS s dst n) (MemmoveResult (snpS s dst n) R Mt d src len g) 0x80042644#64 R Mt := by
  apply memmove_nw codeLive d src len g R Mt geometry destination source length aligned window
  intro R' Mt' frame copied
  apply swp_done
  intro rv mv observed
  have kept : ∀ r ∈ nRegs, r ≠ VsaIris.PC → r ∉ memmoveScratch → rv r = R r := by
    intro r hr ne out
    simp only [memmoveScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    obtain ⟨h6, h11, h12, h13, h14, h15, h16, h17, h28⟩ := out
    exact (observed.regs r hr ne).trans (frame r h11 h12 h13 h14 h15 h16 h17 h6 h28)
  have inside : ∀ i, i < len → snpS s dst n (d + i) := fun i hi => by
    have := geometry.d_in
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  exact ⟨observed.pc, kept 10 (by decide) (by decide) (by decide),
    kept,
    fun i hi => (observed.img _ (inside i hi)).trans (copied.done i hi),
    fun a owned outside => (observed.img a owned).trans (copied.rest a outside)⟩

/-- **Whole-machine `memmove` summary**, reusing the retargeted library proof. -/
theorem memmove_summary {live Dt DA s dst n} (d src len : Nat) (g : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem) (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (geometry : MoveGeom s dst n d src len)
    (destination : R 10 = BitVec.ofNat 64 d) (source : R 11 = BitVec.ofNat 64 src)
    (length : R 12 = BitVec.ofNat 64 len) (aligned : (R 1).toNat % 4 = 0)
    (window : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g)
    (separate : LocalSeparation roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n))
    (input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs (snpS s dst n) R Mt c) :
    FnSummary 0x80042644#64 (fun e => e = c)
      (LocalPost live roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n)
        (MemmoveResult (snpS s dst n) R Mt d src len g) c) :=
  symbolic_summary c separate input
    (memmove_symbolic codeLive d src len g R Mt geometry destination source length aligned window)

end OCaml.Vm.Primitives
