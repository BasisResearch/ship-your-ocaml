import OCaml.Vm.Primitives.Named.NamedTransport
import Vsa.Densify.Transport

/-!
# The named-value table in the loop invariant

`NamedAt c pl named` is the loop invariant's view of `callback.c`'s table:
the table's memory (`TableCore`) represents `world.named` in the densified
memory `fillZeroMem c.σ.mem`, and its bytes lie in RAM below the arena's end.
Stating it over the densified memory makes it a fact about total reads
(`getD 0`), which is what native paths' frames give (`NamedAt.frame`); at a
C call entry whose RAM is dense, `NamedAt.tableAt` turns it into
`NamedTableAt` of the real memory, with the code pins `strcmp` needs from the
image. `NamedFoot` is the footprint a native path's writes must miss.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Bytecode OCaml.Vm OCaml.Vm.Primitives

/-- **The named-value table at a loop head**, with chains `chains`: they
represent `named` in the densified memory, and the table's bytes lie in RAM
below `heapEnd`. The loop invariant holds `∃ chains, NamedAt c pl named chains`. -/
structure NamedAt (c : Config) (pl : Place) (named : List (String × Val))
    (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)) : Prop where
  core : TableCore (Vsa.Densify.fillZeroMem c.σ.mem) pl named chains
  ram : ∀ a, TableFoot chains a → Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Sim.DlHeap.heapEnd

/-- The table's bytes at `c`, for any chains it holds. -/
def NamedFoot (c : Config) (pl : Place) (named : List (String × Val)) (a : Nat) : Prop :=
  ∃ chains, NamedAt c pl named chains ∧ TableFoot chains a

/-- Densified memories agree (with presence) on RAM bytes whose total reads agree. -/
theorem agree_fill {m m' : Mem} {a : Nat} (ram : Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Sim.DlHeap.heapEnd)
    (same : (m'[a]?).getD 0 = (m[a]?).getD 0) :
    Agree (Vsa.Densify.fillZeroMem m) (Vsa.Densify.fillZeroMem m') a := by
  have hi : a < Vsa.Densify.ramBase + Vsa.Densify.ramSize := by
    have := ram.2; simp only [Vsa.Sim.DlHeap.heapEnd, Vsa.Densify.ramBase, Vsa.Densify.ramSize] at *; omega
  apply agree_of_eq
  rw [Vsa.Densify.fillZeroMem_ram _ ram.1 hi, Vsa.Densify.fillZeroMem_ram _ ram.1 hi, same]

/-- **The table across a native path** whose total reads agree on the
table's bytes. -/
theorem NamedAt.frame {c c' : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : NamedAt c pl named chains)
    (same : ∀ a, TableFoot chains a → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) :
    NamedAt c' pl named chains :=
  ⟨h.core.transport fun a t => agree_fill (h.ram a t) (same a t), h.ram⟩

/-- **At a dense C call entry** the table represents `named` in the real
memory, with the image's code pins. -/
theorem NamedAt.tableAt {c : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : NamedAt c pl named chains)
    (dense : ∀ a, Vsa.Densify.ramBase ≤ a → a < Vsa.Densify.ramBase + Vsa.Densify.ramSize →
      (c.σ.mem[a]?).isSome)
    (image : ExecutableImage c) : TableShape c.σ.mem pl named chains := by
  have core := h.core
  rw [Vsa.Densify.fillZeroMem_eq_of_dense dense] at core
  exact { core with code := strcmp_loaded image, mask := mask_pinned image }

end OCaml.Vm.Primitives.Named.NamedValue
