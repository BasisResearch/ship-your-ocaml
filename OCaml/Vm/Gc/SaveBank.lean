import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.StackArithmetic

namespace OCaml.Vm.Gc.SaveBank
open Vsa.Sim Primitives

def log (sp : BitVec 64) (R : Nat → BitVec 64) (slots : List (Nat × Nat)) : List WEntry :=
  slots.map (fun (r,off) => ((sp + BitVec.ofNat 64 off).toNat,8,R r))

/-- A bounded, pairwise-separated native save bank reads back every saved
register. Stack arithmetic is shared independently of the particular prologue. -/
theorem read (mem : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) (R : Nat → BitVec 64)
    (slots : List (Nat × Nat)) (extent : Nat)
    (bound : sp.toNat + extent + 8 ≤ 0x100000000)
    (bounded : ∀ cell ∈ slots, cell.2 ≤ extent)
    (separated : slots.Pairwise (fun x y => x.2 + 8 ≤ y.2 ∨ y.2 + 8 ≤ x.2))
    (cell : Nat × Nat) (member : cell ∈ slots) :
    bytesT (writeLog mem (log sp R slots)) (sp + BitVec.ofNat 64 cell.2).toNat 8 = R cell.1 := by
  let cells := slots.map (fun (r,off) => ((sp + BitVec.ofNat 64 off).toNat,R r))
  have separate : cells.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by
    apply List.pairwise_map.mpr
    apply separated.imp_of_mem
    intro x y hx hy sep
    change (sp + BitVec.ofNat 64 x.2).toNat + 8 ≤ (sp + BitVec.ofNat 64 y.2).toNat ∨
      (sp + BitVec.ofNat 64 y.2).toNat + 8 ≤ (sp + BitVec.ofNat 64 x.2).toNat
    rw [stack_address sp x.2 extent bound (bounded x hx),stack_address sp y.2 extent bound (bounded y hy)]
    omega
  have readback := word_writeLog_cells mem cells separate (List.mem_map.mpr ⟨cell,member,rfl⟩)
  simpa only [cells,List.map_map,Function.comp_def,log] using readback

/-- Every saved cell obeys the scalar-store lower bound. -/
theorem high {sp R slots}
    (windows : ∀ cell ∈ slots, WriteWindow (sp + BitVec.ofNat 64 cell.2) 8) :
    ∀ e ∈ log sp R slots, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  obtain ⟨cell,hc,rfl⟩ := List.mem_map.mp member
  exact (windows cell hc).htif

end OCaml.Vm.Gc.SaveBank
