import OCaml.Vm.Boot.Startup.PageAddModel

/-! A fresh block's pages are not yet in the page table when every occupied
slot names a page inside a live block: the `disjoint` obligation of
`PageAddSpan` for any caml_page_table_add of newly allocated memory. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives LeanRV64DExecutable

/-- A page-table entry `w = kind ||| page` for a page inside the live block `block`. -/
structure PageEntry (H : List (Nat × Nat)) (w kind page : BitVec 64) (block : Nat × Nat) : Prop where
  owned : block ∈ H
  inBlock : InExt block page.toNat
  aligned : page.toNat % 4096 = 0
  small : kind.toNat < 4096
  word : w = kind ||| page

/-- An occupied slot names a page inside some live block. -/
def SlotInBlock (H : List (Nat × Nat)) (w : BitVec 64) : Prop :=
  ∃ kind page block, PageEntry H w kind page block

theorem fresh_page_apart {H : List (Nat × Nat)} {p size : Nat} (fresh : FreshBlock vsaLayoutP H p size)
    {base : BitVec 64} {j : Nat} (aligned : base.toNat % 4096 = 0) (fits : base.toNat + 4096 * j < 2 ^ 64)
    (lo : p ≤ base.toNat + 4096 * j) (hi : base.toNat + 4096 * j < p + size)
    {w : BitVec 64} (occupied : SlotInBlock H w) :
    guardB bop.BGEU (blockPage base j ^^^ w) 4096#64 = true := by
  obtain ⟨kind, page, block, slot⟩ := occupied
  apply bgeu_of_shift
  rw [slot.word, kind_or_shift _ _ slot.small]
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [blockPage_shift base j aligned fits, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
  have pa := slot.aligned
  have same : page.toNat = base.toNat + 4096 * j := by simp only [Nat.reducePow] at h; omega
  obtain ⟨_, _, _, apart⟩ := fresh
  have inside : InExt (p, size) page.toNat := by unfold InExt; dsimp only; omega
  exact apart block slot.owned _ inside slot.inBlock

end OCaml.Vm.Boot.Startup
