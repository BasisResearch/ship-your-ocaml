import OCaml.Vm.Gc.BestFitSmall

/-! # The best-fit allocator's free structures

Toward the major heap's allocation readiness (the fresh-copy routes of
`caml_oldify_one` allocate through `caml_alloc_shr_for_minor_gc`): the
best-fit policy's small free lists. Size `s ≤ 16` has a list headed at
`bf_small_fl[s].free`, linked through each free block's first word
(`SmallList`); `SmallShape` gives every list with its windows. A nonempty
list supplies the exact-size path's core conditions (`core_of_nonempty`). -/
namespace OCaml.Vm.Gc.BfShape
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A small free list from `p`, linked through each block's first word. -/
def SmallList (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 → List (BitVec 64) → Prop
  | p, [] => p = 0#64
  | p, b :: bs => p = b ∧ b ≠ 0#64 ∧ SmallList m (bytesT m b.toNat 8) bs

/-- The list slot of size `s`. -/
def slot (s : Nat) : BitVec 64 := BestFitSmall.slot (BitVec.ofNat 64 s)

/-- **The small free lists** in memory `m`, list `lists s` for size `s`. -/
structure SmallShape (m : Std.ExtHashMap Nat (BitVec 8)) (lists : Nat → List (BitVec 64)) : Prop where
  linked : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → SmallList m (bytesT m (slot s).toNat 8) (lists s)
  /-- every listed block's link word is readable -/
  blocks : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s, ReadWindow b 8

theorem slot_toNat (s : Nat) (hi : s ≤ Layout.bf_small_count) :
    (slot s).toNat = Layout.sym_bf_small_fl + 16 * s := by
  have log : Nat.log2 Layout.bf_small_size = 4 := by decide
  simp only [slot, BestFitSmall.slot, log, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Layout.sym_bf_small_fl]
  simp only [Layout.bf_small_count] at hi
  omega

theorem slot_write (s : Nat) (hi : s ≤ Layout.bf_small_count) : WriteWindow (slot s) 8 := by
  have h := slot_toNat s hi
  simp only [Layout.bf_small_count] at hi
  constructor <;> rw [h] <;> simp only [Layout.sym_bf_small_fl, Layout.sym_tohost] <;> omega

theorem merge_read (s : Nat) (hi : s ≤ Layout.bf_small_count) :
    ReadWindow (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge) 8 := by
  have h := slot_toNat s hi
  simp only [Layout.bf_small_count] at hi
  have addr : (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat = Layout.sym_bf_small_fl + 16 * s + 8 := by
    rw [BitVec.toNat_add, h]; simp only [BitVec.toNat_ofNat, Layout.off_bf_small_merge, Layout.sym_bf_small_fl]; omega
  constructor <;> rw [addr] <;> simp only [Layout.sym_bf_small_fl, Layout.sym_tohost] <;> omega

/-- **A nonempty small list** supplies the exact-size path's core conditions. -/
theorem core_of_nonempty {m : Std.ExtHashMap Nat (BitVec 8)} {lists : Nat → List (BitVec 64)} {c : Config}
    (shape : SmallShape m lists) (memory : c.σ.mem = m) {s : Nat} (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count)
    (nonempty : lists s ≠ []) : BestFitSmall.CoreConditions (BitVec.ofNat 64 s) c := by
  have linked := shape.linked s lo hi
  obtain ⟨b, bs, hb⟩ : ∃ b bs, lists s = b :: bs := by
    cases h : lists s with
    | nil => exact absurd h nonempty
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [hb] at linked
  obtain ⟨head, nonzero, -⟩ := linked
  have firstEq : BestFitSmall.first (BitVec.ofNat 64 s) c = b := by
    unfold BestFitSmall.first word
    rw [memory]; exact head
  have small : s < 2 ^ 64 := by simp only [Layout.bf_small_count] at hi; omega
  refine ⟨?_, ?_, ?_, slot_write s hi, merge_read s hi, ?_, ?_⟩
  · simp only [BitVec.toNat_ofNat]; omega
  · simp only [BitVec.toNat_ofNat]; omega
  · rw [firstEq]; exact nonzero
  · rw [firstEq]; exact shape.blocks s lo hi b (by rw [hb]; exact List.mem_cons_self ..)
  · apply outLRange_of_forall
    intro e member
    simp only [List.mem_singleton] at member
    subst member
    have h := slot_toNat s hi
    simp only [Layout.bf_small_count] at hi
    show _ ∨ (BestFitSmall.slot (BitVec.ofNat 64 s)).toNat + 8 ≤ _
    rw [show BestFitSmall.slot (BitVec.ofNat 64 s) = slot s from rfl, h]
    simp only [Layout.sym_bf_small_fl, Layout.sym_caml_fl_cur_wsz]
    omega

end OCaml.Vm.Gc.BfShape
