import OCaml.Vm.Gc.FreePlacement
import OCaml.Vm.Gc.BestFitSmall
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Primitives.MemoryFrame

/-!
# Placement of the best-fit small lists

`bf_small_fl[size]` heads a null-terminated list of free blocks of `size`
fields, linked through each block's first field (`freelist.c`).
`SmallChain lo hi size c a` says every block on the list from `a` lies in
`[lo, hi)`. Stores outside `[lo, hi)` preserve it (`SmallChain.frame`), and
the actual exact-size pop (`BestFitSmall.allocate`) returns a block in
`[lo, hi)` and leaves the slot heading a chain again (`SmallChain.pop`).
-/

namespace OCaml.Vm.Gc.FreeLists
open Vsa.Machine Vsa.Sim Primitives

/-- Every store of `log` misses `[lo, hi)`. -/
def Outside (lo hi : Nat) (log : List WEntry) : Prop := ∀ w ∈ log, w.1 + w.2.1 ≤ lo ∨ hi ≤ w.1

/-- A small free list of `size`-field blocks, each in `[lo, hi)`. Finite by
construction: a cyclic list has no derivation. -/
inductive SmallChain (lo hi size : Nat) (c : Config) : BitVec 64 → Prop where
  | nil : SmallChain lo hi size c 0
  | cons {a : BitVec 64} (nonnull : a ≠ 0) (inside : lo + 8 ≤ a.toNat ∧ a.toNat + 8 * size ≤ hi)
      (rest : SmallChain lo hi size c (word c a.toNat)) : SmallChain lo hi size c a

/-- A chain survives stores outside its region. -/
theorem SmallChain.frame {lo hi size : Nat} {c c' : Config} {log : List WEntry}
    (memory : c'.σ.mem = writeLog c.σ.mem log) (outside : Outside lo hi log) (field : 1 ≤ size) :
    ∀ {a}, SmallChain lo hi size c a → SmallChain lo hi size c' a := by
  intro a list
  induction list with
  | nil => exact .nil
  | @cons a nonnull inside _ ih =>
    have same : word c' a.toNat = word c a.toNat := by
      change bytesT c'.σ.mem a.toNat 8 = bytesT c.σ.mem a.toNat 8
      rw [memory, OCaml.Vm.Primitives.bytesT_writeLog_out _ (outLRange_of_forall fun w hw => by
        rcases outside w hw with h | h <;> omega)]
    exact .cons nonnull inside (same ▸ ih)

theorem slot_toNat {size : BitVec 64} (small : size.toNat ≤ Layout.bf_small_count) :
    (BestFitSmall.slot size).toNat = Layout.sym_bf_small_fl + Layout.bf_small_size * size.toNat := by
  simp only [BestFitSmall.slot, Layout.bf_small_size, Layout.sym_bf_small_fl, Layout.bf_small_count] at small ⊢
  rw [show Nat.log2 16 = 4 from rfl, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- **The small-list pop stays in the region.** The returned header lies in
`[lo, hi)` with its `size` fields, and the slot heads a chain again. -/
theorem SmallChain.pop {lo hi : Nat} {ra size : BitVec 64} {before after : Config}
    (post : BestFitSmall.Post ra size before after)
    (list : SmallChain lo hi size.toNat before (BestFitSmall.first size before))
    (nonnull : BestFitSmall.first size before ≠ 0) (positive : 0 < size.toNat)
    (small : size.toNat ≤ Layout.bf_small_count) (statics : Layout.sym_bss_end ≤ lo) :
    gprGet after.σ 10 = some (BestFitSmall.first size before - BitVec.ofNat 64 Layout.header_bytes) ∧
      lo ≤ (BestFitSmall.first size before).toNat - 8 ∧
      (BestFitSmall.first size before).toNat - 8 + 8 * (size.toNat + 1) ≤ hi ∧
      SmallChain lo hi size.toNat after (word after (BestFitSmall.slot size).toNat) := by
  have slot := slot_toNat small
  simp only [Layout.bf_small_size, Layout.sym_bf_small_fl, Layout.bf_small_count, Layout.sym_bss_end] at slot small statics
  have static : Outside lo hi (BestFitSmall.effect size before) := by
    intro w hw
    simp only [BestFitSmall.effect, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · left; simp only [slot]; omega
    · left; simp only [Layout.sym_caml_fl_cur_wsz]; omega
  have head : word after (BestFitSmall.slot size).toNat = word before (BestFitSmall.first size before).toNat := by
    change bytesT after.σ.mem _ 8 = _
    rw [post.memory]
    exact word_writeLog_at _ _ 0 _ _ rfl (outLRange_of_forall fun w hw => by
      simp only [BestFitSmall.effect, List.drop_succ_cons, List.drop_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      subst hw
      simp only [slot, Layout.sym_caml_fl_cur_wsz]
      omega)
  have result := post.result
  generalize BestFitSmall.first size before = f at list nonnull head result ⊢
  cases list with
  | nil => exact absurd rfl nonnull
  | cons _ inside rest =>
    refine ⟨result, by omega, by omega, ?_⟩
    rw [head]
    exact SmallChain.frame post.memory static positive rest

end OCaml.Vm.Gc.FreeLists

namespace OCaml.Vm.Gc.FreeLists
open Vsa.Machine Vsa.Sim Primitives

/-- Every small list `1 ≤ i ≤ 16` lies in `[lo, hi)`. -/
def SmallListsIn (lo hi : Nat) (c : Config) : Prop :=
  ∀ i : Nat, 1 ≤ i → i ≤ Layout.bf_small_count →
    SmallChain lo hi i c (word c (BestFitSmall.slot (BitVec.ofNat 64 i)).toNat)

/-- **The small-list pop preserves every small list's placement.** -/
theorem SmallListsIn.pop {lo hi : Nat} {ra size : BitVec 64} {before after : Config}
    (post : BestFitSmall.Post ra size before after) (lists : SmallListsIn lo hi before)
    (nonnull : BestFitSmall.first size before ≠ 0) (positive : 0 < size.toNat)
    (small : size.toNat ≤ Layout.bf_small_count) (statics : Layout.sym_bss_end ≤ lo) :
    SmallListsIn lo hi after := by
  have sizeEq : BitVec.ofNat 64 size.toNat = size := by simp
  have own := lists size.toNat positive small
  rw [sizeEq] at own
  have popped := (SmallChain.pop post own nonnull positive small statics).2.2.2
  have slotSize := slot_toNat small
  simp only [Layout.bf_small_size, Layout.sym_bf_small_fl, Layout.bf_small_count, Layout.sym_bss_end] at slotSize small statics
  intro i low high
  by_cases same : i = size.toNat
  · subst same
    rw [sizeEq]
    exact popped
  · have small' : (BitVec.ofNat 64 i).toNat ≤ Layout.bf_small_count := by
      simp only [BitVec.toNat_ofNat, Layout.bf_small_count] at high ⊢
      omega
    have slotI := slot_toNat small'
    simp only [BitVec.toNat_ofNat, Layout.bf_small_size, Layout.sym_bf_small_fl, Layout.bf_small_count] at slotI high
    have keep : word after (BestFitSmall.slot (BitVec.ofNat 64 i)).toNat =
        word before (BestFitSmall.slot (BitVec.ofNat 64 i)).toNat := by
      change bytesT after.σ.mem _ 8 = bytesT before.σ.mem _ 8
      rw [post.memory, OCaml.Vm.Primitives.bytesT_writeLog_out _ (outLRange_of_forall fun w hw => by
        simp only [BestFitSmall.effect, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · simp only [slotI, slotSize]
          rw [Nat.mod_eq_of_lt (by omega)] at slotI
          omega
        · simp only [slotI, Layout.sym_caml_fl_cur_wsz]
          omega)]
    rw [keep]
    have static : Outside lo hi (BestFitSmall.effect size before) := by
      intro w hw
      simp only [BestFitSmall.effect, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · left; simp only [slotSize]; omega
      · left; simp only [Layout.sym_caml_fl_cur_wsz]; omega
    exact SmallChain.frame post.memory static low (lists i low (by simpa [Layout.bf_small_count] using high))

end OCaml.Vm.Gc.FreeLists
