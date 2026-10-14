import OCaml.Vm.Boot.Startup.PageModify
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-! caml_page_table_add over the pages of one aligned block: page `j` is
`base + 4096 j`, its entry `kind | page j`. Entries of different pages differ
above bit 12, which is what caml_page_table_modify's probe compares. -/

/-- Page `j` of the block at `base`. -/
def blockPage (base : BitVec 64) (j : Nat) : BitVec 64 := base + BitVec.ofNat 64 (4096 * j)

theorem bgeu_of_shift {a b : BitVec 64} (ne : a >>> 12 ≠ b >>> 12) : guardB bop.BGEU (a ^^^ b) 4096#64 = true := by
  unfold guardB Functions.zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  apply decide_eq_true
  apply Int.ofNat_le.mpr
  apply Classical.byContradiction
  intro small
  apply ne
  apply BitVec.xor_eq_zero_iff.mp
  rw [← BitVec.ushiftRight_xor_distrib]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat] at small ⊢
  omega

theorem kind_or_shift (kind page : BitVec 64) (small : kind.toNat < 4096) : (kind ||| page) >>> 12 = page >>> 12 := by
  rw [BitVec.ushiftRight_or_distrib]
  have zero : kind >>> 12 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [zero, BitVec.zero_or]

theorem blockPage_shift (base : BitVec 64) (j : Nat) (aligned : base.toNat % 4096 = 0)
    (fits : base.toNat + 4096 * j < 2 ^ 64) : ((blockPage base j) >>> 12).toNat = base.toNat / 4096 + j := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold blockPage
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [p64] at fits ⊢
  rw [Nat.mod_eq_of_lt (a := 4096 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Entries of different pages of the block pass the probe's page test. -/
theorem blockPage_other (base kind : BitVec 64) (j k : Nat) (ne : j ≠ k) (aligned : base.toNat % 4096 = 0)
    (fitsJ : base.toNat + 4096 * j < 2 ^ 64) (fitsK : base.toNat + 4096 * k < 2 ^ 64) (small : kind.toNat < 4096) :
    guardB bop.BGEU (blockPage base k ^^^ (kind ||| blockPage base j)) 4096#64 = true := by
  apply bgeu_of_shift
  rw [kind_or_shift _ _ small]
  intro eq
  have := congrArg BitVec.toNat eq
  rw [blockPage_shift base k aligned fitsK, blockPage_shift base j aligned fitsJ] at this
  omega

/-- The table holds exactly the first `k` pages of the block, each once. -/
def PagesIn (m : Std.ExtHashMap Nat (BitVec 8)) (ent kind base : BitVec 64) (k : Nat) : Prop :=
  ∀ i, i < 2048 → slotWord m ent i ≠ 0#64 → ∃ j, j < k ∧ slotWord m ent i = kind ||| blockPage base j

theorem slotWord_pageSlot (m : Std.ExtHashMap Nat (BitVec 8)) (ent : BitVec 64) (i : Nat) (hi : i < 2048)
    (fits : ent.toNat + 16384 ≤ 2 ^ 64) : slotWord m ent i = pageSlot m ent.toNat i := by
  unfold slotWord pageSlot
  rw [slotAddr_nat ent i hi fits]

theorem pageCount_congr {m m' : Std.ExtHashMap Nat (BitVec 8)} {blk : Nat}
    (same : ∀ i, i < 2048 → pageSlot m' blk i = pageSlot m blk i) : pageCount m' blk = pageCount m blk := by
  unfold pageCount
  rw [List.filter_congr (p := fun i => pageSlot m' blk i != 0#64) (q := fun i => pageSlot m blk i != 0#64)
    (fun i hi => by rw [same i (List.mem_range.mp hi)])]

/-- Page `k` of the block is not in a table holding pages below `k`. -/
theorem PagesIn.absent {m ent kind base k} (P : PagesIn m ent kind base k) (aligned : base.toNat % 4096 = 0)
    (fits : base.toNat + 4096 * k < 2 ^ 64) (small : kind.toNat < 4096) :
    ∀ i, i < 2048 → slotWord m ent i ≠ 0#64 →
      guardB bop.BGEU (blockPage base k ^^^ slotWord m ent i) 4096#64 = true := by
  intro i hi occ
  obtain ⟨j, hj, eq⟩ := P i hi occ
  rw [eq]
  exact blockPage_other base kind j k (by omega) aligned (by omega) fits small

/-- Filling an empty slot with page `k` extends the table to `k + 1` pages. -/
theorem PagesIn.fill {m m' : Std.ExtHashMap Nat (BitVec 8)} {ent kind base k slot}
    (P : PagesIn m ent kind base k)
    (filled : slotWord m' ent slot = kind ||| blockPage base k)
    (others : ∀ i, i < 2048 → i ≠ slot → slotWord m' ent i = slotWord m ent i) :
    PagesIn m' ent kind base (k + 1) := by
  intro i hi occ
  by_cases same : i = slot
  · subst same; exact ⟨k, by omega, filled⟩
  · rw [others i hi same] at occ ⊢
    obtain ⟨j, hj, eq⟩ := P i hi occ
    exact ⟨j, by omega, eq⟩
end OCaml.Vm.Boot.Startup
