import OCaml.Vm.Boot.Startup.PageAddSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_page_table_add over the `n` pages of an aligned block: one
`page_table_modify_insert` per page, folded by `indexedLoop`. -/

/-- The table after one insertion into slot `s`. -/
theorem table_after_insert {m m' : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} {ent occ v : BitVec 64}
    {s lo hi : Nat} (hs : s < 2048) (fits : ent.toNat + 16384 ≤ heapEnd) (tableHigh : heapStart ≤ ent.toNat)
    (stackLog : LogInW [⟨lo, hi⟩] log) (above : heapEnd ≤ lo)
    (eq : m' = writeLog (writeLog m log)
      [((slotAddr ent (BitVec.ofNat 64 s)).toNat, 8, v), (pageTable + 0x18, 8, occ + 1#64)])
    (F : PageTableFields m occ ent) :
    PageTableFields m' (occ + 1#64) ent ∧
      (∀ i, i < 2048 → slotWord m' ent i = if i = s then v else slotWord m ent i) := by
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  rw [hE] at fits above
  rw [hS] at tableHigh
  have fits64 : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans fits (by decide)
  have slotNat := slotAddr_nat ent s hs fits64
  -- below the arena's end the stack log is invisible
  have low (x : Nat) (hx : x < heapEnd) : ((writeLog m log)[x]?).getD 0 = (m[x]?).getD 0 := by
    rw [hE] at hx
    rw [frameOn_writeLog _ _ _ stackLog x ⟨Or.inl (show x < lo by omega), trivial⟩]
  have record (off w : Nat) (hoff : off + w ≤ 0x18 ∨ 0x20 ≤ off) (hw : off + w ≤ 0x28) (x : Nat)
      (hx : pageTable + off ≤ x ∧ x < pageTable + off + w) : (m'[x]?).getD 0 = (m[x]?).getD 0 := by
    rw [hP] at hx
    rw [eq, writeLog_out _ _ _ (by simp only [OutL, slotNat, hP, and_true]; omega), low x (by rw [hE]; omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [word_observed (m := m) _ fun i hi => record 0 8 (Or.inl (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.size
  · rw [read4_observed (m := m) _ fun k hk => record 8 4 (Or.inl (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.shift
  · rw [word_observed (m := m) _ fun i hi => record 0x10 8 (Or.inl (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.mask
  · rw [eq]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial
  · rw [word_observed (m := m) _ fun i hi => record 0x20 8 (Or.inr (by decide)) (by decide) _ ⟨by omega, by omega⟩]
    exact F.entries
  · intro i hi
    have iNat := slotAddr_nat ent i hi fits64
    split
    · rename_i same; subst same
      unfold slotWord
      rw [eq]
      exact word_writeLog_at _ _ 0 _ _ rfl (by
        simp only [List.drop, OutLRange, hP, and_true]; omega)
    · rename_i ne
      unfold slotWord
      rw [word_observed (m := m) _ fun k hk => by
        rw [eq, writeLog_out _ _ _ (by simp only [OutL, slotNat, iNat, hP, and_true]; omega),
          low _ (by rw [iNat, hE]; omega)]]
end OCaml.Vm.Boot.Startup
