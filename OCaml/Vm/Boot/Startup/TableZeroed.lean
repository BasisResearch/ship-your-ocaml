import OCaml.Vm.Boot.Startup.TableZero
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish : Config}

theorem ResetTablePublished.leaf
    (w : ResetTablePublished initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish) :
    LeafInput jal_80009828_call.link afterPublish where
  good := w.post.good
  image := w.post.image
  minstret := w.post.minstret
  raReg := (w.post.frame .x1 (by decide) (by decide)).trans w.allocation.leaf.raReg
  aligned := by decide
  tick := w.post.tick

/-- Reset returns from the first minor-table memset, after publishing the
fresh block and clearing all 56 of its bytes through the native routine. -/
structure ResetTableZeroed (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero : Config) : Prop where
  published : ResetTablePublished initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish
  run : Steps (Vsa.Densify.fillZero initial) afterZero
  post : EffectPost [12, 11, 1, 6, 14, 15, 13, 5]
    (memset56Memory afterPublish.σ.mem (vsaReg afterTable 10).toNat) afterPublish
    jal_80009844_call.link (BitVec.ofNat 64 (vsaReg afterTable 10).toNat) afterZero

theorem reset_table_zeroed_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero,
    ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, w⟩ :=
    reset_table_published_exists
  obtain ⟨afterZero, run, post⟩ := (table_zero afterPublish false _ _ w.allocation.region w.leaf
    (by
      change gpr afterPublish 10 = some (BitVec.ofNat 64 (vsaReg afterTable 10).toNat)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using w.post.result)).run afterPublish ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable,
    afterPublish, afterZero, w, w.run.trans run, post⟩

/-- The initialized table's concrete byte observations follow from the summary. -/
theorem ResetTableZeroed.zero_bytes {afterZero : Config}
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero)
    (i : Nat) (hi : i < 56) :
    afterZero.σ.mem[(vsaReg afterTable 10).toNat + i]? = some 0#8 := by
  rw [w.post.memory]
  exact memset56Memory_inside w.published.allocation.region _ _ (by omega) (by omega)
end OCaml.Vm.Boot.WhileMinElfParse
