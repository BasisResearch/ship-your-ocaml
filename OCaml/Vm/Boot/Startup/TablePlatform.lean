import OCaml.Vm.Boot.Startup.TableZeroed
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero : Config}

theorem ResetTablePublished.vsaOk
    (w : ResetTablePublished initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish) :
    VsaOk startupLive afterPublish :=
  w.post.vsaOk w.allocation.post.good (by decide)
    (by simp only [keysG, tablePublishRegs]; decide)

/-- Exact zeroing and the retained output interface establish the complete
library platform invariant at the next startup allocation boundary. -/
theorem ResetTableZeroed.vsaOk
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    VsaOk startupLive afterZero := by
  apply w.post.vsaOk_of_present w.published.vsaOk (by decide)
    (by simp only [keysG, tableZeroFinalRegs, memset56Regs]; decide)
  intro a ha
  rw [w.post.memory]
  by_cases inside : (vsaReg afterTable 10).toNat ≤ a ∧ a < (vsaReg afterTable 10).toNat + 56
  · rw [memset56Memory_inside w.published.allocation.region _ a inside.1 inside.2]
    rfl
  · rw [memset56Memory_out w.published.allocation.region _ a (by omega)]
    exact w.published.vsaOk.live a ha
end OCaml.Vm.Boot.WhileMinElfParse
