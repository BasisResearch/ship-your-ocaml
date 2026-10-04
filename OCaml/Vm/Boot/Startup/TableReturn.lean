import OCaml.Vm.Boot.Startup.TableAllocation
import OCaml.Vm.Boot.Startup.MemsetReadback
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- The published domain global is outside allocator metadata and scratch. -/
theorem domain_allocator_outside (H : List (Nat × Nat)) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) (i : Nat) (hi : i < 8) :
    ¬ mS H s (Layout.sym_Caml_state + i) := by
  change ¬ (stackWin s allocHeadroom _ ∨ vsaFoot H _)
  unfold stackWin InExt vsaFoot allocGlobal InRange
  simp only [Layout.sym_Caml_state, allocHeadroom, heapStart, heapEnd] at *
  omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable : Config}

theorem ResetTableAllocation.pc
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable) :
    PCAt jal_80009828_call.link afterTable := library_pc w.post.good w.post.result.frame.pc

theorem ResetTableAllocation.image
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable) :
    ExecutableImage afterTable :=
  image_local w.before.post.image w.post.good startup_image_live
    (allocator_image_separate _ _ (by decide)) w.post.memory

theorem ResetTableAllocation.leaf
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable) :
    LeafInput jal_80009828_call.link afterTable where
  good := w.post.good.good
  image := w.image
  minstret := w.post.good.good.minstret
  raReg := library_gpr w.post.good (by decide) (by decide) w.post.result.frame.ra
  aligned := by decide
  tick := w.post.good.tick

theorem ResetTableAllocation.region
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable) :
    Memset56Region (vsaReg afterTable 10).toNat :=
  ⟨w.post.result.fresh.lo, w.post.result.fresh.hi, w.post.result.align⟩

/-- Saved registers retain the published-domain address and original allocation. -/
theorem ResetTableAllocation.saved
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable)
    (n : Nat) (hn : n ∈ [8, 9]) :
    gprGet afterTable.σ n = gprGet atRequest.σ n := by
  have choices : n = 8 ∨ n = 9 := by simpa using hn
  have range : 1 ≤ n ∧ n ≤ 31 := by omega
  have saved := w.post.result.frame.saved (n, vsaReg atTableMalloc n)
    (by rcases choices with eq | eq <;> subst n <;> simp [firstMallocSaved, vsaSaved])
  have same : gprGet afterTable.σ n = gprGet atTableMalloc.σ n :=
    library_register_frame (w.before.allocatorInput _ startupTable_capacity).good
      w.post.good range.1 range.2 saved
  apply same.trans
  rcases choices with eq | eq <;> subst n
  all_goals exact w.before.post.frame _ (by decide) (by decide)
end OCaml.Vm.Boot.WhileMinElfParse
