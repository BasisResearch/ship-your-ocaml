import OCaml.Vm.Boot.Startup.MinorTablesPrefix
import OCaml.Vm.Boot.Startup.AllocatorRun
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap
open OCaml.Vm.Primitives

/-- The pooling switch is an ordinary runtime global, outside every allocator
ownership window used by startup. -/
theorem pool_allocator_outside (H : List (Nat × Nat)) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) (i : Nat) (hi : i < 8) :
    ¬ mS H s (Layout.sym_pool + i) := by
  change ¬ (stackWin s allocHeadroom _ ∨ vsaFoot H _)
  unfold stackWin InExt vsaFoot allocGlobal InRange
  simp only [Layout.sym_pool, allocHeadroom, heapStart, heapEnd] at *
  omega

/-- A confined allocator call preserves the disabled-pooling test. -/
theorem allocator_pool_zero {H s Q before after}
    (post : LocalPost startupLive VsaIris.MallocFast.roR VsaIris.Sym.allocText
      VsaIris.Sym.aRegs (mS H s) Q before after)
    (high : heapEnd + allocHeadroom ≤ s.toNat)
    (pins : LPins8 before.σ.mem Layout.sym_pool (List.replicate 8 0#8)) :
    LPins8 after.σ.mem Layout.sym_pool (List.replicate 8 0#8) :=
  lpins8_observed pins fun i hi => post.memory _ (pool_allocator_outside H s high i hi)
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

theorem ResetFirstAllocation.pool_zero {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    LPins8 after.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  apply allocator_pool_zero w.post (by decide)
  rw [w.before.post.memory]
  exact w.before.alloc.pool_zero

theorem ResetMinorTables.pool_zero {initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config}
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    LPins8 atTables.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  apply lpins8_observed w.allocation.pool_zero
  intro i hi
  rw [w.post.memory, frameOn_writeLog _ _ _ domainInit_log_inside]
  change (Layout.sym_pool + i < Layout.sym_Caml_state ∨ _) ∧
    (Layout.sym_pool + i < firstDomainPtr.toNat ∨ _) ∧ True
  have bounds : Layout.sym_pool + 8 ≤ Layout.sym_Caml_state ∧
      Layout.sym_pool + 8 ≤ firstDomainPtr.toNat := by decide
  exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩

theorem ResetTableAlloc.pool_zero {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config}
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest) :
    LPins8 atRequest.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  rw [w.post.memory]
  apply lpins8_writeLog w.tables.pool_zero
  simp only [minorTablesLog, OutLRange]
  decide
end OCaml.Vm.Boot.WhileMinElfParse
