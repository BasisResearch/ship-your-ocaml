import OCaml.Vm.Boot.Startup.TableAllocatorInput
namespace OCaml.Vm.Boot.Startup
open Vsa.Sim.DlHeap VsaIris.VsaHeap

/-- Credits justified by the initial allocation's exact top bound. -/
def startupAllocatorCredits : Nat := (heapEnd - (heapStart + 944) - extendSlack) / 2

theorem startupAllocatorCredits_capacity :
    2 * startupAllocatorCredits + extendSlack ≤ heapEnd - (heapStart + 944) := by decide

theorem startupTable_capacity :
    2 * (startupAllocatorCredits - 64 + 64) + extendSlack ≤ heapEnd - (heapStart + 944) := by decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap
open VsaIris.Sym VsaIris.MallocFast OCaml.Vm.Primitives

structure ResetTableMalloc (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc : Config) : Prop where
  request : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest
  run : Steps (Vsa.Densify.fillZero initial) atTableMalloc
  post : BoundaryPost [15] atRequest jal_80009828_call.link
    (BitVec.ofNat 64 Layout.sym_malloc) [(15, 0#64)] atTableMalloc

theorem ResetTableMalloc.allocatorInput {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc : Config}
    (w : ResetTableMalloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc)
    (k : Nat) (cap : 2 * k + extendSlack ≤ heapEnd - (heapStart + 944)) :
    AllocatorInput firstDomainHeap 56#64 jal_80009828_call.link (firstMallocStack - 32#64) k atTableMalloc :=
  statAlloc_allocator_input (w.request.allocatorInput k cap) w.post

theorem reset_table_malloc_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc,
    ResetTableMalloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, w⟩ := reset_table_alloc_exists
  have leaf : LeafInput jal_80009828_call.link atRequest :=
    ⟨w.post.good, w.post.image, w.post.minstret, gholds_lookup _ w.post.regs (by rfl), by decide, w.post.tick⟩
  obtain ⟨atTableMalloc, run, post⟩ :=
    (statAlloc_dispatch atRequest _ leaf w.pool_zero).run atRequest ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc,
    w, w.run.trans run, post⟩

/-- The next malloc returns a fresh aligned table, retaining quantified
allocator capacity and the existing domain allocation. -/
structure ResetTableAllocation (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable : Config) : Prop where
  before : ResetTableMalloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc
  run : Steps (Vsa.Densify.fillZero initial) afterTable
  post : LocalPost startupLive roR allocText aRegs (mS firstDomainHeap (firstMallocStack - 32#64))
    (MallocRoomEnd vsaLayoutP vsaRoomB firstDomainHeap 56#64 jal_80009828_call.link (firstMallocStack - 32#64)
      (firstMallocSaved (vsaReg atTableMalloc)) (startupAllocatorCredits - 64)) atTableMalloc afterTable

theorem reset_table_allocation_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable,
    ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, w⟩ :=
    reset_table_malloc_exists
  have input := w.allocatorInput _ startupTable_capacity
  obtain ⟨afterTable, run, post⟩ :=
    (allocator_summary atTableMalloc firstDomainHeap 56#64 jal_80009828_call.link (firstMallocStack - 32#64)
      (startupAllocatorCredits - 64) 64 input (by constructor <;> decide)).run atTableMalloc ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable,
    w, w.run.trans run, post⟩
end OCaml.Vm.Boot.WhileMinElfParse
