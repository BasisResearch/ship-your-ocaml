import OCaml.Vm.Boot.Startup.TableHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Common startup inputs at the two remaining minor-table allocation sites.
The heap and remaining capacity vary; the source function's frame is fixed. -/
structure TableReady (H : List (Nat × Nat)) (capacity : Nat) (ra : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  platform : VsaOk startupLive c
  readOnly : ROHolds (vsaModel startupLive) c VsaIris.MallocFast.roR VsaIris.Sym.allocText
  room : vsaRoomB ((vsaModel startupLive).mem c) H capacity
  stack : gprGet c.σ 2 = some (firstMallocStack - 32#64)
  globalReg : gprGet c.σ 8 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  domainWord : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr
  poolZero : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero : Config}

theorem ResetTableZeroed.domain_word
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    bytesT afterZero.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr := by
  have lower := w.published.allocation.region.lower
  have before := w.published.allocation.domain_word
  rw [word_observed (m := afterPublish.σ.mem) Layout.sym_Caml_state (fun i hi => by
    rw [w.post.memory, memset56Memory_out w.published.allocation.region _ _ (Or.inl (by
      unfold heapStart Layout.sym_Caml_state at *; omega))]), w.published.post.memory,
    bytesT_writeLog_out _ (show OutLRange _ Layout.sym_Caml_state 8 from by
      simp only [tablePublishLog, OutLRange]; decide)]
  exact before

theorem ResetTableZeroed.pool_zero
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    LPins8 afterZero.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  have atMalloc : LPins8 atTableMalloc.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
    rw [w.published.allocation.before.post.memory]
    exact w.published.allocation.before.request.pool_zero
  have allocated := allocator_pool_zero w.published.allocation.post (by decide) atMalloc
  have published : LPins8 afterPublish.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
    rw [w.published.post.memory]
    exact lpins8_writeLog allocated (by simp only [tablePublishLog, OutLRange]; decide)
  apply lpins8_observed published
  intro i hi
  have lower := w.published.allocation.region.lower
  rw [w.post.memory, memset56Memory_out w.published.allocation.region _ _ (Or.inl (by
    unfold heapStart Layout.sym_pool at *; omega))]

/-- The actual first-table return supplies every input required by the next
allocation, without assuming fresh platform or allocator facts. -/
theorem ResetTableZeroed.ready
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    TableReady (firstTableHeap (vsaReg afterTable 10)) (startupAllocatorCredits - 64) jal_80009844_call.link afterZero where
  good := w.post.good
  image := w.post.image
  minstret := w.post.minstret
  raReg := gholds_lookup _ w.post.regs (by rfl)
  aligned := by decide
  tick := w.post.tick
  platform := w.vsaOk
  readOnly := w.readOnly
  room := w.room
  stack := (w.post.frame .x2 (by decide) (by decide)).trans ((w.published.post.frame .x2 (by decide) (by decide)).trans
    (library_gpr w.published.allocation.post.good (by decide) (by decide) w.published.allocation.post.result.frame.sp))
  globalReg := (w.post.frame .x8 (by decide) (by decide)).trans ((w.published.post.frame .x8 (by decide) (by decide)).trans
    w.published.allocation.publishInput.globalReg)
  domainWord := w.domain_word
  poolZero := w.pool_zero
end OCaml.Vm.Boot.WhileMinElfParse
