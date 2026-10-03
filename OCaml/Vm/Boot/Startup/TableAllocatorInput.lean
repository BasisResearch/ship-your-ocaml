import OCaml.Vm.Boot.Startup.PoolFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap
open OCaml.Vm.Primitives

/-- Allocator metadata and managed payloads all lie below the startup stack. -/
theorem allocator_foot_below {H a} (ha : vsaFoot H a) : a < heapEnd := by
  unfold vsaFoot allocGlobal InRange heapStart heapEnd at *
  omega

theorem minorTables_log_outside (s0 s1 : BitVec 64) (a : Nat) (below : a < heapEnd) :
    OutL (minorTablesLog s0 s1) a := by
  have bounds : heapEnd ≤ firstMallocStack.toNat - 24 := by decide
  simp only [minorTablesLog, OutL]
  exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), trivial⟩

/-- The disabled-pool wrapper only changes x15 and preserves every other
input needed by the successful allocator contract. -/
theorem statAlloc_allocator_input {H n r s capacity before after}
    (input : AllocatorInput H n r s capacity before)
    (post : BoundaryPost [15] before r (BitVec.ofNat 64 Layout.sym_malloc) [(15, 0#64)] after) :
    AllocatorInput H n r s capacity after where
  good := by
    have present : GprPresent before.σ := ⟨fun n lo hi => input.good.gpr n lo (by omega)⟩
    have afterPins := present.of_regs_ne (writes := [15]) (by decide) post.regs
      (by simp only [keysG]; decide) post.frame
    refine ⟨post.good, post.tick, fun n lo hi => afterPins.get n lo (by omega), ?_, ?_⟩
    · intro a ha
      rw [post.memory]
      exact input.good.live a ha
    · exact (post.frame .htif_payload_writes (by decide) (by decide)).trans input.good.htifIdle
  readOnly := by
    apply readonly_transport input.readOnly
    · intro p hp
      have eq : p = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
      subst p
      change (gprGet after.σ 3).getD 0 = (gprGet before.σ 3).getD 0
      rw [show gprGet after.σ 3 = gprGet before.σ 3 from post.frame .x3 (by decide) (by decide)]
    · intro a
      change (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
      rw [post.memory]
  room := by
    change vsaRoomB (fun a => (after.σ.mem[a]?).getD 0) H capacity
    rw [post.memory]
    exact input.room
  request := (post.frame .x10 (by decide) (by decide)).trans input.request
  stack := (post.frame .x2 (by decide) (by decide)).trans input.stack
  link := post.raReg
  stackOk := input.stackOk
  high := input.high
  aligned := input.aligned
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem ResetTableAlloc.vsaOk {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config}
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest) :
    VsaOk startupLive atRequest :=
  w.post.vsaOk w.tables.vsaOk (by decide)
    (by simp only [keysG, minorTablesCallRegs, minorTablesRegs, List.take]; decide)

theorem ResetTableAlloc.readOnly {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config}
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest) :
    ROHolds (vsaModel startupLive) atRequest VsaIris.MallocFast.roR VsaIris.Sym.allocText := by
  apply w.post.toEffectPost.readOnly_log (by decide) (by decide) w.tables.readOnly
  intro p hp
  have bounds := (allocator_sources p hp).geometry
  exact minorTables_log_outside _ _ _ (Nat.lt_trans bounds.high (by decide))

theorem ResetTableAlloc.room {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config}
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest)
    (k : Nat) (cap : 2 * k + extendSlack ≤ heapEnd - (heapStart + 944)) :
    vsaRoomB ((vsaModel startupLive).mem atRequest) firstDomainHeap k := by
  apply roomLocal_vsaRoomB firstDomainHeap _ _ k ?_ (w.tables.room k cap)
  intro a ha
  change (atTables.σ.mem[a]?).getD 0 = (atRequest.σ.mem[a]?).getD 0
  rw [w.post.memory, writeLog_out _ _ _ (minorTables_log_outside _ _ _ (allocator_foot_below ha))]

theorem ResetTableAlloc.allocatorInput {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config}
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest)
    (k : Nat) (cap : 2 * k + extendSlack ≤ heapEnd - (heapStart + 944)) :
    AllocatorInput firstDomainHeap 56#64 jal_80009828_call.link (firstMallocStack - 32#64) k atRequest where
  good := w.vsaOk
  readOnly := w.readOnly
  room := w.room k cap
  request := w.post.result
  stack := gholds_lookup _ w.post.regs (by rfl)
  link := gholds_lookup _ w.post.regs (by rfl)
  stackOk := by constructor <;> decide
  high := by decide
  aligned := by decide
end OCaml.Vm.Boot.WhileMinElfParse
