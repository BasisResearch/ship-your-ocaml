import OCaml.Vm.Boot.Startup.TablePlatform
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Allocator ownership excludes every live payload listed in its heap shape. -/
theorem allocator_payload_outside {H : List (Nat × Nat)} {p n a : Nat}
    (member : (p, n) ∈ H) (lower : heapStart ≤ p) (owned : vsaFoot H a) :
    a < p ∨ p + n ≤ a := by
  rcases owned with global | heap
  · unfold allocGlobal InRange heapStart at *
    omega
  · have outside := heap.2.2 (p, n) member
    change ¬ (p ≤ a ∧ a < p + n) at outside
    omega

def firstTableHeap (p : BitVec 64) : List (Nat × Nat) := (p.toNat, 56) :: firstDomainHeap

theorem tablePublish_allocator_outside (slot : MinorTableSlot) (p : BitVec 64)
    {H : List (Nat × Nat)} {a : Nat} (domain : (firstDomainPtr.toNat, 928) ∈ H) (owned : vsaFoot H a) :
    OutL (tablePublishLog slot p) a := by
  have outside := allocator_payload_outside domain (by decide) owned
  have range : firstDomainPtr.toNat ≤ slot.address.toNat ∧
      slot.address.toNat + 8 ≤ firstDomainPtr.toNat + 928 := by cases slot <;> decide
  simp only [tablePublishLog, OutL]
  exact ⟨(by omega), trivial⟩

theorem tablePublish_pins_outside (slot : MinorTableSlot) (p : BitVec 64)
    {pin : Nat × BitVec 8} (member : pin ∈ VsaIris.Sym.allocText) :
    OutL (tablePublishLog slot p) pin.1 := by
  have high := (allocator_sources pin member).geometry.high
  have lower : heapStart ≤ slot.address.toNat := by cases slot <;> decide
  exact ⟨Or.inl (by omega), trivial⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero : Config}

theorem ResetTablePublished.room
    (w : ResetTablePublished initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish) :
    vsaRoomB ((vsaModel startupLive).mem afterPublish) (firstTableHeap (vsaReg afterTable 10)) (startupAllocatorCredits - 64) := by
  apply roomLocal_vsaRoomB _ _ _ _ ?_ w.allocation.post.result.room
  intro a owned
  change (afterTable.σ.mem[a]?).getD 0 = (afterPublish.σ.mem[a]?).getD 0
  rw [w.post.memory, writeLog_out _ _ _ (tablePublish_allocator_outside .refs _
    (by simp [firstTableHeap, firstDomainHeap]) owned)]

theorem ResetTableZeroed.room
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    vsaRoomB ((vsaModel startupLive).mem afterZero) (firstTableHeap (vsaReg afterTable 10)) (startupAllocatorCredits - 64) := by
  apply roomLocal_vsaRoomB _ _ _ _ ?_ w.published.room
  intro a owned
  change (afterPublish.σ.mem[a]?).getD 0 = (afterZero.σ.mem[a]?).getD 0
  rw [w.post.memory, memset56Memory_out w.published.allocation.region _ a
    (allocator_payload_outside (by simp [firstTableHeap]) w.published.allocation.region.lower owned)]

theorem ResetTablePublished.readOnly
    (w : ResetTablePublished initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish) :
    ROHolds (vsaModel startupLive) afterPublish VsaIris.MallocFast.roR VsaIris.Sym.allocText :=
  w.post.toEffectPost.readOnly_log (by decide) (by decide) w.allocation.post.readOnly
    (fun _ hp => tablePublish_pins_outside _ _ hp)

theorem ResetTableZeroed.readOnly
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    ROHolds (vsaModel startupLive) afterZero VsaIris.MallocFast.roR VsaIris.Sym.allocText := by
  constructor
  · intro pin hp
    have eq : pin = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
    subst pin
    exact (w.post.toEffectPost.observed_gpr (by decide) 3 (by decide) (by decide) (by decide)).trans
      (w.published.readOnly.1 _ hp)
  · intro pin hp
    have high := (allocator_sources pin hp).geometry.high
    have lower := w.published.allocation.region.lower
    change (afterZero.σ.mem[pin.1]?).getD 0 = pin.2
    rw [w.post.memory, memset56Memory_out w.published.allocation.region _ pin.1 (Or.inl (by omega))]
    exact w.published.readOnly.2 pin hp
end OCaml.Vm.Boot.WhileMinElfParse
