import OCaml.Vm.Boot.Startup.DomainInit
import OCaml.Vm.Primitives.LibraryEffects
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap
open OCaml.Vm.Primitives

def firstDomainHeap : List (Nat × Nat) := [(firstDomainPtr.toNat, 928)]

/-- The published-domain word is outside allocator globals, and the payload
is excluded from the allocator's mutable metadata footprint. -/
theorem domainInit_heap_outside {a : Nat} (ha : vsaFoot firstDomainHeap a) :
    OutW domainInitWindows a := by
  have notPayload : ¬ (firstDomainPtr.toNat ≤ a ∧ a < firstDomainPtr.toNat + 928) := by
    rcases ha with global | heap
    · unfold allocGlobal InRange firstDomainPtr heapStart at *
      simp only [BitVec.toNat_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod]
      omega
    · exact heap.2.2 (firstDomainPtr.toNat, 928) (by simp [firstDomainHeap])
  have notGlobal : a < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ a := by
    unfold vsaFoot allocGlobal InRange firstDomainHeap firstDomainPtr heapStart at ha
    unfold Layout.sym_Caml_state
    omega
  change (a < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ a) ∧
    (a < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ a) ∧ True
  exact ⟨notGlobal, (by omega), trivial⟩

theorem domainInit_allocator_outside {p : Nat × BitVec 8}
    (hp : p ∈ VsaIris.Sym.allocText) : OutW domainInitWindows p.1 := by
  have source := allocator_sources p hp
  have bounds := source.geometry
  have global : p.1 + 1 ≤ Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ p.1 := by
    unfold AllocatorByteSource at source
    split at source <;>
      simp only [Image.textBase, Image.textSize, allocatorImpureAddr, Layout.sym_Caml_state] at * <;> omega
  change (p.1 < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ p.1) ∧
    (p.1 < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ p.1) ∧ True
  refine ⟨(by omega), Or.inl ?_, trivial⟩
  have hi := bounds.high
  change p.1 < heapStart + 16
  omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup
open VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem ResetMinorTables.vsaOk {initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config}
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    VsaOk startupLive atTables :=
  w.post.vsaOk w.allocation.post.good (by decide) (by simp only [keysG, domainInitRegs]; decide)

/-- Domain payload initialization retains every certified allocator byte. -/
theorem ResetMinorTables.readOnly {initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config}
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    ROHolds (vsaModel startupLive) atTables VsaIris.MallocFast.roR VsaIris.Sym.allocText := by
  constructor
  · intro p hp
    have same : p = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
    subst p
    exact (w.post.toEffectPost.observed_gpr (by decide) 3 (by decide) (by decide) (by decide)).trans
      (w.allocation.post.readOnly.1 _ hp)
  · intro p hp
    change (atTables.σ.mem[p.1]?).getD 0 = p.2
    rw [w.post.memory, frameOn_writeLog _ _ _ domainInit_log_inside _ (domainInit_allocator_outside hp)]
    exact w.allocation.post.readOnly.2 p hp

/-- The first allocator's capacity survives initialization stores in its payload. -/
theorem ResetMinorTables.room {initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config}
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables)
    (k : Nat) (cap : 2 * k + extendSlack ≤ heapEnd - (heapStart + 944)) :
    vsaRoomB ((vsaModel startupLive).mem atTables) firstDomainHeap k := by
  have before := w.allocation.post.result.room k cap
  have ptr := w.allocation.post.result.pointer
  change vsaReg afterMalloc 10 = firstDomainPtr at ptr
  change vsaRoomB ((vsaModel startupLive).mem afterMalloc) [((vsaReg afterMalloc 10).toNat, 928)] k at before
  rw [ptr] at before
  apply roomLocal_vsaRoomB firstDomainHeap _ _ k ?_ before
  intro a ha
  change (afterMalloc.σ.mem[a]?).getD 0 = (atTables.σ.mem[a]?).getD 0
  rw [w.post.memory, frameOn_writeLog _ _ _ domainInit_log_inside _ (domainInit_heap_outside ha)]
end OCaml.Vm.Boot.WhileMinElfParse
