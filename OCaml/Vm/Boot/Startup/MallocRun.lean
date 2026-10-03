import OCaml.Vm.Boot.Startup.MallocFirstResult
import OCaml.Vm.Boot.Startup.AllocatorImage
import OCaml.Vm.Primitives.LibraryFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

def startupLive (a : Nat) : Prop :=
  Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Densify.ramBase + Vsa.Densify.ramSize

def firstMallocStack : BitVec 64 := WhileMinElfParse.camlMainStack - 112#64 - 16#64

def firstMallocSaved (R : Nat → BitVec 64) : List (Nat × BitVec 64) :=
  vsaSaved.map (fun n => (n, R n))

theorem firstMallocSaved_keys (R : Nat → BitVec 64) :
    (firstMallocSaved R).map Prod.fst = vsaSaved := rfl

theorem firstMallocSaved_values (R : Nat → BitVec 64) :
    ∀ p ∈ firstMallocSaved R, R p.1 = p.2 := by
  intro p hp
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem startup_alloc_live : AllocLive startupLive := by
  intro p hp
  have bounds := (allocator_sources p hp).geometry
  exact ⟨bounds.low, Nat.lt_trans bounds.high (by decide)⟩

theorem firstMalloc_separate :
    LocalSeparation roR allocText aRegs (mS [] firstMallocStack) where
  registers := by decide
  bytes := by
    intro p hp owned
    have bounds := (allocator_sources p hp).geometry
    change VsaIris.stackWin firstMallocStack allocHeadroom p.1 ∨ vsaFoot [] p.1 at owned
    rcases owned with stack | global | heap
    · have hi := bounds.high
      change Layout.sym_stack_top - 656 ≤ p.1 ∧ _ at stack
      unfold heapStart Layout.sym_stack_top at *
      omega
    · exact bounds.outsideGlobals global
    · exact Nat.not_le_of_lt bounds.high heap.1

theorem startup_foot_live {H : List (Nat × Nat)} {a : Nat} (ha : vsaFoot H a) :
    startupLive a := by
  unfold vsaFoot allocGlobal InRange heapStart heapEnd at ha
  unfold startupLive Vsa.Densify.ramBase Vsa.Densify.ramSize
  omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap Startup
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

theorem ResetMallocWitness.symbolic_input {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) :
    SymbolicInput startupLive allocText aRegs (mS [] firstMallocStack)
      (vsaReg atMalloc) atMalloc.σ.mem atMalloc where
  good := w.vsaOk _ (fun _ h => h)
  readOnly := by
    constructor
    · intro p hp
      have eq : p = (3, gpV) := by simpa only [roR, VsaIris.gp, List.mem_singleton] using hp
      subst p
      change (gprGet atMalloc.σ 3).getD 0 = gpV
      rw [w.gp]
      rfl
    · intro p hp
      change (atMalloc.σ.mem[p.1]?).getD 0 = p.2
      rw [w.allocator_loaded p hp]
      rfl
  registers := fun _ _ _ => rfl
  memory := fun _ _ => rfl

theorem ResetMallocWitness.entry_regs {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) :
    EntryRegs (vsaReg atMalloc) mallocEntryBV jal_8002a8e8_call.link 928#64 firstMallocStack
      (firstMallocSaved (vsaReg atMalloc)) := by
  constructor
  · change (pcOf atMalloc).getD 0 = mallocEntryBV
    rw [w.post.pc]; rfl
  · change (gprGet atMalloc.σ 1).getD 0 = _
    rw [w.post.raReg]; rfl
  · change (gprGet atMalloc.σ 10).getD 0 = _
    rw [w.request]; rfl
  · change (gprGet atMalloc.σ 2).getD 0 = _
    rw [w.stack]; rfl
  · exact firstMallocSaved_values _
/-- The actual first malloc reaches its caller using the symbolic bootstrap
summary and the run kernel; no startup execution is evaluated in the kernel. -/
theorem ResetMallocWitness.malloc_run {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) :
    FnSummary mallocEntryBV (fun c => c = atMalloc)
      (LocalPost startupLive roR allocText aRegs (mS [] firstMallocStack)
        (FirstMallocEnd jal_8002a8e8_call.link firstMallocStack
          (firstMallocSaved (vsaReg atMalloc))) atMalloc) := by
  let C := firstMallocCtx startupLive jal_8002a8e8_call.link firstMallocStack
    (firstMallocSaved (vsaReg atMalloc)) (vsaReg atMalloc) atMalloc.σ.mem
  have entry := w.entry_regs
  have ok : MOK C := firstMalloc_ok startup_alloc_live (firstMallocSaved_keys _)
    (by constructor <;> decide) (by decide) entry
  have regs : MRegs C (vsaReg atMalloc) :=
    ⟨entry.ra, entry.sp, rfl, rfl, rfl, rfl⟩
  apply symbolic_summary atMalloc firstMalloc_separate w.symbolic_input
  exact malloc_bootstrap_entry ok regs entry.a0 w.initial_arena rfl (by change heapEnd + mHead ≤ firstMallocStack.toNat; decide) rfl rfl
    (fun a ha => w.symbolic_input.good.live a (startup_foot_live ha))

/-- Extend the closed reset execution through the first allocator return. -/
structure ResetFirstAllocation (initial atMain atDomain atAlloc atMalloc after : Config) : Prop where
  before : ResetMallocWitness initial atMain atDomain atAlloc atMalloc
  run : Steps (Vsa.Densify.fillZero initial) after
  post : LocalPost startupLive roR allocText aRegs (mS [] firstMallocStack)
    (FirstMallocEnd jal_8002a8e8_call.link firstMallocStack
      (firstMallocSaved (vsaReg atMalloc))) atMalloc after

theorem reset_first_allocation_exists : ∃ initial atMain atDomain atAlloc atMalloc after,
    ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, w⟩ := reset_malloc_exists
  obtain ⟨after, run, post⟩ := w.malloc_run.run atMalloc ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, after, w, w.run.trans run, post⟩
end OCaml.Vm.Boot.WhileMinElfParse
