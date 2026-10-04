import OCaml.Vm.Boot.Startup.TableNextInitialize
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim VsaIris.Inst OCaml.Vm.Primitives

/-- The second initialized table followed by the third successful allocation. -/
structure TableFinalAllocated (H : List (Nat × Nat)) (capacity : Nat) (before after : Config) where
  middle : Config
  initialized : TableNextInitialized H (capacity + 64) before middle
  allocation : TableNextAllocated (((vsaReg initialized.allocated 10).toNat, 56) :: H) capacity true middle after

/-- Reuse the abstract second-table round and remaining allocation call site. -/
theorem table_final_allocate (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (ra : BitVec 64)
    (ready : TableReady H (capacity + 128) ra c) (domain : (firstDomainPtr.toNat, 928) ∈ H) :
    FnSummary (tableNextEntry false) (fun d => d = c)
      (fun after => Nonempty (TableFinalAllocated H capacity c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have ready' : TableReady H ((capacity + 64) + 64) ra c := by
    simpa only [Nat.add_assoc] using ready
  obtain ⟨middle, firstRun, ⟨initialized⟩⟩ := (table_next_initialize c H (capacity + 64) ra ready').run c ⟨pc, rfl⟩
  have next := initialized.ready ready' domain
  obtain ⟨after, lastRun, ⟨allocation⟩⟩ := (table_next_allocate middle true _ capacity _ next).run middle
    ⟨initialized.zeroing.pc, rfl⟩
  exact ⟨after, firstRun.trans lastRun, ⟨middle, initialized, allocation⟩⟩

/-- All allocation inputs survive into the third table's publication boundary. -/
theorem TableFinalAllocated.ready {H capacity before after ra}
    (w : TableFinalAllocated H capacity before after) (ready : TableReady H (capacity + 128) ra before)
    (domain : (firstDomainPtr.toNat, 928) ∈ H) :
    TableReady (((vsaReg after 10).toNat, 56) :: ((vsaReg w.initialized.allocated 10).toNat, 56) :: H)
      capacity (tableNextCall true).link after := by
  have ready' : TableReady H ((capacity + 64) + 64) ra before := by
    simpa only [Nat.add_assoc] using ready
  exact w.allocation.ready (w.initialized.ready ready' domain)
end OCaml.Vm.Boot.Startup
