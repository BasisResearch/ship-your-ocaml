import OCaml.Vm.Boot.Startup.TableNextReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim VsaIris.Inst OCaml.Vm.Primitives

/-- The second table's allocation, publication and initialization certificates,
with intermediate states kept as data inside the existential summary result. -/
structure TableNextInitialized (H : List (Nat × Nat)) (capacity : Nat) (before after : Config) where
  allocated : Config
  published : Config
  allocation : TableNextAllocated H capacity false before allocated
  publication : WriteRegistersPost [15, 10] (tablePublishLog .ephemerons (vsaReg allocated 10)) allocated
    MinorTableSlot.ephemerons.exit (vsaReg allocated 10) (tablePublishRegs (vsaReg allocated 10)) published
  zeroing : RegistersPost [12, 11, 1, 6, 14, 15, 13, 5]
    (memset56Memory published.σ.mem (vsaReg allocated 10).toNat) published
    (tableZeroCall true).link (BitVec.ofNat 64 (vsaReg allocated 10).toNat)
    (tableZeroFinalRegs true (vsaReg allocated 10).toNat) after

/-- The complete second-table round, reusable for any preceding live heap. -/
theorem table_next_initialize (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (ra : BitVec 64)
    (ready : TableReady H (capacity + 64) ra c) :
    FnSummary (tableNextEntry false) (fun d => d = c)
      (fun after => Nonempty (TableNextInitialized H capacity c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨allocated, allocationRun, ⟨allocation⟩⟩ := (table_next_allocate c false H capacity ra ready).run c ⟨pc, rfl⟩
  obtain ⟨published, publicationRun, publication⟩ :=
    (table_publish allocated .ephemerons _ _ (allocation.publishInput ready)).run allocated ⟨allocation.pc, rfl⟩
  have leaf : LeafInput (tableNextCall false).link published :=
    ⟨publication.good, publication.image, publication.minstret,
      (publication.frame .x1 (by decide) (by decide)).trans allocation.leaf.raReg,
      by decide, publication.tick⟩
  have pointer : gprGet published.σ 10 = some (BitVec.ofNat 64 (vsaReg allocated 10).toNat) := by
    change gpr published 10 = _
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using publication.result
  obtain ⟨after, zeroRun, zeroing⟩ := (table_zero_registers published true _ _ allocation.region leaf pointer).run published
    ⟨publication.pc, rfl⟩
  exact ⟨after, allocationRun.trans (publicationRun.trans zeroRun), ⟨allocated, published, allocation, publication, zeroing⟩⟩

/-- The full second round retains the common contract needed by the third. -/
theorem TableNextInitialized.ready {H capacity before after ra}
    (w : TableNextInitialized H capacity before after) (ready : TableReady H (capacity + 64) ra before)
    (domain : (firstDomainPtr.toNat, 928) ∈ H) :
    TableReady (((vsaReg w.allocated 10).toNat, 56) :: H) capacity (tableZeroCall true).link after := by
  have allocated := w.allocation.ready ready
  have published := allocated.publish (List.mem_cons_of_mem _ domain) w.publication
  exact published.zero w.allocation.region (List.mem_cons_self ..) w.zeroing
end OCaml.Vm.Boot.Startup
