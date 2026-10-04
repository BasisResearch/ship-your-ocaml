import OCaml.Vm.Boot.Startup.TableNextAllocate
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {H : List (Nat × Nat)} {capacity : Nat} {last : Bool} {before after : Config}

theorem TableNextAllocated.pc (w : TableNextAllocated H capacity last before after) :
    PCAt (tableNextCall last).link after := library_pc w.allocation.good w.allocation.result.frame.pc

theorem TableNextAllocated.image (w : TableNextAllocated H capacity last before after) : ExecutableImage after :=
  image_local w.dispatch.image w.allocation.good startup_image_live
    (allocator_image_separate _ _ (by decide)) w.allocation.memory

theorem TableNextAllocated.leaf (w : TableNextAllocated H capacity last before after) :
    LeafInput (tableNextCall last).link after where
  good := w.allocation.good.good
  image := w.image
  minstret := w.allocation.good.good.minstret
  raReg := library_gpr w.allocation.good (by decide) (by decide) w.allocation.result.frame.ra
  aligned := by cases last <;> decide
  tick := w.allocation.good.tick

theorem TableNextAllocated.region (w : TableNextAllocated H capacity last before after) :
    Memset56Region (vsaReg after 10).toNat :=
  ⟨w.allocation.result.fresh.lo, w.allocation.result.fresh.hi, w.allocation.result.align⟩

theorem TableNextAllocated.saved {ra} (w : TableNextAllocated H capacity last before after)
    (ready : TableReady H (capacity + 64) ra before) (n : Nat) (hn : n ∈ [8, 9]) :
    gprGet after.σ n = gprGet w.request.σ n := by
  have choices : n = 8 ∨ n = 9 := by simpa using hn
  have input := statAlloc_allocator_input (table_next_allocator_input ready w.setup) w.dispatch
  have same := allocator_saved_register input.good w.allocation.good w.allocation.result.frame n
    (by rcases choices with eq | eq <;> subst n <;> simp [vsaSaved])
  apply same.trans
  rcases choices with eq | eq <;> subst n
  all_goals exact w.dispatch.frame _ (by decide) (by decide)

theorem TableNextAllocated.domain_word {ra} (w : TableNextAllocated H capacity last before after)
    (ready : TableReady H (capacity + 64) ra before) :
    bytesT after.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr := by
  rw [word_observed (m := w.atMalloc.σ.mem) Layout.sym_Caml_state
    (fun i hi => w.allocation.memory _ (domain_allocator_outside _ _ (by decide) i hi)),
    w.dispatch.memory, w.setup.memory]
  exact ready.domainWord

/-- The abstract successful allocation supplies the shared publication protocol. -/
theorem TableNextAllocated.publishInput {ra} (w : TableNextAllocated H capacity last before after)
    (ready : TableReady H (capacity + 64) ra before) :
    TablePublishInput (vsaReg after 10) (tableNextCall last).link after where
  toLeafInput := w.leaf
  globalReg := (w.saved ready 8 (by decide)).trans (gholds_lookup (n := 8) _ w.setup.regs (by rfl))
  pointer := library_gpr w.allocation.good (by decide) (by decide) rfl
  domain := (w.saved ready 9 (by decide)).trans (gholds_lookup (n := 9) _ w.setup.regs (by rfl))
  domainWord := w.domain_word ready
  nonzero := fun eq => w.allocation.result.fresh.nonzero (congrArg BitVec.toNat eq)
end OCaml.Vm.Boot.Startup
