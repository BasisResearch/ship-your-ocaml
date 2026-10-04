import OCaml.Vm.Boot.Startup.RuntimeReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

/-- A landed successful malloc contract returns the same runtime interface,
with its fresh allocation included and the library's remaining capacity. -/
theorem RuntimeReady.malloc_result {H capacity remaining n sp ra before after}
    (ready : RuntimeReady H capacity sp ra before)
    (high : heapEnd + allocHeadroom ≤ sp.toNat)
    (post : LocalPost startupLive roR VsaIris.Sym.allocText VsaIris.Sym.aRegs (mS H sp)
      (MallocRoomEnd vsaLayoutP vsaRoomB H n ra sp (firstMallocSaved (vsaReg before)) remaining) before after) :
    RuntimeReady (((vsaReg after 10).toNat, n.toNat) :: H) remaining sp ra after where
  good := post.good.good
  image := image_local ready.image post.good startup_image_live
    (allocator_image_separate _ _ high) post.memory
  minstret := post.good.good.minstret
  raReg := library_gpr post.good (by decide) (by decide) post.result.frame.ra
  aligned := ready.aligned
  tick := post.good.tick
  platform := post.good
  readOnly := post.readOnly
  room := post.result.room
  stack := library_gpr post.good (by decide) (by decide) post.result.frame.sp
  domainWord := by
    rw [word_observed (m := before.σ.mem) Layout.sym_Caml_state
      (fun i hi => post.memory _ (domain_allocator_outside _ _ high i hi))]
    exact ready.domainWord
  poolZero := allocator_pool_zero post high ready.poolZero

/-- Library scratch is below its entry stack pointer; caller native slots above
that boundary are disjoint from both scratch and allocator ownership. -/
theorem allocator_caller_outside {H sp a} (high : heapEnd + allocHeadroom ≤ sp.toNat)
    (caller : sp.toNat ≤ a) : ¬ mS H sp a := by
  change ¬ (stackWin sp allocHeadroom a ∨ vsaFoot H a)
  intro owned
  rcases owned with scratch | heap
  · unfold stackWin InExt at scratch
    omega
  · have below := allocator_foot_below heap
    omega
end OCaml.Vm.Boot.Startup
