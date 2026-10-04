import OCaml.Vm.Boot.Startup.TableNextReturn
import OCaml.Vm.Boot.Startup.TableReadyEffects
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- A successful table malloc retains readiness with the fresh block added to
the live heap and the charged capacity recorded in its library result. -/
theorem TableNextAllocated.ready {H capacity last before after ra}
    (w : TableNextAllocated H capacity last before after) (ready : TableReady H (capacity + 64) ra before) :
    TableReady (((vsaReg after 10).toNat, 56) :: H) capacity (tableNextCall last).link after where
  toLeafInput := w.leaf
  platform := w.allocation.good
  readOnly := w.allocation.readOnly
  room := w.allocation.result.room
  stack := library_gpr w.allocation.good (by decide) (by decide) w.allocation.result.frame.sp
  globalReg := (w.publishInput ready).globalReg
  domainWord := w.domain_word ready
  poolZero := by
    apply allocator_pool_zero w.allocation (by decide)
    rw [w.dispatch.memory, w.setup.memory]
    exact ready.poolZero
end OCaml.Vm.Boot.Startup
