import OCaml.Vm.Gc.FreshAllocator
import OCaml.Vm.Gc.AllocIndirect

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Actual entry to the loaded free-list callee, with its new return link
and both oldify/allocator native save frames retained. -/
structure FreeListEntry (R : Nat → BitVec 64) (target : BitVec 64) (before after : Config) : Prop
    extends FreeListBoundary R target before after target
      (AllocEntry.callRegs (allocatorRegs R before) target) where
  link : gprGet after.σ 1 = some AllocEntry.returnPc

/-- Splice the actual indirect call into the completed fresh prefix. -/
theorem FreeListBoundary.enter {R target before middle}
    (post : FreeListBoundary R target before middle) (aligned : target.toNat % 4 = 0) :
    FnSummary AllocEntry.callPc (fun d => d = middle) (FreeListEntry R target before) := by
  have summary := AllocEntry.call_free_list post.good post.tick post.minstret post.code
    post.registers aligned
  apply summary.weaken (fun _ h => h)
  intro after called
  have memory : after.σ.mem = middle.σ.mem := called.mem
  refine ⟨?_,called.ra⟩
  refine ⟨called.good,called.minstret,called.tick,memory ▸ post.code,
    memory ▸ post.oldifyCode,memory.trans post.memory,called.pc,called.registers,
    called.output.trans post.output,?_⟩
  intro r noise outside
  apply (called.frame r noise (by simp [wrChain]) (outside 1 (by simp))).trans
  exact post.native r noise outside

/-- Fresh scanned-object entry reaches the real free-list callee through
its loaded JALR target. No premise assumes execution of that callee. -/
theorem enter_free_list {R domain size tag target c}
    (input : EntryInput R domain size tag c)
    (code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem)
    (windows : AllocEntry.Windows (allocatorRegs R c))
    (pointer : word c Layout.sym_caml_fl_p_allocate = target)
    (outer : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) Layout.sym_caml_fl_p_allocate 8)
    (inner : OutLRange (AllocEntry.prefixLog (allocatorRegs R c)) Layout.sym_caml_fl_p_allocate 8)
    (aligned : target.toNat % 4 = 0) :
    FnSummary OldifyEntry.pc (fun d => d = c) (FreeListEntry R target c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_free_list input code windows pointer outer inner).run
  intro middle post
  exact (post.enter aligned).run middle ⟨post.pc,rfl⟩

end OCaml.Vm.Gc.Fresh
