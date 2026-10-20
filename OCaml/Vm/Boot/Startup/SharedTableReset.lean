import OCaml.Vm.Boot.Startup.ExtTableFinish
import OCaml.Vm.Boot.Startup.CustomReset
import OCaml.Vm.Boot.Startup.ExtTableLive
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Actual reset execution after the shared-library path table is initialized. -/
structure ResetSharedTableReturned (initial after : Config) where
  source : Config
  custom : ResetCustomReturned initial source
  called : Config
  call : WriteRegistersPost [11, 10, 1] [] source jal_80004de0_call.target sharedTableAddress
    ((1, jal_80004de0_call.link) :: sharedTableArgs parameterStack) called
  H : List (Nat × Nat)
  domain : (firstDomainPtr.toNat, 928) ∈ H
  t1 : BitVec 64
  t2 : BitVec 64
  t3 : BitVec 64
  /-- caml_init_domain's record and tables at the call. -/
  entryKept : DomainKept H called.σ.mem t1 t2 t3
  returned : ExtTableReturned H (startupAllocatorCredits - 384) parameterStack jal_80004de0_call.link
    (vsaReg called 8) sharedTableAddress 8#64 called after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem ResetSharedTableReturned.reset {initial after} (w : ResetSharedTableReturned initial after) :
    ElfResetReady elf initial := w.custom.reset

theorem ResetSharedTableReturned.pc {initial after} (w : ResetSharedTableReturned initial after) :
    PCAt 0x80004de4#64 after := w.returned.post.pc

theorem ResetSharedTableReturned.ready {initial after} (w : ResetSharedTableReturned initial after) :
    ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
      RuntimeReady H (startupAllocatorCredits - 384) parameterStack jal_80004de0_call.link after :=
  ⟨_, List.mem_cons_of_mem _ w.domain, w.returned.ready⟩

theorem reset_shared_table_returned_exists : ∃ initial after, Nonempty (ResetSharedTableReturned initial after) := by
  obtain ⟨initial, source, ⟨w⟩⟩ := reset_custom_returned_exists
  have ready := w.returned.ready
  have domain := w.returned.nodes.member w.source.domain
  have entry := w.kept_after
  generalize ((vsaReg w.returned.nodes.bigarray.registration.allocated 10).toNat, 16) :: w.returned.nodes.H3 = H
    at ready domain entry
  obtain ⟨called, run1, call⟩ := (caml_shared_table source _ _ ready.toLeafInput ready.stack).run source ⟨w.pc, rfl⟩
  have calledReady := ready.effect call (by decide)
    (by simp only [sharedTableArgs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl))
    (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have capacity : startupAllocatorCredits - 320 = (startupAllocatorCredits - 384) + 64 := by decide
  rw [capacity] at calledReady
  obtain ⟨after, run2, ⟨returned⟩⟩ := (ext_table_init called _ (startupAllocatorCredits - 384) 64 parameterStack
    jal_80004de0_call.link (vsaReg called 8) sharedTableAddress 8#64 calledReady (by constructor <;> decide)
    (ExtTableSite.shared _) (library_gpr calledReady.platform (by decide) (by decide) rfl) call.result
    (gholds_lookup (n := 11) _ call.regs (by rfl)) (by constructor <;> decide)).run called ⟨call.pc, rfl⟩
  rw [show source.σ.mem = called.σ.mem from call.memory.symm] at entry
  exact ⟨initial, after, ⟨source, w, called, call, _, domain, _, _, _, entry, returned, w.run.trans (run1.trans run2)⟩⟩

/-- The record and the tables after the shared-library path table is built. -/
theorem ResetSharedTableReturned.kept_after {initial after} (w : ResetSharedTableReturned initial after) :
    DomainKept (((vsaReg w.returned.allocation.allocation.allocated 10).toNat,
      (extTableRequest 8#64).toNat) :: w.H) after.σ.mem w.t1 w.t2 w.t3 :=
  (w.entryKept.live (w.returned.live (by constructor <;> decide) (Or.inr (by decide)))).mono
    fun _ he => List.mem_cons_of_mem _ he
end OCaml.Vm.Boot.WhileMinElfParse
