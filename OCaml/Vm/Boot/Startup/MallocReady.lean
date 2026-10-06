import OCaml.Vm.Boot.Startup.AllocatorRun
import OCaml.Vm.Boot.Startup.RuntimeMalloc
import OCaml.Vm.Boot.Startup.StatCheckedAllocate
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- A successful `malloc(n)` from a ready native caller: the landed allocator
run and readiness with the fresh block live. -/
structure MallocReturned (H : List (Nat × Nat)) (capacity : Nat) (n sp ra : BitVec 64) (before after : Config) where
  allocation : LocalPost startupLive roR allocText aRegs (mS H sp)
    (MallocRoomEnd vsaLayoutP vsaRoomB H n ra sp (firstMallocSaved (vsaReg before)) capacity) before after
  ready : RuntimeReady (((vsaReg after 10).toNat, n.toNat) :: H) capacity sp ra after

theorem malloc_ready (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (n sp ra : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp allocHeadroom)
    (request : gprGet c.σ 10 = some n) (charged : vsaChg n.toNat charge) :
    FnSummary (BitVec.ofNat 64 Layout.sym_malloc) (fun d => d = c)
      (fun after => Nonempty (MallocReturned H capacity n sp ra c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have input : AllocatorInput H n ra sp (capacity + charge) c :=
    { good := ready.platform
      readOnly := ready.readOnly
      room := ready.room
      request := request
      stack := ready.stack
      link := ready.raReg
      stackOk := frame.allocator_stack
      high := frame.lower
      aligned := ready.aligned }
  obtain ⟨after, run, allocation⟩ := (allocator_summary c H n ra sp capacity charge input charged).run c ⟨pc, rfl⟩
  exact ⟨after, run, ⟨allocation, ready.malloc_result frame.lower allocation⟩⟩
theorem MallocReturned.fresh {H capacity n sp ra before after} (w : MallocReturned H capacity n sp ra before after) :
    (vsaReg after 10).toNat ≠ 0 ∧ heapStart ≤ (vsaReg after 10).toNat ∧
      (vsaReg after 10).toNat + n.toNat ≤ heapEnd ∧
      ∀ e ∈ H, ∀ a, InExt ((vsaReg after 10).toNat, n.toNat) a → ¬ InExt e a :=
  w.allocation.result.fresh.destruct

theorem MallocReturned.pc {H capacity n sp ra before after} (w : MallocReturned H capacity n sp ra before after) :
    PCAt ra after :=
  library_pc w.allocation.good w.allocation.result.frame.pc

theorem MallocReturned.result {H capacity n sp ra before after} (w : MallocReturned H capacity n sp ra before after) :
    gprGet after.σ 10 = some (vsaReg after 10) :=
  library_gpr w.ready.platform (by decide) (by decide) rfl

/-- malloc keeps every library-saved register. -/
theorem MallocReturned.saved_gpr {H capacity n sp ra before after k}
    (w : MallocReturned H capacity n sp ra before after) (platform : VsaOk startupLive before)
    (member : k ∈ vsaSaved) : gprGet after.σ k = gprGet before.σ k :=
  allocator_saved_register platform w.allocation.good w.allocation.result.frame k member

/-- malloc keeps every byte at or above its caller's stack pointer. -/
theorem MallocReturned.caller_byte {H capacity n sp ra before after a}
    (w : MallocReturned H capacity n sp ra before after) (frame : NativeFrame sp allocHeadroom)
    (caller : sp.toNat ≤ a) : (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 :=
  w.allocation.memory a (allocator_caller_outside frame.lower caller)
end OCaml.Vm.Boot.Startup
