import OCaml.Vm.Boot.Startup.StatCheckedPrefix
import OCaml.Vm.Boot.Startup.StatCheckedCallCallInterface
import OCaml.Vm.Boot.Startup.RuntimeMalloc
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.NativeNested
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

def statCheckedCallRegs (sp n : BitVec 64) : GRegs :=
  [(1, jal_8000bb88_call.link), (8, n), (2, nativeStack sp 32), (15, 0#64), (10, n)]

/-- The native caller geometry also supplies the landed allocator's stack interface. -/
theorem NativeFrame.allocator_stack {sp} (frame : NativeFrame sp allocHeadroom) : SpOKA sp := by
  constructor
  · have lower := frame.lower
    have bound : Vsa.Sim.tohostAddr + 16 ≤ heapEnd := by decide
    omega
  · have upper := frame.upper
    have bound : Layout.sym_stack_top ≤ 2^32 := by decide
    omega
  · exact frame.aligned

structure StatCheckedAllocated (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 n : BitVec 64)
    (before after : Config) where
  saved : Config
  atMalloc : Config
  setup : WriteRegistersPost [15, 2, 8] (statCheckedLog sp ra s0) before 0x8000bb88#64 n
    (statCheckedRegs sp ra n) saved
  call : RegistersPost [1] saved.σ.mem saved jal_8000bb88_call.target n
    (statCheckedCallRegs sp n) atMalloc
  allocation : LocalPost startupLive roR VsaIris.Sym.allocText VsaIris.Sym.aRegs
    (mS H (nativeStack sp 32))
    (MallocRoomEnd vsaLayoutP vsaRoomB H n jal_8000bb88_call.link (nativeStack sp 32)
      (firstMallocSaved (vsaReg atMalloc)) capacity) atMalloc after
  ready : RuntimeReady (((vsaReg after 10).toNat, n.toNat) :: H) capacity
    (nativeStack sp 32) jal_8000bb88_call.link after

/-- The nonpooling checked wrapper invokes the existing successful allocator contract. -/
theorem stat_checked_allocate (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 n : BitVec 64) (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp 544) (saved0 : gprGet c.σ 8 = some s0)
    (request : gprGet c.σ 10 = some n) (charged : vsaChg n.toNat charge) :
    FnSummary 0x8000bb2c#64 (fun d => d = c)
      (fun after => Nonempty (StatCheckedAllocated H capacity sp ra s0 n c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := frame.resize (small := 32) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 32) 512 := frame.nested (front := 32) (by decide)
  have input : StatCheckedPrefixInput sp ra s0 n c :=
    ⟨ready.toLeafInput, short, ⟨ready.stack, saved0, ready.raReg, request, trivial⟩, ready.poolZero⟩
  obtain ⟨saved, run1, setup⟩ := (stat_checked_prefix c sp ra s0 n input).run c ⟨pc, rfl⟩
  have savedReady := ready.stack_log setup (by decide)
    (by simp only [statCheckedRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ setup.regs (by rfl))
    (gholds_lookup (n := 1) _ setup.regs (by rfl)) ready.aligned short (statCheckedLog_inside short)
  have args : GHolds saved.σ [(8, n), (2, nativeStack sp 32), (15, 0#64), (10, n)] :=
    holds_project setup.regs (by simp [statCheckedRegs, lookupG])
  obtain ⟨atMalloc, run2, call⟩ := (call_registers_summary jal_8000bb88_call_shape jal_8000bb88_call_decode saved
    (jal_8000bb88_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [8, 2, 15, 10]; decide) (by simp only [KeysAvoidRa, keysG]; decide) (by rfl)).run saved ⟨setup.pc, rfl⟩
  have mallocReady := savedReady.effect call (by decide)
    (by change ∀ x ∈ [1], x ∈ [1, 8, 2, 15, 10]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl))
    (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have allocInput : AllocatorInput H n jal_8000bb88_call.link (nativeStack sp 32) (capacity + charge) atMalloc :=
    ⟨mallocReady.platform, mallocReady.readOnly, mallocReady.room, call.result,
      mallocReady.stack, mallocReady.raReg, nested.allocator_stack, nested.lower, by decide⟩
  obtain ⟨after, run3, allocated⟩ := (allocator_summary atMalloc H n _ _ capacity charge allocInput charged).run
    atMalloc ⟨call.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans run3), ⟨saved, atMalloc, setup, call, allocated,
    mallocReady.malloc_result nested.lower allocated⟩⟩
end OCaml.Vm.Boot.Startup
