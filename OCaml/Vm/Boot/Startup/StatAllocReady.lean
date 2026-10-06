import OCaml.Vm.Boot.Startup.StatAlloc
import OCaml.Vm.Boot.Startup.AllocatorRun
import OCaml.Vm.Boot.Startup.RuntimeMalloc
import OCaml.Vm.Boot.Startup.StatCheckedAllocate
import OCaml.Vm.Primitives.LibraryEffects
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- Nonpooling `caml_stat_alloc_noexc(n)` that succeeds: dispatch, then the landed malloc. -/
structure StatAllocated (H : List (Nat × Nat)) (capacity : Nat) (n sp ra : BitVec 64) (before after : Config) where
  atMalloc : Config
  dispatch : BoundaryPost [15] before ra (BitVec.ofNat 64 Layout.sym_malloc) [(15, 0#64)] atMalloc
  platform : VsaOk startupLive atMalloc
  allocation : LocalPost startupLive roR allocText aRegs (mS H sp)
    (MallocRoomEnd vsaLayoutP vsaRoomB H n ra sp (firstMallocSaved (vsaReg atMalloc)) capacity) atMalloc after
  ready : RuntimeReady (((vsaReg after 10).toNat, n.toNat) :: H) capacity sp ra after

theorem stat_alloc_ready (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (n sp ra : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp allocHeadroom)
    (request : gprGet c.σ 10 = some n) (charged : vsaChg n.toNat charge) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) (fun d => d = c)
      (fun after => Nonempty (StatAllocated H capacity n sp ra c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨atMalloc, run1, dispatch⟩ := (statAlloc_dispatch c ra ready.toLeafInput ready.poolZero).run c ⟨pc, rfl⟩
  have kept (k : Nat) (lower : 1 ≤ k) (upper : k ≤ 31) (unwritten : k ∉ [15]) :
      gprGet atMalloc.σ k = gprGet c.σ k := by
    apply gprGet_of_frame k lower upper (gpr_avoids_noise k (by omega) lower)
    · intro m hm
      have hm15 : m = 15 := List.mem_singleton.1 hm
      subst hm15
      exact gprReg_beq_false 15 (by decide) k (by omega) (by decide) lower
        (fun e => unwritten (by simp [e]))
    · intro r noise outside
      exact dispatch.frame r (fun m hm => by
        have ne := outside m hm
        exact fun e => by rw [e, beq_self_eq_true] at ne; contradiction) noise
  have post : RegistersPost [15] c.σ.mem c (BitVec.ofNat 64 Layout.sym_malloc) n [(15, 0#64)] atMalloc :=
    ⟨⟨dispatch.good, dispatch.image, dispatch.minstret, dispatch.tick, dispatch.pc,
      (kept 10 (by decide) (by decide) (by decide)).trans request, dispatch.memory, dispatch.output,
      dispatch.frame⟩, dispatch.regs⟩
  have mid := ready.effect post (by decide) (by simp [keysG]) (by decide)
    ((kept 2 (by decide) (by decide) (by decide)).trans ready.stack)
    ((kept 1 (by decide) (by decide) (by decide)).trans ready.raReg) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have input : AllocatorInput H n ra sp (capacity + charge) atMalloc :=
    { good := mid.platform
      readOnly := mid.readOnly
      room := mid.room
      request := (kept 10 (by decide) (by decide) (by decide)).trans request
      stack := mid.stack
      link := mid.raReg
      stackOk := frame.allocator_stack
      high := frame.lower
      aligned := mid.aligned }
  obtain ⟨after, run2, allocation⟩ := (allocator_summary atMalloc H n ra sp capacity charge input charged).run
    atMalloc ⟨dispatch.pc, rfl⟩
  exact ⟨after, run1.trans run2, ⟨atMalloc, dispatch, mid.platform, allocation, mid.malloc_result frame.lower allocation⟩⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- The allocation keeps every byte at or above its caller's stack pointer. -/
theorem StatAllocated.caller_byte {H capacity n sp ra before after a}
    (w : StatAllocated H capacity n sp ra before after) (frame : NativeFrame sp allocHeadroom)
    (caller : sp.toNat ≤ a) : (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 := by
  have unchanged := w.allocation.memory a (allocator_caller_outside frame.lower caller)
  change (after.σ.mem[a]?).getD 0 = (w.atMalloc.σ.mem[a]?).getD 0 at unchanged
  rw [unchanged, w.dispatch.memory]

/-- The allocation keeps every library-saved register. -/
theorem StatAllocated.saved_gpr {H capacity n sp ra before after k}
    (w : StatAllocated H capacity n sp ra before after) (member : k ∈ vsaSaved) :
    gprGet after.σ k = gprGet before.σ k := by
  have range : 1 ≤ k ∧ k ≤ 31 ∧ k ≠ 15 := by simp [vsaSaved] at member; omega
  have mid : gprGet w.atMalloc.σ k = gprGet before.σ k := by
    apply gprGet_of_frame k range.1 range.2.1 (gpr_avoids_noise k (by omega) range.1)
    · intro m hm
      have hm15 : m = 15 := List.mem_singleton.1 hm
      subst hm15
      exact gprReg_beq_false 15 (by decide) k (by omega) (by decide) range.1 (fun e => range.2.2 e.symm)
    · intro r noise outside
      exact w.dispatch.frame r (fun m hm => by
        have ne := outside m hm
        exact fun e => by rw [e, beq_self_eq_true] at ne; contradiction) noise
  exact (allocator_saved_register w.platform w.allocation.good w.allocation.result.frame k member).trans mid
end OCaml.Vm.Boot.Startup
