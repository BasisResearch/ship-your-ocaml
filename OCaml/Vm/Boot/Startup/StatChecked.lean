import OCaml.Vm.Boot.Startup.StatCheckedAllocate
import OCaml.Vm.Boot.Startup.StatCheckedReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

theorem StatCheckedAllocated.saved_word {H capacity sp ra s0 n before after off value}
    (w : StatCheckedAllocated H capacity sp ra s0 n before after)
    (frame : NativeFrame sp 544) (member : (off, value) ∈ [(16, s0), (24, ra)]) :
    bytesT after.σ.mem (nativeFrameBase sp 32 + off) 8 = value := by
  have short := frame.resize (small := 32) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 32) 512 := frame.nested (front := 32) (by decide)
  rw [word_observed (m := w.atMalloc.σ.mem) (nativeFrameBase sp 32 + off)
    (fun i hi => w.allocation.memory _ (allocator_caller_outside nested.lower (by
      rw [short.stack_nat]; omega))), w.call.memory, w.setup.memory]
  apply short.word_log_read (slots := [(16, s0), (24, ra)])
  · intro k v hk
    have choices : (k, v) = (16, s0) ∨ (k, v) = (24, ra) := by simpa using hk
    rcases choices with eq | eq <;> cases eq <;> decide
  · simp
  · exact member

structure StatCheckedReturned (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 n : BitVec 64)
    (before after : Config) where
  allocated : Config
  allocation : StatCheckedAllocated H capacity sp ra s0 n before allocated
  returned : WriteRegistersPost [1, 8, 2] [] allocated ra (vsaReg allocated 10)
    (statCheckedReturnRegs sp ra s0 (vsaReg allocated 10)) after
  ready : RuntimeReady (((vsaReg allocated 10).toNat, n.toNat) :: H) capacity sp ra after

/-- Complete successful nonpooling caml_stat_alloc, using the landed malloc run
and restoring the original native caller rather than assuming a return. -/
theorem stat_checked (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 n : BitVec 64) (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp 544) (saved0 : gprGet c.σ 8 = some s0)
    (request : gprGet c.σ 10 = some n) (charged : vsaChg n.toNat charge) :
    FnSummary 0x8000bb2c#64 (fun d => d = c)
      (fun after => Nonempty (StatCheckedReturned H capacity sp ra s0 n c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨allocated, run1, ⟨w⟩⟩ :=
    (stat_checked_allocate c H capacity charge sp ra s0 n ready frame saved0 request charged).run c ⟨pc, rfl⟩
  have input : StatCheckedReturnInput sp ra s0 (vsaReg allocated 10) jal_8000bb88_call.link allocated := {
    toLeafInput := w.ready.toLeafInput
    frame := frame.resize (by decide) (by decide)
    regs := ⟨w.ready.stack, library_gpr w.allocation.good (by decide) (by decide) rfl, trivial⟩
    nonzero := fun eq => w.allocation.result.fresh.nonzero (congrArg BitVec.toNat eq)
    savedRa := w.saved_word frame (by simp)
    savedS0 := w.saved_word frame (by simp)
    returnAligned := ready.aligned }
  obtain ⟨after, run2, returned⟩ := (stat_checked_return allocated sp ra s0 _ _ input).run allocated
    ⟨library_pc w.allocation.good w.allocation.result.frame.pc, rfl⟩
  have finalReady := w.ready.effect returned (by decide)
    (by simp only [statCheckedReturnRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ returned.regs (by rfl))
    (gholds_lookup (n := 1) _ returned.regs (by rfl)) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  exact ⟨after, run1.trans run2, ⟨allocated, w, returned, finalReady⟩⟩
end OCaml.Vm.Boot.Startup
