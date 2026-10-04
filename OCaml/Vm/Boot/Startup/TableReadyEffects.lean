import OCaml.Vm.Boot.Startup.TableReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- A summary transports table-startup readiness from its complete register
interface and ordinary heap/global memory frame. -/
theorem TableReady.effect {H capacity oldra before after writes mem pc value regs ra}
    (ready : TableReady H capacity oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (stackFrame : 2 ∉ writes) (globalFrame : 8 ∉ writes) (gpFrame : 3 ∉ writes)
    (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (below : ∀ a, a < heapStart → mem[a]? = before.σ.mem[a]?)
    (heap : ∀ a, vsaFoot H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (present : ∀ a : Nat, (before.σ.mem[a]?).isSome → (mem[a]?).isSome) :
    TableReady H capacity ra after where
  toRuntimeReady := ready.toRuntimeReady.effect post keys cover gpFrame
    ((post.toEffectPost.gpr_frame keys 2 (by decide) (by decide) stackFrame).trans ready.stack)
    link aligned below heap present
  globalReg := (post.toEffectPost.gpr_frame keys 8 (by decide) (by decide) globalFrame).trans ready.globalReg

/-- Publishing into a domain payload retains the abstract allocator heap. -/
theorem TableReady.publish {H capacity ra before after slot p}
    (ready : TableReady H capacity ra before) (member : (firstDomainPtr.toNat, 928) ∈ H)
    (post : WriteRegistersPost [15, 10] (tablePublishLog slot p) before slot.exit p (tablePublishRegs p) after) :
    TableReady H capacity ra after := by
  apply ready.effect post (by decide) (by simp only [keysG, tablePublishRegs]; decide)
    (by decide) (by decide) (by decide)
    ((post.frame .x1 (by decide) (by decide)).trans ready.raReg) ready.aligned
  · intro a ha
    have bound : heapStart ≤ slot.address.toNat := by cases slot <;> decide
    exact writeLog_out _ _ a ⟨Or.inl (by omega), trivial⟩
  · intro a ha
    rw [writeLog_out _ _ a (tablePublish_allocator_outside slot p member ha)]
  · intro a ha
    exact writeLog_present _ _ _ ha

/-- Native zeroing changes only the new payload, preserving all allocator and
runtime-global observations in the shared readiness contract. -/
theorem TableReady.zero {H capacity oldra before after second base}
    (ready : TableReady H capacity oldra before) (region : Memset56Region base)
    (member : (base, 56) ∈ H)
    (post : RegistersPost [12, 11, 1, 6, 14, 15, 13, 5] (memset56Memory before.σ.mem base) before
      (tableZeroCall second).link (BitVec.ofNat 64 base) (tableZeroFinalRegs second base) after) :
    TableReady H capacity (tableZeroCall second).link after := by
  constructor
  · exact ready.toRuntimeReady.zero post (by decide)
      (by simp only [keysG, tableZeroFinalRegs, memset56Regs]; decide) (by decide)
      ((post.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready.stack)
      (gholds_lookup _ post.regs (by rfl)) (by cases second <;> decide) member region
  · exact (post.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans ready.globalReg
end OCaml.Vm.Boot.Startup
