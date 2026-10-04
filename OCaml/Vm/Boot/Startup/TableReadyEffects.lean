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
  good := post.good
  image := post.image
  minstret := post.minstret
  raReg := link
  aligned := aligned
  tick := post.tick
  platform := by
    apply post.vsaOk_of_present ready.platform keys cover
    intro a ha
    rw [post.memory]
    exact present a (ready.platform.live a ha)
  readOnly := by
    constructor
    · intro pin hp
      have eq : pin = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
      subst pin
      exact (post.toEffectPost.observed_gpr keys 3 (by decide) (by decide) gpFrame).trans
        (ready.readOnly.1 _ hp)
    · intro pin hp
      change (after.σ.mem[pin.1]?).getD 0 = pin.2
      rw [post.memory, below pin.1 (allocator_sources pin hp).geometry.high]
      exact ready.readOnly.2 pin hp
  room := by
    apply roomLocal_vsaRoomB H _ _ capacity ?_ ready.room
    intro a ha
    change (before.σ.mem[a]?).getD 0 = (after.σ.mem[a]?).getD 0
    rw [post.memory, heap a ha]
  stack := (post.toEffectPost.gpr_frame keys 2 (by decide) (by decide) stackFrame).trans ready.stack
  globalReg := (post.toEffectPost.gpr_frame keys 8 (by decide) (by decide) globalFrame).trans ready.globalReg
  domainWord := by
    rw [post.memory, Vsa.Sim.Boot.bytesT_local_eq (m' := before.σ.mem) Layout.sym_Caml_state 8 (fun i hi => below _ (by
      unfold heapStart Layout.sym_Caml_state; omega))]
    exact ready.domainWord
  poolZero := by
    apply lpins8_observed ready.poolZero
    intro i hi
    rw [post.memory, below _ (by unfold heapStart Layout.sym_pool; omega)]

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
  apply ready.effect post (by decide) (by simp only [keysG, tableZeroFinalRegs, memset56Regs]; decide)
    (by decide) (by decide) (by decide)
    (gholds_lookup _ post.regs (by rfl)) (by cases second <;> decide)
  · intro a ha
    exact memset56Memory_out region _ a (Or.inl (Nat.lt_of_lt_of_le ha region.lower))
  · intro a ha
    rw [memset56Memory_out region _ a (allocator_payload_outside member region.lower ha)]
  · intro a ha
    by_cases inside : base ≤ a ∧ a < base + 56
    · rw [memset56Memory_inside region _ a inside.1 inside.2]
      rfl
    · rw [memset56Memory_out region _ a (by omega)]
      exact ha
end OCaml.Vm.Boot.Startup
