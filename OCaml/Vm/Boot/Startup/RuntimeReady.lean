import OCaml.Vm.Boot.Startup.TableHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Runtime and allocator facts retained across startup calls, independent
of any one function's choice of saved registers or stack-frame size. -/
structure RuntimeReady (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  platform : VsaOk startupLive c
  readOnly : ROHolds (vsaModel startupLive) c VsaIris.MallocFast.roR VsaIris.Sym.allocText
  room : vsaRoomB ((vsaModel startupLive).mem c) H capacity
  stack : gprGet c.σ 2 = some sp
  domainWord : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr
  poolZero : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)

/-- A summary transports runtime readiness from its complete register
interface and ordinary heap/global memory frame. -/
theorem RuntimeReady.effect {H capacity oldsp oldra before after writes mem pc value regs sp ra}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp)
    (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (below : ∀ a, a < heapStart → mem[a]? = before.σ.mem[a]?)
    (heap : ∀ a, vsaFoot H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (present : ∀ a : Nat, (before.σ.mem[a]?).isSome → (mem[a]?).isSome) :
    RuntimeReady H capacity sp ra after where
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
  stack := stack
  domainWord := by
    rw [post.memory, Vsa.Sim.Boot.bytesT_local_eq (m' := before.σ.mem) Layout.sym_Caml_state 8 (fun i hi => below _ (by
      unfold heapStart Layout.sym_Caml_state; omega))]
    exact ready.domainWord
  poolZero := by
    apply lpins8_observed ready.poolZero
    intro i hi
    rw [post.memory, below _ (by unfold heapStart Layout.sym_pool; omega)]

/-- A finite store log confined to one live payload preserves startup readiness. -/
theorem RuntimeReady.payload_log {H capacity oldsp oldra before after writes log pc value regs sp ra base size}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (member : (base, size) ∈ H) (lower : heapStart ≤ base)
    (inside : LogInW [⟨base, base + size⟩] log) : RuntimeReady H capacity sp ra after := by
  apply ready.effect post keys cover gpFrame stack link aligned
  · intro a ha
    exact frameOn_writeLog _ _ _ inside a ⟨Or.inl (Nat.lt_of_lt_of_le ha lower), trivial⟩
  · intro a ha
    rw [frameOn_writeLog _ _ _ inside a ⟨allocator_payload_outside member lower ha, trivial⟩]
  · intro a ha
    exact writeLog_present _ _ _ ha

/-- Complete 56-byte native zeroing preserves every other live allocation. -/
theorem RuntimeReady.zero {H capacity oldsp oldra before after writes pc value regs sp ra base}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : RegistersPost writes (memset56Memory before.σ.mem base) before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (member : (base, 56) ∈ H) (region : Memset56Region base) : RuntimeReady H capacity sp ra after := by
  apply ready.effect post keys cover gpFrame stack link aligned
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
