import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.HeapFrame
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Boot.Startup.AllocatorPins
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! Readiness across stores to newlib's `errno` words: the heap shape reads
`vsaRead`, which excludes them (`vsaRoomB_errno`). -/

/-- `RuntimeReady.effect_framed` with the heap frame relaxed to `vsaRead`. -/
theorem RuntimeReady.errno_framed {H capacity oldsp oldra before after writes mem pc value regs sp ra}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (pins : ∀ pin ∈ VsaIris.Sym.allocText, (mem[pin.1]?).getD 0 = (before.σ.mem[pin.1]?).getD 0)
    (domain : bytesT mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (pool : LPins8 mem Layout.sym_pool (List.replicate 8 0#8))
    (heap : ∀ a, vsaRead H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
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
      rw [post.memory, pins pin hp]
      exact ready.readOnly.2 pin hp
  room := vsaRoomB_errno ready.room fun a ha => by
    change (before.σ.mem[a]?).getD 0 = (after.σ.mem[a]?).getD 0
    rw [post.memory, heap a ha]
  stack := stack
  domainWord := by rw [post.memory]; exact domain
  poolZero := by rw [post.memory]; exact pool

/-- The two `errno` words as windows. -/
def errnoWindows : List W := [⟨0x80064668, 0x8006466c⟩, ⟨0x80064d48, 0x80064d4c⟩]

/-- A log inside the frame window and the `errno` words keeps readiness. -/
theorem RuntimeReady.errno_log {H capacity oldsp oldra before after writes log pc value regs sp ra frameSp size}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (frame : NativeFrame frameSp size)
    (inside : LogInW (⟨nativeFrameBase frameSp size, frameSp.toNat⟩ :: errnoWindows) log) :
    RuntimeReady H capacity sp ra after := by
  have lower := frame.lower
  have outside (a : Nat) (below : a < heapEnd) (notErrno : a < 0x80064668 ∨ 0x8006466c ≤ a)
      (notErrno2 : a < 0x80064d48 ∨ 0x80064d4c ≤ a) :
      OutW (⟨nativeFrameBase frameSp size, frameSp.toNat⟩ :: errnoWindows) a := by
    simp only [OutW, errnoWindows, and_true]
    refine ⟨Or.inl (by unfold nativeFrameBase; omega), notErrno, notErrno2⟩
  apply ready.errno_framed post keys cover gpFrame stack link aligned
  · intro pin member
    have source := allocator_sources pin member
    unfold AllocatorByteSource at source
    rw [frameOn_writeLog _ _ _ inside pin.1 (outside _ (by
      split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, heapEnd] at * <;> omega)
      (by split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega)
      (by split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega))]
  · rw [word_observed (m := before.σ.mem) _ (fun i hi => by
      rw [frameOn_writeLog _ _ _ inside _ (outside _ (by unfold Layout.sym_Caml_state heapEnd; omega)
        (by unfold Layout.sym_Caml_state; omega) (by unfold Layout.sym_Caml_state; omega))])]
    exact ready.domainWord
  · exact lpins8_observed ready.poolZero (fun i hi => by
      rw [frameOn_writeLog _ _ _ inside _ (outside _ (by unfold Layout.sym_pool heapEnd; omega)
        (by unfold Layout.sym_pool; omega) (by unfold Layout.sym_pool; omega))])
  · intro a ha
    have below := allocator_foot_below ha.1
    rw [frameOn_writeLog _ _ _ inside a (outside a below
      (by have := ha.2.1; unfold InRange at this; omega) (by have := ha.2.2; unfold InRange at this; omega))]
  · intro a present
    exact writeLog_present _ _ _ present
end OCaml.Vm.Boot.Startup
