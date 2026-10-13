import OCaml.Vm.Boot.Startup.TableHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {live : Nat → Prop}

/-- Runtime and allocator facts retained across calls, independent of any one
function's choice of saved registers or stack-frame size, over the library
model's live set `live` (the bytes the VSA model keeps present). Startup uses
all of RAM (`RuntimeReady`); a caller whose memory is not dense uses the
program image (`imageLive`), whose presence `ExecutableImage` gives. -/
structure RuntimeReadyL (live : Nat → Prop) (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64)
    (c : Config) : Prop extends LeafInput ra c where
  platform : VsaOk live c
  readOnly : ROHolds (vsaModel live) c VsaIris.MallocFast.roR VsaIris.Sym.allocText
  room : vsaRoomB ((vsaModel live).mem c) H capacity
  stack : gprGet c.σ 2 = some sp
  domainWord : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr
  poolZero : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)

/-- Startup readiness: the library's live set is all of RAM. -/
abbrev RuntimeReady (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (c : Config) : Prop :=
  RuntimeReadyL startupLive H capacity sp ra c

/-- The written registers are present after a summary. -/
def WrittenPresent (writes : List Nat) (after : Config) : Prop :=
  ∀ n ∈ writes, 1 ≤ n → n ≤ 31 → (gprGet after.σ n).isSome

theorem _root_.OCaml.Vm.Primitives.RegistersPost.writtenPresent {writes mem before pc value regs after}
    (post : RegistersPost writes mem before pc value regs after) (cover : ∀ n ∈ writes, n ∈ keysG regs) :
    WrittenPresent writes after := fun n written _ _ => by
  obtain ⟨v, hv⟩ := lookupG_of_mem (cover n written)
  rw [gholds_lookup _ post.regs hv]
  rfl

theorem _root_.OCaml.Vm.Primitives.RegistersPost.vsaOk_of_written {writes mem before pc value regs after}
    (post : RegistersPost writes mem before pc value regs after)
    (pre : VsaOk live before) (keys : KeysOK writes) (gprs : WrittenPresent writes after)
    (present : ∀ a, live a → (after.σ.mem[a]?).isSome) : VsaOk live after := by
  refine ⟨post.good, post.tick, ?_, present, ?_⟩
  · intro n lower upper
    by_cases written : n ∈ writes
    · exact gprs n written lower (by omega)
    · have frame := post.toEffectPost.gpr_frame keys n lower upper written
      change gprGet after.σ n = gprGet before.σ n at frame
      rw [frame]
      exact pre.gpr n lower upper
  · rw [post.frame _ (fun n _ => by
      have h := gprReg_htif_payload n
      exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
    exact pre.htifIdle

/-- A summary transports runtime readiness from its complete register
interface and ordinary heap/global memory frame. -/
theorem RuntimeReadyL.effect_framed_written {H capacity oldsp oldra before after writes mem pc value regs sp ra}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (gprs : WrittenPresent writes after)
    (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp)
    (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (pins : ∀ pin ∈ VsaIris.Sym.allocText, (mem[pin.1]?).getD 0 = (before.σ.mem[pin.1]?).getD 0)
    (domain : bytesT mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (pool : LPins8 mem Layout.sym_pool (List.replicate 8 0#8))
    (heap : ∀ a, vsaFoot H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (present : ∀ a : Nat, (before.σ.mem[a]?).isSome → (mem[a]?).isSome) :
    RuntimeReadyL live H capacity sp ra after where
  good := post.good
  image := post.image
  minstret := post.minstret
  raReg := link
  aligned := aligned
  tick := post.tick
  platform := by
    apply post.vsaOk_of_written ready.platform keys gprs
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
  room := by
    apply roomLocal_vsaRoomB H _ _ capacity ?_ ready.room
    intro a ha
    change (before.σ.mem[a]?).getD 0 = (after.σ.mem[a]?).getD 0
    rw [post.memory, heap a ha]
  stack := stack
  domainWord := by rw [post.memory]; exact domain
  poolZero := by rw [post.memory]; exact pool

theorem RuntimeReadyL.effect_framed {H capacity oldsp oldra before after writes mem pc value regs sp ra}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp)
    (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (pins : ∀ pin ∈ VsaIris.Sym.allocText, (mem[pin.1]?).getD 0 = (before.σ.mem[pin.1]?).getD 0)
    (domain : bytesT mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (pool : LPins8 mem Layout.sym_pool (List.replicate 8 0#8))
    (heap : ∀ a, vsaFoot H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (present : ∀ a : Nat, (before.σ.mem[a]?).isSome → (mem[a]?).isSome) :
    RuntimeReadyL live H capacity sp ra after :=
  ready.effect_framed_written post keys (post.writtenPresent cover) gpFrame stack link aligned pins domain pool heap
    present

/-- A summary transports runtime readiness from its complete register
interface and ordinary heap/global memory frame. -/
theorem RuntimeReadyL.effect_written {H capacity oldsp oldra before after writes mem pc value regs sp ra}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (gprs : WrittenPresent writes after)
    (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp)
    (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (below : ∀ a, a < heapStart → mem[a]? = before.σ.mem[a]?)
    (heap : ∀ a, vsaFoot H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (present : ∀ a : Nat, (before.σ.mem[a]?).isSome → (mem[a]?).isSome) :
    RuntimeReadyL live H capacity sp ra after := by
  apply RuntimeReadyL.effect_framed_written ready post keys gprs gpFrame stack link aligned
  · intro pin hp
    rw [below pin.1 (allocator_sources pin hp).geometry.high]
  · rw [Vsa.Sim.Boot.bytesT_local_eq (m' := before.σ.mem) Layout.sym_Caml_state 8 (fun i hi => below _ (by
      unfold heapStart Layout.sym_Caml_state; omega))]
    exact ready.domainWord
  · apply lpins8_observed ready.poolZero
    intro i hi
    rw [below _ (by unfold heapStart Layout.sym_pool; omega)]
  · exact heap
  · exact present

theorem RuntimeReadyL.effect {H capacity oldsp oldra before after writes mem pc value regs sp ra}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : RegistersPost writes mem before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp)
    (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (below : ∀ a, a < heapStart → mem[a]? = before.σ.mem[a]?)
    (heap : ∀ a, vsaFoot H a → (mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0)
    (present : ∀ a : Nat, (before.σ.mem[a]?).isSome → (mem[a]?).isSome) :
    RuntimeReadyL live H capacity sp ra after :=
  ready.effect_written post keys (post.writtenPresent cover) gpFrame stack link aligned below heap present

/-- A finite store log confined to one live payload preserves startup readiness. -/
theorem RuntimeReadyL.payload_log {H capacity oldsp oldra before after writes log pc value regs sp ra base size}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (member : (base, size) ∈ H) (lower : heapStart ≤ base)
    (inside : LogInW [⟨base, base + size⟩] log) : RuntimeReadyL live H capacity sp ra after := by
  apply RuntimeReadyL.effect ready post keys cover gpFrame stack link aligned
  · intro a ha
    exact frameOn_writeLog _ _ _ inside a ⟨Or.inl (Nat.lt_of_lt_of_le ha lower), trivial⟩
  · intro a ha
    rw [frameOn_writeLog _ _ _ inside a ⟨allocator_payload_outside member lower ha, trivial⟩]
  · intro a ha
    exact writeLog_present _ _ _ ha

/-- Complete 56-byte native zeroing preserves every other live allocation. -/
theorem RuntimeReadyL.zero {H capacity oldsp oldra before after writes pc value regs sp ra base}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : RegistersPost writes (memset56Memory before.σ.mem base) before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (member : (base, 56) ∈ H) (region : Memset56Region base) : RuntimeReadyL live H capacity sp ra after := by
  apply RuntimeReadyL.effect ready post keys cover gpFrame stack link aligned
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
