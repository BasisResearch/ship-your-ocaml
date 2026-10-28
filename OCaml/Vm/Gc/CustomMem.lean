import OCaml.Vm.Primitives.Leaf
import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Gc.NurseryDefs
import OCaml.Vm.Boot.Startup.HeapReady
import OCaml.Vm.Gc.F1Heap
import OCaml.Vm.Gc.NamedOwnership
import OCaml.Vm.Gc.CustomContext

/-!
# `caml_alloc_custom_mem` for a channel's custom block, from any call site

`caml_ml_open_descriptor_out/in` and `caml_ml_out_channels_list` (through the
inlined `caml_alloc_channel`) wrap a channel record in a custom block with
`caml_alloc_custom_mem(&channel_operations, sizeof(struct channel *),
sizeof(struct channel))`. That call is the collector-integrated allocation:
`Alloc_small` in the minor heap, the custom table, and the GC-speed
accounting. Its summary is the named obligation `CustomMemCall` (lane a6-gc).

A call site (`CustomMemSite`) is its return address, its stack pointer, the
record in `s0` and the caller's frame above `sp`. The call is safe for `k + 1`
more such allocations (`Ready (k + 1)`); each one consumes one
(the major-resource charge has rational operands `57424/297968`; the
actual binary64 helper/threshold execution remains part of this obligation). newlib's heap enters as `HeapReady H cap`
at the call, together with independent `CustomCallPins`, and returns as `HeapReady H' cap'` over every block of `H` (the
first call since the cut adds the custom table's block), so a caller with
several calls (`caml_ml_out_channels_list`) chains it. `Ready` reads only the
runtime's own state (`CustomMemCall.state`): the static
`caml_extra_heap_resources`, the domain's `extra_heap_resources_minor`, and the
custom table's struct and storage (live blocks of newlib's heap). It lies apart
from the fixed caller-write regions (`CallerApart`):
* allocator globals (selected-ledger ownership excludes free arena bytes);
* F1's covered regions other than the domain record;
* the native stack;
* the minor heap;
* the domain's `young_ptr`, `young_limit` and `local_roots` words.

Actual records, named roots and other live allocations carry local separation
in the selected heap's `CustomSpace`; their memory-linked shapes do not imply
allocator ownership. Callers keep `Ready` through their checked byte frames.
`CustomMemReturned.allocGrows` bounds physical backing-storage growth, and its
single returned heap also carries `CustomLedger` for that storage.
-/

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady)
set_option autoImplicit false

/-- `caml_alloc_custom_mem`'s entry. -/
def customMemEntry : BitVec 64 := 0x800247f8#64

/-- `&channel_operations`. -/
def channelOps : BitVec 64 := 2147891728#64

/-- `sizeof(struct channel)`, the custom block's out-of-heap charge. -/
def channelMem : BitVec 64 := 65616#64

/-- Native stack the call uses below its `sp`. -/
def customStackBytes : Nat := 576

/-- The custom block's header: wosize 2, `Custom_tag`, color 0. -/
def customHeader : BitVec 64 := 0x8ff#64

/-- The header is a channel's (`ObjAt (.channel id)`: wosize 2, `Custom_tag`). -/
theorem customHeader_ok : HeaderOk customHeader (OCaml.Bytecode.Obj.channel 0).wosize (OCaml.Bytecode.Obj.channel 0).tag := by
  unfold HeaderOk; decide

/-- A call of `caml_alloc_custom_mem(&channel_operations, 8, sizeof(struct
channel))`: the return address, `sp` at the call, the record in `s0`, and the
caller's frame `[sp, sp + callerBytes)`. -/
structure CustomMemSite where
  link : BitVec 64
  sp : BitVec 64
  record : BitVec 64
  callerBytes : Nat

/-- The registers the call reads. -/
def CustomMemSite.args (site : CustomMemSite) : GRegs :=
  [(10, channelOps), (11, 8#64), (12, channelMem), (8, site.record), (2, site.sp)]

/-- A domain word's address at `c`. -/
def domainAddr (c : Config) (offset : Nat) : Nat :=
  (word c Layout.sym_Caml_state).toNat + offset

/-- What callers write around the call: the runtime's custom-allocation state
lies apart from it. -/
structure CallerApart (c : Config) (a : Nat) : Prop where
  belowStack : a < Vsa.Sim.DlHeap.heapEnd
  minor : a < minorRegion.lo ∨ minorRegion.hi ≤ a
  youngPtr : a + 8 ≤ domainAddr c Layout.off_young_ptr ∨ domainAddr c Layout.off_young_ptr + 8 ≤ a
  youngLimit : a + 8 ≤ domainAddr c Layout.off_young_limit ∨ domainAddr c Layout.off_young_limit + 8 ≤ a
  localRoots : a + 8 ≤ domainAddr c Layout.off_local_roots ∨ domainAddr c Layout.off_local_roots + 8 ≤ a
  /-- the one static word: `caml_extra_heap_resources` (`caml_adjust_gc_speed`) -/
  static : a < Vsa.Sim.DlHeap.heapStart → VsaIris.InExt (Layout.sym_caml_extra_heap_resources, 8) a
  /-- within the domain record, only `extra_heap_resources_minor` -/
  domainField : VsaIris.InExt (domainAddr c 0, Layout.domainStateBytes) a →
    VsaIris.InExt (domainAddr c Layout.off_extra_heap_resources_minor, 8) a
  /-- apart from F1's regions other than the domain record (the custom table's
  struct and storage are blocks of their own) -/
  covered : ∀ e ∈ f1Covered, e.1 ≠ Boot.WhileMinRuntime.domain → ¬ VsaIris.InExt e a

/-- At the call: the link and argument registers, the callee's stack room,
and nursery room for the block (`caml_alloc_small`'s fast path). -/
structure CustomMemInput (H : List (Nat × Nat)) (cap : Nat) (site : CustomMemSite) (f : Config) : Prop where
  leaf : LeafInput site.link f
  /-- Actual read-only parameters and identity, independent of Ready. -/
  context : CustomCallPins f
  /-- newlib's heap, for the custom table's first allocation -/
  heap : HeapReady H cap f
  pc : pcOf f = some customMemEntry
  regs : GHolds f.σ site.args
  frame : NativeFrame site.sp customStackBytes
  room : (runtimeFields f).youngLimit + 24 ≤ (runtimeFields f).youngPtr
  youngAligned : (runtimeFields f).youngPtr % 8 = 0

/-- The call returned the custom block `v` at the old `young_ptr − 16`, with its
header and operations word written. The callee-saved registers, `sp`, the
young limit, the local roots, and memory outside its own footprint are kept.
The footprint is: the runtime's state, the callee's stack, the block, and the
`young_ptr` word. -/
structure CustomMemReturned (state : Config → Nat → Prop) (H : List (Nat × Nat)) (site : CustomMemSite)
    (v : BitVec 64) (f d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ x, d.σ.regs.get? Register.minstret = some x
  tick : d.tick < 2
  link : ∃ r, gprGet d.σ 1 = some r ∧ r.toNat % 4 = 0
  pc : pcOf d = some site.link
  stack : gprGet d.σ 2 = some site.sp
  record : gprGet d.σ 8 = some site.record
  result : gprGet d.σ 10 = some v
  saved : ∀ n ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet f.σ n
  gprs : GprsKept f d
  idle : d.σ.regs.get? Register.htif_payload_writes = some 0#4
  output : d.σ.sailOutput = f.σ.sailOutput
  block : v.toNat + 16 = (runtimeFields f).youngPtr
  youngPtr : (runtimeFields d).youngPtr = (runtimeFields f).youngPtr - 24
  youngLimit : (runtimeFields d).youngLimit = (runtimeFields f).youngLimit
  domain : word d Layout.sym_Caml_state = word f Layout.sym_Caml_state
  header : bytesT d.σ.mem (v.toNat - 8) 8 = customHeader
  ops : bytesT d.σ.mem v.toNat 8 = channelOps
  /-- newlib's heap over every block of `H` (plus the custom table's on the
  first call), ready for the next call; ownership of the returned state is
  certified in that same existential ledger -/
  heap : ∃ H' cap', HeapReady H' cap' d ∧ CustomOwned state H' d ∧ CustomLedger H' d ∧ ∀ e ∈ H, e ∈ H'
  kept : ∀ a, ¬ state f a → ¬ VsaIris.VsaHeap.vsaFoot H a →
    (a < site.sp.toNat - customStackBytes ∨ site.sp.toNat ≤ a) →
    (a + 24 < (runtimeFields f).youngPtr ∨ (runtimeFields f).youngPtr ≤ a) →
    (a + 8 ≤ domainAddr f Layout.off_young_ptr ∨ domainAddr f Layout.off_young_ptr + 8 ≤ a) →
    (d.σ.mem[a]?).getD 0 = (f.σ.mem[a]?).getD 0
  /-- the runtime's state grows only into newlib's free space at the call
  (the custom table's storage, first allocated or reallocated) -/
  grows : ∀ a, state d a → state f a ∨ VsaIris.VsaHeap.vsaFoot H a
  /-- Actual custom-table allocation/reallocation grows allocated storage
  only into this input ledger's free footprint. Resource accumulator bytes
  cannot be reclassified as backing storage. Supplied by the native callee. -/
  allocGrows : ∀ a, CustomAllocFoot d a → CustomAllocFoot f a ∨ VsaIris.VsaHeap.vsaFoot H a

/-- Finite G1 channel-custom budget. The rational inequality below does
not prove actual binary64 rounding or native threshold branches; those remain
part of the accepted native call obligation. -/
def quietBound : Nat := 5

theorem quietBound_spec : quietBound * 57424 ≤ 297968 ∧ 297968 < (quietBound + 1) * 57424 := by decide

/-- `Ready` from a count: `Customs c n` says the runtime's custom-allocation
state at `c` is the one after `n` channel allocations since the cut (lane
a6-gc supplies it at the cut with `n = 0` and across each call with `n + 1`;
lane a1-arms carries `Customs c s.world.customs` in the represented state). -/
def ReadyOf (Customs : Config → Nat → Prop) (k : Nat) (c : Config) : Prop :=
  ∃ n, Customs c n ∧ n + k ≤ quietBound

theorem ReadyOf.succ {Customs : Config → Nat → Prop} {k n} {c d : Config} (ready : ReadyOf Customs (k + 1) c)
    (unique : ∀ n', Customs c n' → n' = n) (step : Customs d (n + 1)) : ReadyOf Customs k d := by
  obtain ⟨n', at', bound⟩ := ready
  rw [unique n' at'] at bound
  exact ⟨n + 1, step, by omega⟩

/-- Physical-state laws of the named `CustomMemCall` machine obligation.
`Customs` describes physical custom-allocation state, independently of the
channel refcounts. Its concrete supplier must certify these laws together
with the call summary; they do not follow from `Ready k`.

The caller increments a channel refcount before calling the allocator. Such
stores frame `Customs`; only the allocator advances its count. -/
structure CustomAccounting (Ready : Nat → Config → Prop)
    (state : Config → Nat → Prop) (Customs : Config → Nat → Prop) : Prop where
  unique : ∀ {c n n'}, Customs c n → Customs c n' → n = n'
  frame : ∀ {c d n}, Customs c n →
    (∀ a, state c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) →
    word d Layout.sym_Caml_state = word c Layout.sym_Caml_state → Customs d n
  /-- Quietness is proved from the physical state and the remaining budget,
  rather than from the refcount sum as a frame-stable definition of `Ready`. -/
  ready : ∀ {k c}, ReadyOf Customs k c → Ready k c

/-- Physical accounting across a native span. The charge is the number of
actual custom allocations, independent of earlier refcount stores. -/
structure CustomCountStep (Customs : Config → Nat → Prop) (c d : Config) (charge : Nat) : Prop where
  count : ∀ {n}, Customs c n → Customs d (n + charge)

theorem CustomCountStep.trans {Customs : Config → Nat → Prop} {c d e : Config} {i j : Nat}
    (first : CustomCountStep Customs c d i) (second : CustomCountStep Customs d e j) :
    CustomCountStep Customs c e (i + j) := by
  constructor
  intro n h
  simpa only [Nat.add_assoc] using second.count (first.count h)

/-- Register-only segments preserve physical custom accounting. -/
theorem CustomAccounting.sameMemory {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (accounting : CustomAccounting Ready state Customs)
    {c d : Config} (memory : d.σ.mem = c.σ.mem) : CustomCountStep Customs c d 0 :=
by
  constructor
  intro n h
  simpa only [Nat.add_zero] using accounting.frame h (fun _ _ => by rw [memory])
    (by unfold word; rw [memory])

/-- Readiness, state footprint, and physical count across caller stores. -/
structure CustomFramed (Ready : Nat → Config → Prop) (state Customs : Config → Nat → Prop)
    (k : Nat) (c d : Config) : Prop where
  ready : Ready k d
  state : ∀ a, state d a ↔ state c a
  counts : CustomCountStep Customs c d 0
  addresses : customBase d = customBase c ∧ customEnd d = customEnd c

/-- Exact physical accounting on this execution, in addition to the allocator's
ordinary return facts. It is supplied by the actual `FnSummary` post. -/
structure CustomMemCountedReturned (state : Config → Nat → Prop)
    (Customs : Config → Nat → Prop) (H : List (Nat × Nat)) (site : CustomMemSite)
    (v : BitVec 64) (f d : Config) : Prop extends CustomMemReturned state H site v f d where
  count : ∀ {n}, Customs f n → Customs d (n + 1)

/-- **The runtime's channel custom allocations** (named obligation, lane
a6-gc). `Ready k c`: `k` more calls are safe at `c`, judged from `state c`
alone; read-only call parameters are separately required by CustomMemInput.
These are the bytes the call may write besides its stack, the
block, `young_ptr` and newlib's own bytes (`vsaFoot H`): the counters and the
custom table. -/
structure CustomMemCall (Ready : Nat → Config → Prop) (state : Config → Nat → Prop)
    (Customs : Config → Nat → Prop) : Prop where
  /-- The runtime footprint consists of the resource words and the fixed G1
  custom table with its actual storage. This does not assert quietness or a
  complete physical accounting predicate. -/
  footprint : ∀ c a, state c a → CustomFoot c a
  /-- A ready physical runtime includes the whole table struct and current
  storage in its read/write footprint, as well as both resource words.
  The concrete physical supplier must prove this; occupancy alone cannot. -/
  physical : ∀ k c, Ready k c → ∀ a, CustomFoot c a → state c a
  accounting : CustomAccounting Ready state Customs
  apart : ∀ c a, state c a → CallerApart c a
  /-- a caller's stores outside the runtime's state keep it ready -/
  frame : ∀ k c c', Ready k c → (∀ a, state c a → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) →
    word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state → Ready k c' ∧ (∀ a, state c' a ↔ state c a)
  call : ∀ (H : List (Nat × Nat)) (cap : Nat) (site : CustomMemSite) (k : Nat) (f : Config),
    Ready (k + 1) f → CustomMemInput H cap site f → CustomOwned state H f →
    FnSummary customMemEntry (fun d => d = f)
      (fun d => ∃ v, CustomMemCountedReturned state Customs H site v f d ∧ Ready k d)

/-- Concrete read-only pins cannot overlap mutable custom-state bytes.
This uses the actual domain pin and the existing footprint's local rules. -/
theorem CustomCallRead.not_state {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    {c : Config} (pins : CustomCallPins c) {a : Nat} (read : CustomCallRead a) : ¬ state c a := by
  intro at_
  have bounds := read.bounds
  have apart := custom.apart c a at_
  rcases bounds.location with low | domain
  · exact bounds.resource (apart.static low)
  · apply bounds.minorResource
    have dom : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
      rw [pins.domain]; rfl
    simpa only [domainAddr, dom] using apart.domainField (by simpa only [domainAddr, dom, Nat.add_zero] using domain)

/-- Read-only domain observations belong to the same selected allocator
ledger; low static reads avoid allocator globals by finite address checks. -/
theorem CustomCallRead.notFoot {H : List (Nat × Nat)} {cap : Nat} {c : Config}
    (heap : HeapReady H cap c) (domain : Covered H (Boot.WhileMinRuntime.domain, Layout.domainStateBytes))
    {a : Nat} (read : CustomCallRead a) : ¬ VsaIris.VsaHeap.vsaFoot H a := by
  rcases read.bounds.location with low | inside
  · rintro (global | ⟨lo, _, _⟩)
    · exact read.bounds.allocator global
    · omega
  · exact domain.notFoot (fun _ member => heap.block_bounds member) inside

/-- Actual record/domain separation also protects every read-only call pin. -/
theorem CustomCallRead.outside_record {a r size : Nat} (read : CustomCallRead a)
    (low : Vsa.Sim.DlHeap.heapStart ≤ r)
    (apart : r + size ≤ Boot.WhileMinRuntime.domain ∨
      Boot.WhileMinRuntime.domain + Layout.domainStateBytes ≤ r) : a < r ∨ r + size ≤ a := by
  rcases read.bounds.location with below | inside
  · omega
  · have lo := inside.1; have hi := inside.2
    dsimp only at hi
    omega

/-- State ownership comes from the same ledger selected by `LibHeapAt`. -/
theorem CustomMemCall.owned {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    {H cap chs c} (heap : LibHeapAt H cap chs c) : CustomOwned state H c :=
  ⟨fun a ha => heap.custom.owned.bytes a (custom.footprint c a ha)⟩

/-- The same selected native-return ledger owns all dynamic custom storage,
not only a potentially partial accounting footprint. -/
theorem CustomMemCall.owned_physical {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    {H c k} (owned : CustomOwned state H c) (ready : Ready k c) : CustomOwned CustomFoot H c :=
  ⟨fun a ha => owned.bytes a (custom.physical k c ready a ha)⟩

/-- Physical table growth keeps separation from actually owned live regions
and the selected named roots. Its memory frame is supplied at the actual native
call boundary, rather than by an unconditional law of arbitrary memory lists. -/
theorem CustomMemReturned.space {state : Config → Nat → Prop} {H blocked roots : List (Nat × Nat)}
    {site : CustomMemSite} {v : BitVec 64} {f d : Config} {cap : Nat}
    (ret : CustomMemReturned state H site v f d) (space : CustomSpace blocked f)
    (heap : HeapReady H cap f) (named : NamedLedger H roots f)
    (covered : ∀ e ∈ blocked, Covered H e)
    (keepNamed : ∀ a, NamedRead f a → byte d a = byte f a) : CustomSpace blocked d := by
  exact space.grow named keepNamed ret.allocGrows
    (fun e he _ inside => (covered e he).notFoot (fun _ member => heap.block_bounds member) inside)
    (fun _ read => named.read_not_foot heap read)

/-- The native return packages spatial evidence and complete physical
ownership with its own existential heap, including after backing-storage growth. -/
theorem CustomMemCall.returned_space {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    {H blocked roots : List (Nat × Nat)} {site : CustomMemSite} {v : BitVec 64}
    {f d : Config} {k cap : Nat} (ret : CustomMemReturned state H site v f d)
    (ready : Ready k d) (space : CustomSpace blocked f) (heap : HeapReady H cap f)
    (named : NamedLedger H roots f) (covered : ∀ e ∈ blocked, Covered H e)
    (keepNamed : ∀ a, NamedRead f a → byte d a = byte f a) :
    ∃ H' cap', HeapReady H' cap' d ∧ CustomOwned CustomFoot H' d ∧
      CustomSpace blocked d ∧ CustomLedger H' d ∧ ∀ e ∈ H, e ∈ H' := by
  obtain ⟨H', cap', heap', owned, ledger, sub⟩ := ret.heap
  exact ⟨H', cap', heap', custom.owned_physical owned ready,
    ret.space space heap named covered keepNamed, ledger, sub⟩

/-- A ready state's table words are inside its physical footprint, so actual
caller byte frames determine the backing-storage addresses as well. -/
theorem CustomMemCall.addresses_frame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    {c d : Config} {k : Nat} (ready : Ready k c)
    (keep : ∀ a, state c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) :
    customBase d = customBase c ∧ customEnd d = customEnd c := by
  apply customAddresses_frame
  intro a ha
  rw [Primitives.byte_total, Primitives.byte_total]
  exact keep a (custom.physical k c ready a (Or.inr (Or.inr (Or.inl ha))))

/-- Selected owned bytes are outside newlib's footprint. -/
theorem CustomMemCall.notFoot {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    {H c} (owned : CustomOwned state H c) {a : Nat} (ha : state c a) :
    ¬ VsaIris.VsaHeap.vsaFoot H a := by
  rintro (global | ⟨low, high, outside⟩)
  · have below : a < Vsa.Sim.DlHeap.heapStart := by
      unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange at global
      unfold Vsa.Sim.DlHeap.heapStart
      omega
    have static := (custom.apart c a ha).static below
    unfold VsaIris.InExt Layout.sym_caml_extra_heap_resources at static
    unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange at global
    omega
  · rcases owned.bytes a ha with below | ⟨e, he, lo, hi⟩
    · omega
    · exact outside e he ⟨lo, by dsimp only at hi; omega⟩

/-- Forget physical return evidence for clients that only need the ordinary
allocator post. The counted execution remains the source of the summary. -/
theorem CustomMemCall.call_forget {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    (H : List (Nat × Nat)) (cap : Nat) (site : CustomMemSite) (k : Nat) (f : Config)
    (ready : Ready (k + 1) f) (input : CustomMemInput H cap site f) (owned : CustomOwned state H f) :
    FnSummary customMemEntry (fun d => d = f)
      (fun d => ∃ v, CustomMemReturned state H site v f d ∧ Ready k d) := by
  apply (custom.call H cap site k f ready input owned).weaken (fun _ h => h)
  intro d ⟨v, returned, readyD⟩
  exact ⟨v, returned.toCustomMemReturned, readyD⟩

/-- Shared framing of readiness and physical accounting from the same byte
and domain observations. Refcount stores are outside this state. -/
theorem CustomMemCall.frame_counted {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} (custom : CustomMemCall Ready state Customs)
    (k : Nat) (c d : Config) (ready : Ready k c)
    (memory : ∀ a, state c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state) :
    CustomFramed Ready state Customs k c d := by
  obtain ⟨readyD, stateD⟩ := custom.frame k c d ready memory domain
  refine ⟨readyD, stateD, ?_, custom.addresses_frame ready memory⟩
  constructor
  intro n h
  simpa only [Nat.add_zero] using custom.accounting.frame h memory domain

abbrev CustomMemCall.Accounting := CustomAccounting

/-- A physical count plus the successful successor's bound supplies readiness. -/
theorem CustomMemCall.Accounting.ready_of_bound
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (accounting : CustomMemCall.Accounting Ready state Customs) {c : Config} {n k : Nat}
    (count : Customs c n) (bound : n + k ≤ quietBound) : Ready k c :=
  accounting.ready ⟨n, count, bound⟩

end OCaml.Vm.Gc
