import OCaml.Vm.Primitives.Leaf
import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Gc.NurseryDefs
import OCaml.Vm.Boot.Startup.HeapReady
import OCaml.Vm.Gc.F1Heap

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
(`caml_extra_heap_resources` grows by `57424/297968` per call, and the sixth
since the cut requests a major slice). newlib's heap enters as `HeapReady H cap`
at the call and returns as `HeapReady H' cap'` over every block of `H` (the
first call since the cut adds the custom table's block), so a caller with
several calls (`caml_ml_out_channels_list`) chains it. `Ready` reads only the
runtime's own state (`CustomMemCall.state`): the static
`caml_extra_heap_resources`, the domain's `extra_heap_resources_minor`, and the
custom table's struct and storage (live blocks of newlib's heap). It lies apart
from what callers write (`CallerApart`):
* newlib's free space and allocator globals;
* F1's covered regions other than the domain record;
* the native stack;
* the minor heap;
* the open channel records;
* the domain's `young_ptr`, `young_limit` and `local_roots` words.

Callers therefore keep `Ready` across their own stores (`CustomMemRuntime.frame`).
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
  records : ∀ chs, OpenChannelList c.σ.mem chs → ∀ r ∈ chs, a < r ∨ r + chanOffBuff + OCaml.Bytecode.ioBufferSize ≤ a
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
  /-- in live blocks or statics, never newlib's free space or globals -/
  free : ∀ H cap, HeapReady H cap c → ¬ VsaIris.VsaHeap.vsaFoot H a

/-- At the call: the link and argument registers, the callee's stack room,
and nursery room for the block (`caml_alloc_small`'s fast path). -/
structure CustomMemInput (H : List (Nat × Nat)) (cap : Nat) (site : CustomMemSite) (f : Config) : Prop where
  leaf : LeafInput site.link f
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
  first call), ready for the next call -/
  heap : ∃ H' cap', HeapReady H' cap' d ∧ ∀ e ∈ H, e ∈ H'
  kept : ∀ a, ¬ state f a → ¬ VsaIris.VsaHeap.vsaFoot H a →
    (a < site.sp.toNat - customStackBytes ∨ site.sp.toNat ≤ a) →
    (a + 24 < (runtimeFields f).youngPtr ∨ (runtimeFields f).youngPtr ≤ a) →
    (a + 8 ≤ domainAddr f Layout.off_young_ptr ∨ domainAddr f Layout.off_young_ptr + 8 ≤ a) →
    (d.σ.mem[a]?).getD 0 = (f.σ.mem[a]?).getD 0

/-- **The runtime's channel custom allocations** (named obligation, lane
a6-gc). `Ready k c`: `k` more calls are safe at `c`, judged from `state c`
alone: the bytes `Ready` reads and the call may write besides its stack, the
block, `young_ptr` and newlib's own bytes (`vsaFoot H`): the counters and the
custom table. -/
structure CustomMemCall (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) : Prop where
  apart : ∀ c a, state c a → CallerApart c a
  /-- a caller's stores outside the runtime's state keep it ready -/
  frame : ∀ k c c', Ready k c → (∀ a, state c a → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) →
    word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state → Ready k c' ∧ (∀ a, state c' a ↔ state c a)
  call : ∀ (H : List (Nat × Nat)) (cap : Nat) (site : CustomMemSite) (k : Nat) (f : Config),
    Ready (k + 1) f → CustomMemInput H cap site f →
    FnSummary customMemEntry (fun d => d = f)
      (fun d => ∃ v, CustomMemReturned state H site v f d ∧ Ready k d)

end OCaml.Vm.Gc
