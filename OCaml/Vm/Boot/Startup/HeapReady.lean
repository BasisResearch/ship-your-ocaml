import OCaml.Vm.Boot.Startup.RuntimeReady
import OCaml.Vm.Boot.WhileMin
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- The memory-only part of `RuntimeReady`: the newlib heap's shape and room
for the live blocks `H`, the allocator's code bytes, the published
`Caml_state` word and the disabled pool.

The heap shape reads only the allocator's globals and the arena bytes
outside every live block (`vsaFoot H`: chunk headers, free chunks, the top
chunk). It never reads live payload bytes, so any write inside a live
block's `[p, p + n)` keeps it. -/
structure HeapReady (H : List (Nat × Nat)) (capacity : Nat) (c : Config) : Prop where
  room : vsaRoomB ((vsaModel startupLive).mem c) H capacity
  text : ∀ pin ∈ VsaIris.Sym.allocText, (c.σ.mem[pin.1]?).getD 0 = pin.2
  domainWord : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr
  poolZero : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)

theorem RuntimeReady.heap {H capacity sp ra c} (ready : RuntimeReady H capacity sp ra c) :
    HeapReady H capacity c :=
  ⟨ready.room, ready.readOnly.2, ready.domainWord, ready.poolZero⟩

/-- Readiness from the heap part and the caller's register state. -/
theorem RuntimeReady.of_heap {H capacity sp ra c} (heap : HeapReady H capacity c) (leaf : LeafInput ra c)
    (platform : VsaOk startupLive c)
    (gp : ∀ p ∈ VsaIris.MallocFast.roR, (vsaModel startupLive).reg c p.1 = p.2)
    (stack : gprGet c.σ 2 = some sp) : RuntimeReady H capacity sp ra c where
  toLeafInput := leaf
  platform := platform
  readOnly := ⟨gp, heap.text⟩
  room := heap.room
  stack := stack
  domainWord := heap.domainWord
  poolZero := heap.poolZero
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMin
open Startup

/-- **The newlib heap at the captured cut** (named obligation, a0-boot).
Some live-block list and a capacity of at least 2^24 bytes (16 MiB) satisfy
`HeapReady` at the densified cut. The reset route discharges it when it
reaches the cut, by `RuntimeReady.heap`. a6-gc's write barrier
(`caml_realloc_ref_table` → `caml_stat_alloc_noexc`) depends on it. At the
cut `top` = 0x80391310 and the break is 0x803a4000, against
`heapEnd` = 0x86800000, so about 105 MB above top remain. -/
def cut_heapReady_Statement : Prop :=
  ∃ H capacity, 2 ^ 24 ≤ capacity ∧ HeapReady H capacity (Vsa.Densify.fillZero cut)
end OCaml.Vm.Boot.WhileMin
