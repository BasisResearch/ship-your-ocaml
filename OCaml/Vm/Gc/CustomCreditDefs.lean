import OCaml.Vm.Gc.Generated.CustomTableGeometry
import OCaml.Vm.Gc.CustomLedger
import OCaml.Vm.Boot.Startup.HeapReady

/-! Selected native custom capacity accounting, below the runtime and callers. -/
namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine

/-- Heap readiness is downward closed in advertised capacity. It cannot
supply a positive numeric input-credit premise on its own. -/
theorem HeapReady.capacity_mono {H : List (Nat × Nat)} {cap small : Nat} {c : Config}
    (heap : HeapReady H cap c) (bound : small ≤ cap) : HeapReady H small c where
  room := by
    obtain ⟨starts, m, top, brk, chunks, bins, image, shape, room⟩ := heap.room
    exact ⟨starts, m, top, brk, chunks, bins, image, shape, by omega⟩
  text := heap.text
  domainWord := heap.domainWord
  poolZero := heap.poolZero

end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives Boot.Startup VsaIris.VsaHeap

/-- Independent initial backing-table credit, in addition to remembered-set
and future channel-record reservations. -/
def customTableCharge : Nat := 2 ^ 20

def customTableReserve (c : Config) : Nat := if customBase c = 0 then customTableCharge else 0

/-- Only the actual backing-base observation determines the one-time credit. -/
theorem customTableReserve_congr {c d : Config} (base : customBase d = customBase c) :
    customTableReserve d = customTableReserve c :=
  congrArg (fun b => if b = 0 then customTableCharge else 0) base

/-- Register-only execution preserves the backing-table reserve. -/
theorem customTableReserve_of_mem {c d : Config} (memory : d.σ.mem = c.σ.mem) :
    customTableReserve d = customTableReserve c := by
  unfold customTableReserve customBase word
  rw [memory]

/-- Finite G1 channel-custom budget. The rational inequality below does
not prove actual binary64 rounding or native threshold branches; those remain
part of the accepted native call obligation. -/
def quietBound : Nat := 5

theorem quietBound_spec : quietBound * 57424 ≤ 297968 ∧ 297968 < (quietBound + 1) * 57424 := by decide

/-- A domain word's address at `c`. -/
def domainAddr (c : Config) (offset : Nat) : Nat :=
  (word c Layout.sym_Caml_state).toNat + offset

/-- Full actual table-addressing observations needed to rule out a later
reallocation. Occupancy by itself supplies none of these pins. A concrete
physical Customs producer must establish and preserve them. -/
structure CustomTableShape (c : Config) (count : Nat) : Prop where
  base : customBase c ≠ 0
  pointer : (word c (customTable + Layout.off_custom_table_ptr)).toNat =
    customBase c + count * Layout.custom_elt_size
  threshold : (word c (customTable + CustomTable.off_threshold)).toNat =
    customBase c + (0x40000 / 8) * Layout.custom_elt_size
  limit : word c (customTable + CustomTable.off_limit) = word c (customTable + CustomTable.off_threshold)
  ending : customEnd c = customBase c + (0x40000 / 8 + 256) * Layout.custom_elt_size
  size : word c (customTable + CustomTable.off_size) = 32768#64
  reserve : word c (customTable + CustomTable.off_reserve) = 256#64

/-- Full quiet addressing combines mutable table shape with separately
preserved read-only runtime identity and nursery parameters. -/
structure QuietCustomTable (c : Config) (count : Nat) : Prop extends CustomTableShape c count where
  tableWord : word c (domainAddr c Layout.off_custom_table) = BitVec.ofNat 64 customTable
  nurseryWords : word c (domainAddr c Layout.off_minor_heap_wsz) = 0x40000#64

/-- At the quiet bound the actual ptr is strictly below the actual limit. -/
theorem QuietCustomTable.not_full {c : Config} {count : Nat}
    (shape : QuietCustomTable c count) (quiet : count ≤ quietBound) :
    (word c (customTable + Layout.off_custom_table_ptr)).toNat <
      (word c (customTable + CustomTable.off_limit)).toNat := by
  rw [shape.pointer, shape.limit, shape.threshold]
  have bound : quietBound = 5 := rfl
  have size : Layout.custom_elt_size = 24 := rfl
  rw [size]
  omega

/-- Missing native capacity component, indexed by the actual input/returned
ledgers and advertised capacities. Its supplier must use actual allocation
spending and the physical table shape (including quiet no-growth), not an
arbitrary HeapReady witness. This is a specification, not a new trust axiom. -/
structure CustomMemSpending (H H' : List (Nat × Nat)) (cap cap' : Nat) (f d : Config) : Prop where
  heap : HeapReady H' cap' d
  ledger : CustomLedger H' d
  retained : ∀ e ∈ H, e ∈ H'
  spend : cap + customTableReserve d ≤ cap' + customTableReserve f

/-- Native spending composes across the actual selected intermediate ledger;
the one-time custom-table reserve cancels at the intermediate state. -/
theorem CustomMemSpending.trans {H H' H'' : List (Nat × Nat)} {cap cap' cap'' : Nat} {c d e : Config}
    (first : CustomMemSpending H H' cap cap' c d)
    (second : CustomMemSpending H' H'' cap' cap'' d e) : CustomMemSpending H H'' cap cap'' c e where
  heap := second.heap
  ledger := second.ledger
  retained := fun block member => second.retained block (first.retained block member)
  spend := by have := first.spend; have := second.spend; omega

/-- With real input credit and returned spending, ordinary future reserves
survive. The native supplier still owes both physical spending and table pins. -/
theorem CustomMemSpending.room {H H' : List (Nat × Nat)} {cap cap' ordinary : Nat} {f d : Config}
    (spent : CustomMemSpending H H' cap cap' f d)
    (credit : ordinary + customTableReserve f ≤ cap) :
    ordinary + customTableReserve d ≤ cap' := by
  have := spent.spend
  omega

end OCaml.Vm.Gc
