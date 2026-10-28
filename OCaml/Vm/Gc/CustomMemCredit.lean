import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Gc.Generated.CustomReallocEntry
import OCaml.Vm.Gc.Generated.CustomTableGeometry

/-! Allocation credit is distinct from spatial ownership. The request below
comes from the generated custom wrapper and shared null-base route; the native
spending refinement remains an explicit duty of CustomMemCall's supplier. -/
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

/-- Exact RV64 request expression at the null-base size-product call. -/
def customTableRequest (wsz : BitVec 64) : BitVec 64 :=
  ((wsz >>> 3) + 256#64) * BitVec.ofNat 64 Layout.custom_elt_size

/-- The generated route's actual __muldi3 operands have this product.
This is a scalar readback from the shared ELF-derived chain, not a malloc run. -/
theorem customTableRequest_operands (sp s0 s3 ra s2 a0 s1 base domain wsz : BitVec 64) :
    let regs := CustomReallocEntry.state3 sp s0 s3 ra s2 a0 s1 base domain wsz
    srcVal 10 regs * srcVal 11 regs = customTableRequest wsz := rfl

theorem customTableRequest_cut : (customTableRequest 0x40000#64).toNat = 792576 := by decide

theorem customTableRequest_charge : vsaChg (customTableRequest 0x40000#64).toNat customTableCharge := by
  unfold vsaChg
  decide

/-- The concrete startup allowance has room for the additional initial
custom-table credit as well as all existing F1 reservations. -/
theorem customTableCredit_startup : reserved 0 0 + customTableCharge ≤ 2 ^ 24 := by decide

/-- Selected extra input credit, separate from the current ordinary LibHeapAt
room field. Its migration into every native custom caller remains required. -/
structure CustomHeapCredit (H : List (Nat × Nat)) (cap : Nat) (chs : List Nat) (c : Config) : Prop where
  selected : LibHeapAt H cap chs c
  credit : reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length + customTableReserve c ≤ cap

/-- The actual startup memory certificate supplies selected initial credit;
this is a memory observation at the cut, not reset-to-cut execution. -/
theorem customHeapCredit_of {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem (Vsa.Sim.Boot.observedMem Boot.WhileMinImage.initialMem Boot.WhileMinLog.log))
    (heap : HeapCovers c) : ∃ H cap, CustomHeapCredit H cap [] c := by
  obtain ⟨H, cap, bound, selected⟩ := libHeap_at_of memory heap
  have base : (word c (refTable + Layout.off_ref_table_base)).toNat = 0 := by
    rw [show refTable = Boot.WhileMinHeapChunks.refTablePayload from rfl, Boot.WhileMinEntry.read_ref_table_base memory]
    rfl
  have custom : customBase c = 0 := by
    unfold customBase customTable
    rw [Boot.WhileMinRuntime.read_custom_table_base memory]
    rfl
  refine ⟨H, cap, ⟨selected, ?_⟩⟩
  simp only [customTableReserve, custom, ite_true, base, List.length_nil]
  exact Nat.le_trans customTableCredit_startup bound

/-- Ordinary caller windows preserve the extra selected credit, including
both table addressing words; allocator calls need the separate spending law. -/
theorem CustomHeapCredit.frame_windows {H cap chs c d} (h : CustomHeapCredit H cap chs c)
    {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT d.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (frame : FrameOn ws c.σ.mem d.σ.mem) : CustomHeapCredit H cap chs d := by
  have table : ∀ a, InTableWords a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    intro a ha
    exact congrArg (fun x => x.getD 0) (frame a (outW_all fun w hw => (safe w hw).misses_table ha))
  have custom : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a → byte d a = byte c a := by
    intro a ha
    rw [byte_total, byte_total]
    exact congrArg (fun x => x.getD 0) (frame a (outW_all fun w hw => (safe w hw).custom_out ha))
  obtain ⟨base, _⟩ := customAddresses_frame custom
  refine ⟨h.selected.frame_windows safe head frame, ?_⟩
  rw [structWord_keep table (off := Layout.off_ref_table_base) (by decide)]
  simpa only [customTableReserve, base] using h.credit

/-- Ordinary heap ownership can advertise exactly its existing reserve, so
an additional custom-table charge cannot be inferred for that selected cap. -/
theorem LibHeapAt.tightCapacity {H cap chs c} (h : LibHeapAt H cap chs c) :
    LibHeapAt H (reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length) chs c :=
  { h with room := Nat.le_refl _, ready := h.ready.capacity_mono h.room }

/-- Conditional obstruction for the current selected input credit. No actual
allocation shortage or reachable-state counterexample is claimed. -/
theorem LibHeapAt.customCredit_obstruction {H cap chs c} (h : LibHeapAt H cap chs c)
    (empty : customBase c = 0) :
    let advertised := reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length
    LibHeapAt H advertised chs c ∧ ¬ CustomHeapCredit H advertised chs c := by
  refine ⟨h.tightCapacity, ?_⟩
  intro credit
  have impossible := credit.credit
  have positive : 0 < customTableCharge := by decide
  simp only [customTableReserve, empty, ite_true] at impossible
  omega

/-- The current input permits zero advertised capacity while retaining every
leaf/register/frame/nursery fact. This does not assert a reachable shortage. -/
theorem CustomMemInput.zeroCapacity {H : List (Nat × Nat)} {cap : Nat} {site : CustomMemSite} {f : Config}
    (input : CustomMemInput H cap site f) : CustomMemInput H 0 site f :=
  { input with heap := input.heap.capacity_mono (Nat.zero_le cap) }

/-- A positive input charge cannot follow from the current input contract.
The witness is conditional; native execution and physical heap size are not refuted. -/
theorem CustomMemInput.credit_obstruction {H : List (Nat × Nat)} {cap : Nat} {site : CustomMemSite} {f : Config}
    (input : CustomMemInput H cap site f)
    (law : ∀ capacity, CustomMemInput H capacity site f → customTableCharge ≤ capacity) : False := by
  have bad := law 0 input.zeroCapacity
  have positive : 0 < customTableCharge := by decide
  omega

/-- Every returned heap witness may advertise zero. Spatial postconditions
therefore do not themselves bound the capacity chosen by a spending supplier. -/
theorem CustomMemReturned.heap_zero {state : Config → Nat → Prop} {H : List (Nat × Nat)}
    {site : CustomMemSite} {v : BitVec 64} {f d : Config}
    (ret : CustomMemReturned state H site v f d) :
    ∃ H', HeapReady H' 0 d ∧ CustomOwned state H' d ∧ CustomLedger H' d ∧ ∀ e ∈ H, e ∈ H' := by
  obtain ⟨H', cap', heap, owned, ledger, sub⟩ := ret.heap
  exact ⟨H', heap.capacity_mono (Nat.zero_le cap'), owned, ledger, sub⟩

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

/-- Real caller frame producer for unchanged allocation credit. The actual
selected frame preserves the custom addressing words as well as allocator shape. -/
theorem CustomHeapCredit.spending_frame {H cap chs c d} (h : CustomHeapCredit H cap chs c)
    {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT d.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (frame : FrameOn ws c.σ.mem d.σ.mem) : CustomMemSpending H H cap cap c d := by
  have after := h.frame_windows safe head frame
  have custom : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a → byte d a = byte c a := by
    intro a ha
    rw [byte_total, byte_total]
    exact congrArg (fun x => x.getD 0) (frame a (outW_all fun w hw => (safe w hw).custom_out ha))
  obtain ⟨base, _⟩ := customAddresses_frame custom
  exact ⟨after.selected.ready, after.selected.custom, fun _ member => member,
    by simp only [customTableReserve, base]; exact Nat.le_refl _⟩

/-- With real input credit and returned spending, ordinary future reserves
survive. The native supplier still owes both physical spending and table pins. -/
theorem CustomMemSpending.room {H H' : List (Nat × Nat)} {cap cap' ordinary : Nat} {f d : Config}
    (spent : CustomMemSpending H H' cap cap' f d)
    (credit : ordinary + customTableReserve f ≤ cap) :
    ordinary + customTableReserve d ≤ cap' := by
  have := spent.spend
  omega

end OCaml.Vm.Gc
