import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Gc.Generated.CustomReallocEntry
import OCaml.Vm.Gc.Generated.CustomTableGeometry

/-! Allocation credit is distinct from spatial ownership. The request below
comes from the generated custom wrapper and shared null-base route; the native
spending refinement remains an explicit duty of CustomMemCall's supplier. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives Boot.Startup VsaIris.VsaHeap

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

/-- Compatibility view of selected custom credit. LibHeapAt now carries
this same stronger credit in the actual runtime invariant. -/
structure CustomHeapCredit (H : List (Nat × Nat)) (cap : Nat) (chs : List Nat) (c : Config) : Prop where
  selected : LibHeapAt H cap chs c
  credit : reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length + customTableReserve c ≤ cap

/-- Honest projection of the strengthened selected runtime invariant. -/
theorem LibHeapAt.customHeapCredit {H cap chs c} (selected : LibHeapAt H cap chs c) :
    CustomHeapCredit H cap chs c := ⟨selected, selected.credit⟩

/-- The actual startup memory certificate supplies selected initial credit;
this is a memory observation at the cut, not reset-to-cut execution. -/
theorem customHeapCredit_of {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem (Vsa.Sim.Boot.observedMem Boot.WhileMinImage.initialMem Boot.WhileMinLog.log))
    (heap : HeapCovers c) : ∃ H cap, CustomHeapCredit H cap [] c := by
  obtain ⟨H, cap, _, selected⟩ := libHeap_at_of memory heap
  exact ⟨H, cap, selected.customHeapCredit⟩

/-- Ordinary caller windows preserve the extra selected credit, including
both table addressing words; allocator calls need the separate spending law. -/
theorem CustomHeapCredit.frame_windows {H cap chs c d} (h : CustomHeapCredit H cap chs c)
    {ws : List W} (safe : ∀ w ∈ ws, F1HeapSafe w)
    (head : bytesT d.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8)
    (frame : FrameOn ws c.σ.mem d.σ.mem) : CustomHeapCredit H cap chs d :=
  (h.selected.frame_windows safe head frame).customHeapCredit

/-- The old HeapReady numeric projection can advertise exactly ordinary
reserve. It does not preserve the strengthened LibHeapAt credit field. -/
theorem LibHeapAt.tightCapacity {H cap chs c} (h : LibHeapAt H cap chs c) :
    HeapReady H (reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length) c :=
  h.ready.capacity_mono h.room

/-- The old numeric interface admitted exactly ordinary reserve. This explicit
old capacity premise does not describe the strengthened LibHeapAt invariant. -/
theorem LibHeapAt.customCredit_obstruction {H cap chs c} (h : LibHeapAt H cap chs c)
    (empty : customBase c = 0) :
    let advertised := reserved (word c (refTable + Layout.off_ref_table_base)).toNat chs.length
    HeapReady H advertised c ∧ advertised ≤ advertised ∧
      ¬ advertised + customTableReserve c ≤ advertised := by
  refine ⟨h.tightCapacity, Nat.le_refl _, ?_⟩
  have positive : 0 < customTableCharge := by decide
  simp only [customTableReserve, empty, ite_true]
  omega

/-- The uncredited leaf input permits zero advertised capacity while retaining
its native context. CustomMemCall.call separately requires real input credit;
this old projection does not meet that strengthened call contract. -/
theorem CustomMemInput.zeroCapacity {H : List (Nat × Nat)} {cap : Nat} {site : CustomMemSite} {f : Config}
    (input : CustomMemInput H cap site f) : CustomMemInput H 0 site f :=
  { input with heap := input.heap.capacity_mono (Nat.zero_le cap) }

/-- A positive input charge cannot follow from the uncredited leaf input alone.
The witness is conditional; native execution and physical heap size are not refuted. -/
theorem CustomMemInput.credit_obstruction {H : List (Nat × Nat)} {cap : Nat} {site : CustomMemSite} {f : Config}
    (input : CustomMemInput H cap site f)
    (law : ∀ capacity, CustomMemInput H capacity site f → customTableCharge ≤ capacity) : False := by
  have bad := law 0 input.zeroCapacity
  have positive : 0 < customTableCharge := by decide
  omega

/-- The forgetful spatial return can advertise zero. This old projection
does not include CustomMemCountedReturned.credited or its spending law. -/
theorem CustomMemReturned.heap_zero {state : Config → Nat → Prop} {H : List (Nat × Nat)}
    {site : CustomMemSite} {v : BitVec 64} {f d : Config}
    (ret : CustomMemReturned state H site v f d) :
    ∃ H', HeapReady H' 0 d ∧ CustomOwned state H' d ∧ CustomLedger H' d ∧ ∀ e ∈ H, e ∈ H' := by
  obtain ⟨H', cap', heap, owned, ledger, sub⟩ := ret.heap
  exact ⟨H', heap.capacity_mono (Nat.zero_le cap'), owned, ledger, sub⟩

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


end OCaml.Vm.Gc
