import OCaml.Vm.Repr.ChannelCounts
import OCaml.Vm.Boot.WhileMinRuntimeReads
import OCaml.Vm.Boot.WhileMinEntryReads
import OCaml.Vm.Boot.WhileMinAllocator

/-! A physical count component for G1's channel allocations. The custom
table's occupied entries count allocations independently of channel refcount
stores. This component alone does not constrain GC resource accumulators or
the current domain's table pointer, and is not a complete instantiation of
`CustomMemCall`'s accounting predicate. A complete physical runtime predicate
still needs those facts and their startup/frame/call producers. No readiness
or machine transition is inferred from occupancy alone. -/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.Boot Boot.WhileMinLog

/-- Entries occupied in the actual custom table allocated by startup. G1
does not clear that table. Base and insertion pointer are natural addresses,
so this equality excludes subtraction underflow and modular wrap. -/
structure ChannelCustomCount (c : Config) (n : Nat) : Prop where
  occupied : (word c (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_base)).toNat +
    Layout.custom_elt_size * n =
    (word c (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_ptr)).toNat

/-- The two physical words read by the count, separate from channel records. -/
def ChannelCustomCountFoot (a : Nat) : Prop :=
  (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_base ≤ a ∧
    a < Boot.WhileMinRuntime.customTable + Layout.off_custom_table_base + 8) ∨
  (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_ptr ≤ a ∧
    a < Boot.WhileMinRuntime.customTable + Layout.off_custom_table_ptr + 8)

theorem ChannelCustomCount.unique {c : Config} {n m : Nat}
    (h : ChannelCustomCount c n) (h' : ChannelCustomCount c m) : n = m := by
  have size : Layout.custom_elt_size = 24 := rfl
  have hn := h.occupied
  have hm := h'.occupied
  rw [size] at hn hm
  omega

/-- An observation frame preserves occupancy, without inspecting refcounts. -/
theorem ChannelCustomCount.frame {c d : Config} {n : Nat} (h : ChannelCustomCount c n)
    (same : ∀ a, ChannelCustomCountFoot a → byte d a = byte c a) :
    ChannelCustomCount d n := by
  have base : word d (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_base) =
      word c (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_base) := by
    apply Reloc.bytesT_congr
    intro j hj
    exact same _ (Or.inl ⟨by omega, by omega⟩)
  have ptr : word d (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_ptr) =
      word c (Boot.WhileMinRuntime.customTable + Layout.off_custom_table_ptr) := by
    apply Reloc.bytesT_congr
    intro j hj
    exact same _ (Or.inr ⟨by omega, by omega⟩)
  exact ⟨by rw [base, ptr]; exact h.occupied⟩

/-- The checked startup memory contains the actual empty custom table.
As with other startup reads, execution to this memory is a separate gate. -/
theorem ChannelCustomCount.startup {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem Boot.WhileMinImage.initialMem log)) :
    ChannelCustomCount c 0 := by
  constructor
  rw [Boot.WhileMinRuntime.read_custom_table_base memory,
    Boot.WhileMinRuntime.read_custom_table_ptr memory]
  rfl

/-- Initial ownership uses the closed in-use chunk ledger, rather than the
empty ledger that also satisfies allocator readiness. The fixed table is
the startup table (`WhileMinRuntime.read_custom_table`); its observed null
base owns no storage. The domain pointer is not added to the framed state. -/
theorem customLedger_startup {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem Boot.WhileMinImage.initialMem log)) :
    CustomLedger Boot.WhileMinAllocator.liveBlocks c := by
  refine ⟨?_, ?_, Or.inl ?_⟩
  · unfold Covered
    decide +kernel
  · unfold Covered
    decide +kernel
  · unfold customBase customTable
    rw [Boot.WhileMinRuntime.read_custom_table_base memory]
    rfl

/-- Occupancy's physical reads are owned by the selected custom ledger. -/
theorem ChannelCustomCountFoot.owned {H : List (Nat × Nat)} {c : Config}
    (heap : CustomLedger H c) {a : Nat} (foot : ChannelCustomCountFoot a) :
    Covered H (a, 1) := by
  obtain ⟨e, he, lo, hi⟩ := heap.table
  have bounds : customTable ≤ a ∧ a < customTable + Layout.custom_table_bytes := by
    rcases foot with base | ptr
    all_goals
      simp only [customTable, Layout.off_custom_table_base, Layout.off_custom_table_ptr,
        Layout.custom_table_bytes] at *
      omega
  exact ⟨e, he, by dsimp only; omega, by dsimp only; omega⟩


/-- Complete initial channel accounting from concrete startup reads. -/
theorem channelCustoms_startup {c : Config} {cp : ChanPlace} {w : World}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem Boot.WhileMinImage.initialMem log))
    (empty : w.chans = []) : ChannelCustomsRepr ChannelCustomCount c cp w :=
  ChannelCustomsRepr.empty empty (.startup memory)
    (Boot.WhileMinEntry.read_caml_all_opened_channels memory)

end OCaml.Vm.Gc
