import OCaml.Vm.Sim.OpenOutReturn
import OCaml.Vm.Sim.OutListF1Runtime

/-! Reconstruct the opening runtime from its actual input and selected native return. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives Channel Gc
open OutListWalk

/-- Kept runtime reads miss the opening's two errno stores. The mutable
opened-list head is excluded separately at each core read. -/
theorem opening_kept_statics : ∀ w ∈ keptFootprint,
    (w.hi ≤ 0x80064668 ∨ 0x8006466c ≤ w.lo) ∧
    (w.hi ≤ 0x80064d48 ∨ 0x80064d4c ≤ w.lo) := by decide

section Actual
variable {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
  {code : OpenCode} {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {k : Nat}
  {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
  (custom : CustomMemCall Ready state Customs)
  (o : OpenedOut code imageLive Ready state Customs k H (cap - 65616) 65616 sp ra s0 s1 s2 v head c d)
  (heap : LibHeapAt H cap chs c)
  (h : OutInput imageLive H (cap - 65616) 65616 sp ra s0 s1 s2 v head c)
  (N : OutNursery H chs c)

include custom o heap h N

/-- The real remembered-table words survive the opening and native custom call. -/
theorem opening_table_frame : ∀ a, InTableWords a →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
  intro a table
  have field : ∀ off ∈ [Layout.off_ref_table, Layout.off_minor_heap_wsz],
      Boot.WhileMinRuntime.domain + off ≤ a → a < Boot.WhileMinRuntime.domain + off + 8 →
      (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    intro off member lo hi
    obtain ⟨fits, young, _, extra⟩ := listing_table_domain_fields off member
    exact domainField_kept custom o h N fits young extra lo hi
  rcases table with pointer | str | wsz
  · exact field _ (by simp) pointer.1 pointer.2
  · have member : (refTable, 56) ∈ f1Covered := by simp [f1Covered]
    have minor := f1Covered_minor _ member (by decide)
    exact covered_kept custom o heap h member (by decide) str
      (block_of_outside_minor N.low N.high (by dsimp only at minor; omega))
  · exact field _ (by simp) wsz.1 wsz.2

/-- All core pin reads are framed by the actual native stack, fresh record,
selected caller regions and custom footprint. -/
theorem opening_core_frame : ∀ x n, InKept x n →
    (x + n ≤ Layout.sym_caml_all_opened_channels ∨ Layout.sym_caml_all_opened_channels + 8 ≤ x) → bytesT d.σ.mem x n = bytesT c.σ.mem x n := by
  intro x n inside outside
  apply Reloc.bytesT_congr
  intro j hj
  let a := x + j
  by_cases limit : f1Domain ≤ a ∧ a < f1Domain + 8
  · have limitWord : word d f1Domain = word c f1Domain := by
      apply BitVec.eq_of_toNat_eq
      have same := o.youngLimit
      simpa only [runtimeFields, domainWord, o.domain, h.domain, Layout.off_young_limit,
        Nat.add_zero, f1Domain] using same
    have same := byte_of_bytesT limitWord (i := a - f1Domain) (by omega)
    have address : f1Domain + (a - f1Domain) = a := by omega
    rw [address] at same
    dsimp only [a] at same
    simp only [bytesT, same]
  have point : InKept a 1 := listing_kept_byte inside hj
  obtain ⟨w, member, lo, hi⟩ := point
  have bound := listing_kept_bounds w member
  have minor := listing_kept_minor w member
  have young := listing_kept_young w member
  have statics := opening_kept_statics w member
  obtain ⟨foot, stateA⟩ := listing_kept_owned custom heap ⟨w, member, lo, hi⟩
  have lower := h.frame.lower
  have lowM := N.low
  have highM := N.high
  have freshOut : a < o.opening.record.toNat ∨ o.opening.record.toNat + recordBytes ≤ a := by
    rcases List.mem_append.mp member with static | dynamic
    · have below := staticKept_below w static
      have low := o.opening.low
      have arena : Layout.sym_bss_end ≤ DlHeap.heapStart := by decide
      exact Or.inl (by omega)
    · obtain ⟨e, he, el, eh⟩ := listing_dynamic_covered w dynamic
      have apart := fresh_apart_covered o.opening.fresh (heap.extents e he)
        (covered_pos e he) (n := recordBytes) (by decide) (Nat.le_refl _)
      omega
  have headOut : head ≠ 0#64 → a < head.toNat + 56 ∨ head.toNat + 64 ≤ a := by
    intro nonzero
    have record := head_mem heap.channels h.headWord nonzero
    rcases List.mem_append.mp member with static | dynamic
    · obtain ⟨e, he, el, eh⟩ := heap.records _ record
      have low := (heap.ready.block_bounds he).1
      have below := staticKept_below w static
      have arena : Layout.sym_bss_end ≤ DlHeap.heapStart := by decide
      exact Or.inl (by omega)
    · obtain ⟨e, he, el, eh⟩ := listing_dynamic_covered w dynamic
      have apart := heap.recordsApart _ record e he
      have size : 64 ≤ chanRecordBytes := by decide
      omega
  have headAway : a < 0x80064b40 ∨ 0x80064b48 ≤ a := by
    dsimp only [a]
    simp only [Layout.sym_caml_all_opened_channels] at outside
    omega
  have equality := o.kept a stateA foot
    (outW_openWindows_static h.frame (by omega) (by omega) (by omega) headAway freshOut headOut)
    (Or.inl (by omega)) (by omega) (by
      unfold domainAddr; rw [h.domain]
      have dom : Boot.WhileMinRuntime.domain = f1Domain := rfl
      rw [dom]
      simp only [Layout.off_young_ptr]
      omega)
  dsimp only [a] at equality
  simp only [bytesT, equality]

/-- One actual selected spatial return supplies every heap field, including
credit after the real record charge and dynamic remembered/custom separation. -/
theorem opening_restore_heap (bound : chs.length < maxChannels) :
    ∃ H' capacity, LibHeapAt H' capacity (o.opening.record.toNat :: chs) d := by
  obtain ⟨H', capacity, ready, _physical, space, named, ledger, retained, spending⟩ :=
    o.spatial_heap custom heap h N
  have sub : ∀ e ∈ H, e ∈ H' := fun e he => retained e (List.mem_cons_of_mem _ he)
  have tableFrame := opening_table_frame custom o heap h N
  have links : ∀ b ∈ chs, bytesT d.σ.mem (b + chanOffNext) 8 = bytesT c.σ.mem (b + chanOffNext) 8 := by
    intro b hb
    apply Reloc.bytesT_congr
    intro j hj
    have size : 56 ≤ chanRecordBytes := by decide
    have same := record_kept custom o heap h N hb (x := b + chanOffNext + j)
      (by simp only [chanOffNext]; omega) (by simp only [chanOffNext]; omega)
      (fun _ => Or.inl (by simp only [chanOffNext]; omega))
    simp only [bytesT, same]
  have big : chanRecordBytes ≤ recordBytes := by decide
  have blocked : ∀ e ∈ namedBlocked (o.opening.record.toNat :: chs) d,
      e ∈ (o.opening.record.toNat, chanRecordBytes) :: namedBlocked chs c := by
    intro e he
    simp only [namedBlocked, structWord_keep tableFrame (off := Layout.off_ref_table_base) (by decide),
      structWord_keep tableFrame (off := Layout.off_ref_table_end) (by decide), List.map_cons,
      List.mem_append, List.mem_cons] at he ⊢
    rcases he with (fixed | new | old) | storage
    · exact Or.inr (Or.inl (Or.inl fixed))
    · exact Or.inl new
    · exact Or.inr (Or.inl (Or.inr old))
    · exact Or.inr (Or.inr storage)
  have credit : Gc.reserved (word d (refTable + Layout.off_ref_table_base)).toNat
      (o.opening.record.toNat :: chs).length + customTableReserve d ≤ capacity := by
    rw [structWord_keep tableFrame (by decide)]
    have before := heap.open_credit bound
    simp only [List.length_cons]
    omega
  refine ⟨H', capacity, {
    room := by omega
    credit := credit
    channelsBound := by simp only [List.length_cons]; omega
    ready := ready
    extents := fun e he => selected_covered_mono (heap.extents e he) sub
    channels := ?_
    records := ?_
    recordsApart := ?_
    recordsDisjoint := ?_
    recordsAligned := ?_
    table := ?_
    tableIn := sub _ heap.tableIn
    named := named.restrict blocked
    custom := ledger
    customSpace := space.restrict blocked
    customRecords := ?_ }⟩
  · unfold OpenChannelList
    rw [o.linked.head, BitVec.toNat_ofNat]
    have small : o.opening.record.toNat < 2 ^ 64 := BitVec.isLt _
    rw [Nat.mod_eq_of_lt small]
    refine .cons o.linked.nonzero ?_
    rw [o.linked.next]
    exact OpenChannels.congr heap.channels links
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, retained _ List.mem_cons_self, Nat.le_refl _, by dsimp only; omega⟩
    · exact selected_covered_mono (heap.records b hb) sub
  · intro b hb e he
    rcases List.mem_cons.mp hb with rfl | hb
    · exact fresh_apart_covered o.opening.fresh (heap.extents e he) (covered_pos e he) record_pos big
    · exact heap.recordsApart b hb e he
  · intro b hb r hr ne
    rcases List.mem_cons.mp hb with eb | hb <;> rcases List.mem_cons.mp hr with er | hr
    · exact absurd (eb.trans er.symm) ne
    · subst eb
      exact fresh_apart_covered o.opening.fresh (heap.records r hr) record_pos record_pos big
    · subst er
      exact (fresh_apart_covered o.opening.fresh (heap.records b hb) record_pos record_pos big).symm
    · exact heap.recordsDisjoint b hb r hr ne
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact o.opening.align
    · exact heap.recordsAligned b hb
  · have t := heap.table.congr tableFrame
    refine ⟨t.pointer, t.minorWsz, ?_⟩
    rcases t.shape with empty | st
    · exact Or.inl empty
    · refine Or.inr { st with covered := selected_covered_mono st.covered sub, apartRecords := ?_ }
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have apart := fresh_apart_covered o.opening.fresh st.covered
          (by have := st.sized; dsimp only; omega) record_pos big
        dsimp only at apart
        omega
      · exact st.apartRecords b hb
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact fresh_apart_covered o.opening.fresh heap.custom.table (by decide) record_pos big
    · exact heap.customRecords b hb

/-- The actual 24-byte nursery decrement preserves RuntimeOk, while f1_core
and the independent native context reconstruct every pin. -/
theorem opening_runtime (ok : f1Runtime c) (bound : chs.length < maxChannels) : f1Runtime d := by
  obtain ⟨H', capacity, restored⟩ := opening_restore_heap custom o heap h N bound
  obtain ⟨pins, fields⟩ := f1_core_except_head (opening_core_frame custom o heap h N)
    (fun _ => ⟨H', capacity, o.opening.record.toNat :: chs, restored⟩) ok.freeListShape
  have young : (word d (f1Domain + Layout.off_young_ptr)).toNat = (runtimeFields c).youngPtr - 24 := by
    have domain := o.domain.trans ok.freeListShape.domain
    have same : (runtimeFields d).youngPtr = (word d (f1Domain + Layout.off_young_ptr)).toNat := by
      simp only [runtimeFields, domainWord, domain]
      rfl
    exact same.symm.trans o.youngPtr
  have old := ok.bounds
  have room := N.room
  refine { bounds := ?_, noPending := ?_, freeListShape := { pins with customPins := o.context custom h N } }
  · rw [fields, young]
    exact { old with
      alloc := by have := old.limitLow; dsimp only; omega
      ptr := by dsimp only; have := old.ptr; omega
      alignedPtr := by dsimp only; have := N.aligned; omega }
  · rw [fields]; exact ok.noPending

end Actual

/-- Concrete opening runtime relative only to the accepted native custom call.
All caller frames are supplied by the existing opening inputs. -/
theorem f1_openOut_runtime {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs) : OpenOutRuntimeAt f1Layout Ready state Customs where
  custom := custom
  customBudget := by decide
  pins := fun _ ok => ok.freeListShape
  after := by
    intro code H cap chs k sp ra s0 s1 s2 v head c d ok heap bound h N o
    exact opening_runtime custom o heap h N ok bound

end OCaml.Vm.Sim
