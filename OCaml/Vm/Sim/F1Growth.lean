import OCaml.Vm.Sim.BarrierKeep
import OCaml.Vm.Gc.F1Grow
import OCaml.Vm.Sim.F1BarrierRuntime

/-!
# The represented payload across the remembered set's growth (F1)

`observed_kept`: every byte the represented barrier state reads
(`BarrierObserved`) is one the growth call keeps (`Realloc.Kept`): static
words outside newlib's allocator, the runtime's live blocks other than the
remembered-set struct (the `Caml_state` record, code, VM stack, heap chunks,
channel records, primitive table), and the invocation's native words above the
barrier's `sp`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  VsaIris.VsaHeap OCaml.Vm.Gc

theorem barrierStatics_kept : ∀ a ∈ barrierStatics, ∀ x, a ≤ x → x < a + 8 → x < heapStart ∧ ¬ allocGlobal x := by
  intro a ha x lo hi
  simp only [barrierStatics, List.mem_cons, List.not_mem_nil, or_false] at ha
  refine ⟨?_, fun g => ?_⟩
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
        Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_caml_all_opened_channels,
        Layout.sym_caml_prim_table, Layout.off_prim_contents, heapStart] at hi ⊢ <;> omega
  · unfold allocGlobal InRange at g
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
        Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_caml_all_opened_channels,
        Layout.sym_caml_prim_table, Layout.off_prim_contents] at lo hi <;> omega

/-- **Every byte the represented barrier state reads is kept by the growth call.** -/
theorem observed_kept {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    {D : InvocationData} {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat}
    (ok : f1Runtime c) (h : LibHeapAt H cap chs c) (g : OCaml.LoopGeometry f1Layout P s c pl cp high)
    (data : VmPayload P s c pl cp sp high) (low : high - Layout.stackBytes ≤ sp) (small : D.nativeSp < 2 ^ 64) :
    ∀ x, BarrierObserved P s c pl cp sp D x → Realloc.Kept H (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 refTable) x := by
  have region : ∀ y ∈ f1Covered, (y.1 + y.2 ≤ refTable ∨ refTable + 56 ≤ y.1 ∨ y = (refTable, 56)) := by decide
  /- a byte of a covered runtime block other than the struct -/
  have block : ∀ y ∈ f1Covered, y ≠ (refTable, 56) → ∀ x, y.1 ≤ x → x < y.1 + y.2 →
      Realloc.Kept H (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 refTable) x := by
    intro y hy ne x lo hi
    refine kept_covered h (h.extents y hy) lo hi ?_
    rcases region y hy with r | r | r
    · left; omega
    · right; omega
    · exact absurd r ne
  have highEq : high = f1High := by rw [← data.stackHigh, f1_stackHigh ok]
  have codeBase : pl.codeBase = Boot.WhileMinHeapChunks.codeBufferPayload := by
    rw [← data.codeBase, ok.freeListShape.codeWord]; simp [Boot.WhileMinHeapChunks.codeBufferPayload]
  have prims : (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat =
      Boot.WhileMinHeapChunks.primTablePayload := by
    rw [ok.freeListShape.primsWord]; simp [Boot.WhileMinHeapChunks.primTablePayload]
  have codeFits := g.nursery.codeFits
  have primsFit := g.nursery.primsFit
  obtain ⟨len, -⟩ := data.stack
  intro x obs
  cases obs with
  | static ha span =>
    obtain ⟨l, u⟩ := barrierStatics_kept _ ha x span.1 span.2
    exact Gc.kept_static l u
  | domain span =>
    rw [f1_domain ok] at span
    exact block _ List.mem_cons_self (by decide) x span.1 span.2
  | code hc span =>
    have hi := lt_size_of_getElem? hc
    rw [codeBase] at span
    exact block (Boot.WhileMinHeapChunks.codeBufferPayload, f1CodeBytes) (by decide) (by decide) x
      (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [f1CodeBytes] at *; omega)
  | stack hs span =>
    have hi := (List.getElem?_eq_some_iff.1 hs).1
    rw [highEq] at low len
    exact block (f1High - Layout.stackBytes, Layout.stackBytes) (by decide) (by decide) x
      (by dsimp only; have := span.1; omega)
      (by dsimp only; have := span.2; simp only [f1High, Boot.WhileMinEntry.high, Layout.stackBytes] at *; omega)
  | header ho hp span =>
    rcases g.nursery.heapChunks _ _ _ hp ho with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact block (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [minorRegion] at *; omega)
    · exact block (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [majorRegion] at *; omega)
  | fields ho hp span =>
    rcases g.nursery.heapChunks _ _ _ hp ho with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact block (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [minorRegion] at *; omega)
    · exact block (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [majorRegion] at *; omega)
  | channel hc hp span =>
    obtain ⟨chs', list, placed, -⟩ := g.nursery.channelsListed
    have ha := placed _ _ _ hc hp
    rw [h.records_of list] at ha
    have st := h.recordsApart _ ha (refTable, 56) (by decide)
    dsimp only at st
    refine kept_covered h (h.records _ ha) span.1 (by dsimp only; have := span.2; unfold chanRecordBytes; omega) ?_
    have := span.1; have := span.2
    rcases st with o | o
    · left; unfold chanRecordBytes at o; omega
    · right; omega
  | prim hn span =>
    have hi := lt_size_of_getElem? hn
    rw [prims] at span
    exact block (Boot.WhileMinHeapChunks.primTablePayload, 8 * f1PrimCapacity) (by decide) (by decide) x
      (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [f1PrimCapacity] at *; omega)
  | native hr span =>
    left
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    have := span.1
    omega

/-- `Table`'s words determine the table. -/
theorem table_unique {dom tbl ptr limit tbl' ptr' limit' : BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)}
    (t : Gc.Barrier.Table dom tbl ptr limit m) (t' : Gc.Barrier.Table dom tbl' ptr' limit' m) :
    tbl = tbl' ∧ ptr = ptr' ∧ limit = limit' := by
  have e : tbl = tbl' := t.tableWord.symm.trans t'.tableWord
  subst e
  exact ⟨rfl, t.ptrWord.symm.trans t'.ptrWord, t.limitWord.symm.trans t'.limitWord⟩

/-- **`caml_modify` growing an unallocated remembered set, at an F1 state
whose RAM is dense** (every startup-live byte present, as newlib's VSA model
requires) and whose integer registers are all present. -/
theorem f1_barrierGrowth_dense {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high codeReg : Nat}
    {ra codeWord stackWord value : BitVec 64} {c : Config} {l a i tag : Nat} {fields : List Val}
    {vVal : Val} {D : InvocationData} {tbl ptr limit : BitVec 64}
    (input : ModifyInput Gc.f1Layout P s pl cp sp high codeReg ra codeWord stackWord
      (BitVec.ofNat 64 (a + 8 * i)) value c)
    (inv : Invocation D c) (v : NativeValid D) (low : high - Layout.stackBytes ≤ sp)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length)
    (represented : valWord pl vVal = some value)
    (root : ∀ loc, vVal.loc? = some loc → Live s.heap (roots P s) loc)
    (fieldStable : WindowStable Gc.f1Layout.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩])
    (table : Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem)
    (emptyW : word c (tbl + BitVec.ofNat 64 0).toNat = 0#64)
    (grows : ¬ Gc.Barrier.NoGrow (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 32).toNat 8)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 40).toNat 8)
      (BitVec.ofNat 64 (a + 8 * i)) (bytesT c.σ.mem (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8)
      value ptr limit)
    (dense : ∀ x, startupLive x → (c.σ.mem[x]?).isSome) (gprs : GprPresent c.σ) :
    FnSummary (0x8000a9a8#64) (fun e => e = c)
      (BarrierDone Gc.f1Layout P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D ra c) := by
  have ok : f1Runtime c := input.runtime
  have g := input.geometry
  have objArena := g.heapArena l a _ placed selected
  have size : (Obj.block tag fields).wosize = fields.length := rfl
  rw [size] at objArena
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have fits : a + 8 * i < 2 ^ 64 := by simp only [Vsa.Sim.DlHeap.heapEnd] at objArena; omega
  have sn := barrier_slot_nat (a := a) (i := i) fits
  have entry := barrier_entry input f1_barrierRuntime inv v placed selected bound
  obtain ⟨rfl, rfl, rfl⟩ := table_unique table (f1_table ok)
  obtain ⟨tbl', ptr', limit', t', arena, sep⟩ := f1_tableRuntime ok
  obtain ⟨rfl, rfl, rfl⟩ := table_unique t' (f1_table ok)
  have rem := barrier_remembered input v placed selected bound table arena
    (sep P s pl cp high g input.data.codeBase input.data.stackHigh)
  simp only [Gc.Barrier.NoGrow, not_or] at grows
  obtain ⟨notYoung, notOld, young, notRoom⟩ := grows
  have emptyNat : (word c (refTable + Layout.off_ref_table_base)).toNat = 0 := by
    have e := emptyW
    rw [show ((BitVec.ofNat 64 refTable) + BitVec.ofNat 64 0).toNat = refTable + Layout.off_ref_table_base by decide] at e
    rw [e]; rfl
  obtain ⟨hc, -⟩ := g.nursery.heapPrivate l a _ placed selected
  have chunks := g.nursery.heapChunks l a _ placed selected
  rw [size] at hc chunks
  have slotChunks : InHeapChunks (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8 := by
    rw [sn]
    rcases chunks with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have slotPrivate : (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat + 8 ≤ privateRegion.lo ∨
      privateRegion.hi ≤ (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat := by
    rw [sn]; rcases hc with o | o
    · left; omega
    · right; omega
  have platform : VsaIris.Inst.VsaOk startupLive c :=
    ⟨input.good, input.tick, fun n lo hi => gprs.get n lo (by omega), dense, input.loop.htifIdle⟩
  have frame : NativeFrame (BitVec.ofNat 64 D.nativeSp) (32 + (64 + VsaIris.VsaHeap.allocHeadroom)) :=
    ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        exact Nat.le_trans (Nat.add_le_add_left (by decide : 32 + (64 + VsaIris.VsaHeap.allocHeadroom) ≤ nativeHeadroom) _) hh,
     by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) ht),
     by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]; exact v.aligned,
     by decide⟩
  obtain ⟨H, cap, chs, h, grow⟩ := Gc.f1_grow (v := value) ok input.toLeafInput platform input.loop.gp inv.stack
    frame emptyNat slotChunks
  apply (Gc.Barrier.barrier_grow entry rem grow notYoung notOld (Classical.not_not.1 young) (Nat.le_of_not_lt notRoom)).weaken
    (fun _ h => h)
  intro after ⟨gd⟩
  have state0 : BarrierState Gc.f1Layout P s pl cp sp high D c :=
    ⟨input.data, input.primitives, input.image, input.runtime, input.geometry, inv, low⟩
  refine ⟨state0.keep_field_step v live placed selected bound represented root fieldStable ?_ ?_ gd.ready.image
    (Gc.f1_afterGrow ok h emptyNat gd slotChunks slotPrivate) gd.out ?_, gd.ready.good, gd.ready.tick,
    gd.ready.minstret, gd.pc, ?_, gd.ready.platform.htifIdle⟩
  · intro x obs ns
    have kk := observed_kept ok h g input.data low small x obs
    unfold InSpan at ns
    simp only [byte, bytesT, gd.kept x kk (by rw [sn]; omega)]
  · have w := gd.slotWord
    rw [sn] at w
    exact w
  · exact gd.ready.stack.trans inv.stack.symm
  · intro n lo hi out
    apply gd.saved
    simp only [barrierClobber, Gc.Barrier.calleeSaved, Realloc.calleeRest, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at out ⊢
    omega

end OCaml.Vm.Sim
