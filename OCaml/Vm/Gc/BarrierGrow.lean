import OCaml.Vm.Gc.BarrierRun
import OCaml.Vm.Gc.ReallocCallee
import OCaml.Vm.Gc.Generated.BarrierReload

/-!
# `caml_modify` growing the remembered set

The growth path: the value is young, the old value is not, and the
remembered set is full or unallocated, so `caml_modify` calls
`caml_realloc_ref_table`. Readiness (`RuntimeReady`) is carried from the
barrier's entry through its store chains (`ready_step`) to the call.
-/

namespace OCaml.Vm.Gc.Barrier
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris VsaIris.Inst
  VsaIris.VsaHeap LeanRV64DExecutable

/-- **Readiness across a barrier step**: a run whose stores lie at or above
`heapStart` and miss the allocator footprint, keeping x3 and the HTIF state
and every GPR present. -/
theorem ready_step {H capacity sp ra sp' ra' before after} {log : List WEntry} {W : List Nat}
    (ready : RuntimeReady H capacity sp ra before)
    (good : GoodState after.σ) (tick : after.tick < 2)
    (minstret : ∃ w, after.σ.regs.get? Register.minstret = some w)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ W, (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r)
    (present : GprPresent after.σ) (keys : KeysOK W) (gp : 3 ∉ W)
    (stack : gprGet after.σ 2 = some sp') (link : gprGet after.σ 1 = some ra') (aligned : ra'.toNat % 4 = 0)
    (arena : ∀ e ∈ log, heapStart ≤ e.1) (foot : ∀ a, vsaFoot H a → OutL log a) :
    RuntimeReady H capacity sp' ra' after := by
  have low (a : Nat) (h : a < heapStart) : after.σ.mem[a]? = before.σ.mem[a]? := by
    rw [memory]
    apply writeLog_out
    apply outL_of_range (n := 1) ?_ (Nat.le_refl a) (Nat.lt_succ_self a)
    exact outLRange_of_forall fun e he => Or.inl (by have := arena e he; omega)
  have image : ExecutableImage after := by
    apply image_of_writeLog ready.image ?_ memory
    have text : Image.textBase + Image.textSize ≤ heapStart := by decide
    have rodata : Image.rodataBase + Image.rodataSize ≤ heapStart := by decide
    exact ⟨outLRange_of_forall fun e he => Or.inl (by have := arena e he; omega),
      outLRange_of_forall fun e he => Or.inl (by have := arena e he; omega)⟩
  have gp3 : gprGet after.σ 3 = gprGet before.σ 3 :=
    frame_gpr keys frame 3 (by decide) (by decide) gp
  refine ⟨⟨good, image, minstret, link, aligned, tick⟩, ?_, ⟨?_, ?_⟩, ?_, stack, ?_, ?_⟩
  · refine ⟨good, tick, fun n lo hi => present.get n lo (by omega), ?_, ?_⟩
    · intro a ha
      rw [memory]
      exact writeLog_present _ _ _ (ready.platform.live a ha)
    · rw [frame _ (by decide) (fun n hn => gprReg_htif_payload n)]
      exact ready.platform.htifIdle
  · intro pin hp
    have eq : pin = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
    subst pin
    have := ready.readOnly.1 _ hp
    change vsaReg after 3 = _
    change vsaReg before 3 = _ at this
    rw [vsaReg_gpr (by decide)] at this ⊢
    rw [gp3]; exact this
  · intro pin hp
    change (after.σ.mem[pin.1]?).getD 0 = pin.2
    rw [low _ (allocator_sources pin hp).geometry.high]
    exact ready.readOnly.2 pin hp
  · apply roomLocal_vsaRoomB H _ _ capacity ?_ ready.room
    intro a ha
    change (before.σ.mem[a]?).getD 0 = (after.σ.mem[a]?).getD 0
    rw [memory, writeLog_out _ _ _ (foot a ha)]
  · rw [word_observed (m := before.σ.mem) _ (fun i _ => by
      rw [low _ (by unfold heapStart Layout.sym_Caml_state; omega)])]
    exact ready.domainWord
  · exact lpins8_observed ready.poolZero (fun i _ => by rw [low _ (by unfold heapStart Layout.sym_pool; omega)])

/-- The saves before the growth call: the slot address and the table pointer. -/
def fullLog (fsp slot tbl : BitVec 64) : List WEntry :=
  [((fsp + BitVec.ofNat 64 8).toNat, 8, slot), ((fsp + BitVec.ofNat 64 0).toNat, 8, tbl)]

/-- At the `jal caml_realloc_ref_table` (`aa84`). -/
structure AtGrowCall (slot fsp tbl : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some BarrierFull.call.pc
  memory : after.σ.mem = writeLog before.σ.mem (fullLog fsp slot tbl)
  output : after.σ.sailOutput = before.σ.sailOutput
  table : gprGet after.σ 10 = some tbl
  stack : gprGet after.σ 2 = some fsp
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10, 12, 13, 14], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

/-- **A young value and a full (or unallocated) remembered set**: save and call. -/
theorem value_full {slot v fsp dom ys ye tbl ptr limit} {d : Config} (b : Body slot v fsp dom ys ye d)
    (t : Table dom tbl ptr limit d.σ.mem) (pc : PCAt BarrierFull.pc d)
    (young : ValueYoung ys ye v) (full : limit.toNat ≤ ptr.toNat)
    (save8 : WriteWindow (fsp + BitVec.ofNat 64 8) 8) (save0 : WriteWindow (fsp + BitVec.ofNat 64 0) 8) :
    ∃ d1, Steps d d1 ∧ AtGrowCall slot fsp tbl d d1 := by
  have csV : bytesVal .ld (Primitives.read8 d.σ.mem Layout.sym_Caml_state) = dom := dom_value b.domain.domain
  have word (x : Nat) : bytesVal .ld (Primitives.read8 d.σ.mem x) = bytesT d.σ.mem x 8 := read8_value _ _
  have tblV : bytesVal .ld (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 104).toNat) = tbl := by
    rw [word]; exact t.tableWord
  have ptrV : bytesVal .ld (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 24).toNat) = ptr := by
    rw [word]; exact t.ptrWord
  have limV : bytesVal .ld (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 32).toNat) = limit := by
    rw [word]; exact t.limitWord
  have input : BarrierFull.Input v (0x80064d08#64) slot fsp (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 104).toNat)
      (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 24).toNat)
      (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 32).toNat) d :=
    { good := b.good, tick := b.tick, minstret := b.minstret, code0 := b.code
      registers := ⟨b.value, b.state, b.slot, b.stack, trivial⟩
      route := {
        control0 := young.1
        read1 := caml_state_read
        pins1 := by rw [cs_zero_nat]; dsimp only [BarrierFull.mem1, BarrierFull.mem0]; exact read8_pins _ _
        read2 := by rw [csV]; exact b.domain.endRead
        pins2 := by rw [csV]; dsimp only [BarrierFull.mem1, BarrierFull.mem0]; exact read8_pins _ _
        control1 := by rw [word, b.domain.youngEnd]; exact young.2.2
        read3 := by rw [csV]; exact b.domain.startRead
        pins3 := by rw [csV]; dsimp only [BarrierFull.mem2, BarrierFull.mem1, BarrierFull.mem0]; exact read8_pins _ _
        control2 := by rw [word, b.domain.youngStart]; exact young.2.1
        read4 := by rw [csV]; exact t.tableRead
        pins4 := by
          rw [csV]; dsimp only [BarrierFull.mem3, BarrierFull.mem2, BarrierFull.mem1, BarrierFull.mem0]
          exact read8_pins _ _
        read5 := by rw [tblV]; exact t.ptrWrite.read
        pins5 := by
          rw [tblV]; dsimp only [BarrierFull.mem3, BarrierFull.mem2, BarrierFull.mem1, BarrierFull.mem0]
          exact read8_pins _ _
        read6 := by rw [tblV]; exact t.limitRead
        pins6 := by
          rw [tblV]; dsimp only [BarrierFull.mem3, BarrierFull.mem2, BarrierFull.mem1, BarrierFull.mem0]
          exact read8_pins _ _
        control3 := by rw [ptrV, limV]; exact full
        write1 := save8
        write2 := save0 } }
  obtain ⟨d1, run, post⟩ := (BarrierFull.run input).run d ⟨pc, rfl⟩
  have r := post.regs
  rw [BarrierFull.registers] at r
  obtain ⟨-, -, r10, -, -, r2, -⟩ := r
  refine ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl, ?_, post.output,
    by rw [tblV] at r10; exact r10, r2,
    fun q noise out => post.frame q noise fun n hn => out n (BarrierFull.written n hn),
    fun p => BarrierFull.gpr_present post p⟩
  rw [post.memory, BarrierFull.log, tblV]; rfl

/-- The extra facts the growth path needs at `caml_modify`'s entry:
readiness for malloc, a native frame with room for the callee and malloc,
the remembered set unallocated, and where the slot lives. -/
structure Grow (H : List (Nat × Nat)) (capacity charge : Nat) (slot v ra sp tbl wsz : BitVec 64) (c : Config) :
    Prop where
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (32 + (64 + allocHeadroom))
  table : (tbl.toNat, Realloc.tableBytes) ∈ H
  tableAligned : tbl.toNat % 8 = 0
  empty : bytesT c.σ.mem tbl.toNat 8 = 0#64
  minorWsz : bytesT c.σ.mem (firstDomainPtr.toNat + 80) 8 = wsz
  charged : vsaChg (Realloc.request wsz).toNat charge
  /-- the request covers at least the first entry -/
  requestBig : 8 ≤ (Realloc.request wsz).toNat
  refCode : Code.Caml_realloc_ref_tableLoaded c.σ.mem
  genCode : Code.Realloc_generic_table_isra_0Loaded c.σ.mem
  /-- the slot lies in a live block (a major heap chunk or global data) -/
  slotLive : ∃ q n, (q, n) ∈ H ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ (slot + BitVec.ofNat 64 0).toNat ∧
    (slot + BitVec.ofNat 64 0).toNat + 8 ≤ q + n
  slotTable : (slot + BitVec.ofNat 64 0).toNat + 8 ≤ tbl.toNat ∨
    tbl.toNat + Realloc.tableBytes ≤ (slot + BitVec.ofNat 64 0).toNat
  slotWsz : (slot + BitVec.ofNat 64 0).toNat + 8 ≤ firstDomainPtr.toNat + 80 ∨
    firstDomainPtr.toNat + 88 ≤ (slot + BitVec.ofNat 64 0).toNat

/-- The callee-saved registers: s0–s3 and the rest. -/
def calleeSaved : List Nat := [8, 9, 18, 19] ++ Realloc.calleeRest

/-- At `caml_realloc_ref_table`'s entry, from the barrier. -/
structure AtRealloc (H : List (Nat × Nat)) (capacity charge : Nat) (slot v ra sp tbl wsz : BitVec 64)
    (before after : Config) : Prop where
  entry : Realloc.Entry H capacity charge (sp + -32#64) 0x8000aa88#64 tbl (vsaReg before 8) (vsaReg before 9)
    (vsaReg before 18) (vsaReg before 19) wsz after
  pc : after.σ.regs.get? Register.PC = some ReallocEntry.pc
  memory : after.σ.mem = writeLog before.σ.mem
    (majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl)
  saved : ∀ k ∈ calleeSaved, gprGet after.σ k = gprGet before.σ k

theorem frame32 {sp : BitVec 64} (f : NativeFrame sp (32 + (64 + allocHeadroom))) (off : Nat) (h : off + 8 ≤ 32)
    (aligned : off % 8 = 0) :
    WriteWindow ((sp + -32#64) + BitVec.ofNat 64 off) 8 ∧
      ((sp + -32#64) + BitVec.ofNat 64 off).toNat = sp.toNat - 32 + off := by
  have f32 : NativeFrame sp 32 := f.resize (by decide) (by decide)
  have a : (sp + -32#64) + BitVec.ofNat 64 off = BitVec.ofNat 64 (nativeFrameBase sp 32 + off) := f32.address off (by omega)
  rw [a]
  exact ⟨f32.word h aligned, f32.slot_nat (by omega)⟩

/-- The barrier's stores before the growth call: native-frame slots above the
arena, or the slot's word. -/
theorem grow_log_class {H capacity charge slot v ra sp tbl wsz} {c : Config}
    (g : Grow H capacity charge slot v ra sp tbl wsz c) :
    ∀ x ∈ majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl,
      (heapEnd + 512 ≤ x.1 ∧ x.1 + x.2.1 ≤ sp.toNat) ∨
        (x.1 = (slot + BitVec.ofNat 64 0).toNat ∧ x.2.1 = 8) := by
  have lower := g.frame.lower
  obtain ⟨-, n24⟩ := frame32 g.frame 24 (by decide) (by decide)
  obtain ⟨-, n8⟩ := frame32 g.frame 8 (by decide) (by decide)
  obtain ⟨-, n0⟩ := frame32 g.frame 0 (by decide) (by decide)
  intro x hx
  simp only [majorLog, fullLog, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [allocHeadroom] at lower
  rcases hx with rfl | rfl | rfl | rfl
  · left; dsimp only; rw [n24]; omega
  · right; exact ⟨by dsimp only; rw [slot_exact], rfl⟩
  · left; dsimp only; rw [n8]; omega
  · left; dsimp only; rw [n0]; omega

/-- **From `caml_modify`'s entry to `caml_realloc_ref_table`'s**, on the growth path. -/
theorem grow_to_call {H capacity charge slot v ra sp dom ys ye old tbl ptr limit wsz} {c : Config}
    (e : Entry slot v ra sp dom ys ye old c) (rem : Remembered sp ra slot v dom tbl ptr limit c)
    (g : Grow H capacity charge slot v ra sp tbl wsz c)
    (notYoung : ¬ YoungIn ys ye slot) (notOld : ¬ OldYoung ys ye old) (young : ValueYoung ys ye v)
    (full : limit.toNat ≤ ptr.toNat) :
    FnSummary BarrierYoung.pc (fun d => d = c) (AtRealloc H capacity charge slot v ra sp tbl wsz c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  obtain ⟨d1, run1, M⟩ := (major_head e notYoung).run d ⟨pc, rfl⟩
  obtain ⟨d2, run2, O⟩ := (old_run e M).run d1 ⟨M.pc, rfl⟩
  have B : AtBody slot v ra sp d1 d2 := by
    rcases O with ⟨h, -⟩ | ⟨-, B⟩
    · exact absurd h notOld
    · exact B
  have mem2 : d2.σ.mem = writeLog d.σ.mem (majorLog sp ra slot v) := by rw [B.memory, M.memory]
  obtain ⟨h14, h15, h13, h2, -, -⟩ := B.regs
  have body : Body slot v (sp + -32#64) dom ys ye d2 :=
    { good := B.good, tick := B.tick, minstret := B.minstret
      code := by rw [mem2]; exact code_after e.code e.aboveCode
      value := h14, slot := h15, state := h13, stack := h2
      domain := by rw [mem2]; exact e.domainBody }
  obtain ⟨s8, -⟩ := frame32 g.frame 8 (by decide) (by decide)
  obtain ⟨s0w, -⟩ := frame32 g.frame 0 (by decide) (by decide)
  obtain ⟨d3, run3, G⟩ := value_full body (by rw [mem2]; exact rem.table.writeLog rem.stored) B.pc young full s8 s0w
  -- the stores so far
  have mem3 : d3.σ.mem = writeLog d.σ.mem (majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl) := by
    rw [G.memory, mem2, writeLog_append]
  have cls := grow_log_class g
  obtain ⟨q, n, member, qLow, qHigh, slotLo, slotHi⟩ := g.slotLive
  obtain ⟨tLow, tHigh⟩ := g.ready.block_bounds g.table
  have arena : ∀ x ∈ majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl, heapStart ≤ x.1 := by
    intro x hx
    rcases cls x hx with ⟨h, -⟩ | ⟨h, -⟩
    · simp only [heapStart, heapEnd] at *; omega
    · omega
  have outRange (a w : Nat) (h : ∀ x ∈ majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl,
      a + w ≤ x.1 ∨ x.1 + x.2.1 ≤ a) := outLRange_of_forall h
  have foot : ∀ a, vsaFoot H a → OutL (majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl) a := by
    intro a ha
    apply outL_of_range (n := 1) ?_ (Nat.le_refl a) (Nat.lt_succ_self a)
    apply outLRange_of_forall
    intro x hx
    have below := allocator_foot_below ha
    rcases cls x hx with ⟨h, -⟩ | ⟨h, w⟩
    · left; omega
    · rcases allocator_payload_outside member qLow ha with o | o
      · left; omega
      · right; omega
  -- readiness at the call
  have W1 : ∀ n ∈ [13, 14, 15], n ∈ [2, 10, 11, 12, 13, 14, 15] := by decide
  have W2 : ∀ n ∈ [2, 10, 11, 12, 14, 15], n ∈ [2, 10, 11, 12, 13, 14, 15] := by decide
  have W3 : ∀ n ∈ [10, 12, 13, 14], n ∈ [2, 10, 11, 12, 13, 14, 15] := by decide
  have frame3 := frame_chain (frame_chain M.frame B.frame W1 W2) G.frame (fun n h => h) W3
  have keep3 := frame_gpr (by decide) frame3
  have present0 : GprPresent d.σ := ⟨fun n lo hi => g.ready.platform.gpr n lo (by omega)⟩
  have ready3 : RuntimeReady H (capacity + charge) (sp + -32#64) ra d3 :=
    ready_step g.ready G.good G.tick G.minstret mem3 frame3 (G.present (B.present (M.present present0)))
      (by decide) (by decide) G.stack ((keep3 1 (by decide) (by decide) (by decide)).trans e.raReg) e.raAligned
      arena foot
  have code3 : Code.Caml_modifyLoaded d3.σ.mem := by
    rw [mem3]
    exact code_after e.code fun x hx => by
      have := arena x hx
      simp only [heapStart] at this; omega
  obtain ⟨d4, run4, C⟩ := (ready_call BarrierFull.call_shape BarrierFull.call_decode
    (BarrierFull.call_pins code3) ready3 [(10, tbl)] ⟨G.table, trivial⟩ (by simp only [keysG, List.map]; decide)
    (by simp [KeysAvoidRa, keysG]) tbl rfl (by decide)).run d3 ⟨G.pc, rfl⟩
  have mem4 : d4.σ.mem = writeLog d.σ.mem (majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl) :=
    C.memory.trans mem3
  have keep4 (k : Nat) (hk : k ∈ calleeSaved) : gprGet d4.σ k = gprGet d.σ k := by
    have b : 1 ≤ k ∧ k ≤ 31 ∧ k ≠ 1 ∧ k ∉ [2, 10, 11, 12, 13, 14, 15] := by
      simp only [calleeSaved, Realloc.calleeRest, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hk ⊢
      omega
    exact (C.frame k b.1 b.2.1 b.2.2.1).trans (keep3 k b.1 b.2.1 b.2.2.2)
  have low : Realloc.LowKept d.σ.mem d4.σ.mem := by
    intro a _ below _
    rw [mem4]
    apply writeLog_out
    apply outL_of_range (n := 1) ?_ (Nat.le_refl a) (Nat.lt_succ_self a)
    exact outLRange_of_forall fun x hx => Or.inl (by have := arena x hx; omega)
  have word (k : Nat) (hk : k ∈ [8, 9, 18, 19]) : gprGet d4.σ k = some (vsaReg d k) := by
    have mem : k ∈ calleeSaved := List.mem_append_left _ hk
    rw [keep4 k mem]
    have b : 1 ≤ k ∧ k ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    exact library_gpr g.ready.platform b.1 b.2 rfl
  refine ⟨d4, run1.trans (run2.trans (run3.trans run4)), ⟨?_, ?_, mem4, keep4⟩⟩
  · exact {
      ready := by have r := C.ready; rw [BarrierFull.call_link] at r; exact r
      frame := g.frame.nested (front := 32) (by decide)
      saved := ⟨word 8 (by decide), word 9 (by decide), word 18 (by decide), word 19 (by decide), C.regs.1, trivial⟩
      refCode := Realloc.refCode_keep g.refCode low
      genCode := Realloc.genCode_keep g.genCode low
      table := g.table
      tableAligned := g.tableAligned
      empty := by
        rw [mem4, bytesT_writeLog_out _ (outRange _ 8 fun x hx => by
          rcases cls x hx with ⟨h, -⟩ | ⟨h, w⟩
          · left; simp only [Realloc.tableBytes, heapEnd] at *; omega
          · rcases g.slotTable with t | t
            · right; omega
            · left; simp only [Realloc.tableBytes] at t; omega)]
        exact g.empty
      minorWsz := by
        rw [mem4, bytesT_writeLog_out _ (outRange _ 8 fun x hx => by
          rcases cls x hx with ⟨h, -⟩ | ⟨h, w⟩
          · left
            have : firstDomainPtr.toNat + 80 + 8 ≤ heapEnd := by simp [firstDomainPtr, heapStart, heapEnd]
            exact Nat.le_trans this (Nat.le_trans (Nat.le_add_right heapEnd 512) h)
          · rcases g.slotWsz with t | t
            · right; omega
            · left; omega)]
        exact g.minorWsz
      charged := g.charged }
  · rw [C.pc, BarrierFull.call_target]; rfl

/-- The insertion after the growth: `ptr := p + 8`, `*p := slot`. -/
def reloadLog (tbl p slot : BitVec 64) : List WEntry :=
  [((tbl + BitVec.ofNat 64 24).toNat, 8, p + 8#64), ((p + BitVec.ofNat 64 0).toNat, 8, slot)]

/-- At `aa88` after `caml_realloc_ref_table` returns: the saved frame words,
the new `ptr`, the windows and readiness. -/
structure Reloading (H : List (Nat × Nat)) (capacity : Nat) (sp ra slot tbl p link : BitVec 64) (d : Config) :
    Prop where
  ready : RuntimeReady H capacity (sp + -32#64) link d
  code : Code.Caml_modifyLoaded d.σ.mem
  savedTbl : bytesT d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 0).toNat 8 = tbl
  savedSlot : bytesT d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 8).toNat 8 = slot
  savedRa : bytesT d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat 8 = ra
  ptr : bytesT d.σ.mem (tbl + BitVec.ofNat 64 24).toNat 8 = p
  frame0 : WriteWindow ((sp + -32#64) + BitVec.ofNat 64 0) 8
  frame8 : WriteWindow ((sp + -32#64) + BitVec.ofNat 64 8) 8
  frame24 : WriteWindow ((sp + -32#64) + BitVec.ofNat 64 24) 8
  ptrWrite : WriteWindow (tbl + BitVec.ofNat 64 24) 8
  entryWrite : WriteWindow (p + BitVec.ofNat 64 0) 8
  raApart : ∀ x ∈ reloadLog tbl p slot, ((sp + -32#64) + BitVec.ofNat 64 24).toNat + 8 ≤ x.1 ∨
    x.1 + x.2.1 ≤ ((sp + -32#64) + BitVec.ofNat 64 24).toNat
  raAligned : ra.toNat % 4 = 0
  arena : ∀ x ∈ reloadLog tbl p slot, heapStart ≤ x.1
  foot : ∀ a, vsaFoot H a → OutL (reloadLog tbl p slot) a

/-- Returned from the growth path. -/
structure Reloaded (H : List (Nat × Nat)) (capacity : Nat) (sp ra tbl p slot : BitVec 64) (before after : Config) :
    Prop where
  ready : RuntimeReady H capacity sp ra after
  pc : after.σ.regs.get? Register.PC = some ra
  memory : after.σ.mem = writeLog before.σ.mem (reloadLog tbl p slot)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1, 2, 10, 13, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

/-- **Insert after the growth and return** (`aa88`). -/
theorem reload_run {H capacity sp ra slot tbl p link} {d : Config}
    (r : Reloading H capacity sp ra slot tbl p link d) (pc : PCAt BarrierReload.pc d) :
    ∃ d1, Steps d d1 ∧ Reloaded H capacity sp ra tbl p slot d d1 := by
  have word (x : Nat) : bytesVal .ld (Primitives.read8 d.σ.mem x) = bytesT d.σ.mem x 8 := read8_value _ _
  have tblV : bytesVal .ld (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 0).toNat) = tbl := by
    rw [word]; exact r.savedTbl
  have slotV : bytesVal .ld (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 8).toNat) = slot := by
    rw [word]; exact r.savedSlot
  have ptrV : bytesVal .ld (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 24).toNat) = p := by
    rw [word]; exact r.ptr
  have raPins : LPins8 (writeLog d.σ.mem (reloadLog tbl p slot)) ((sp + -32#64) + BitVec.ofNat 64 24).toNat
      (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat) :=
    lpins8_writeLog (read8_pins _ _) (outLRange_of_forall r.raApart)
  have raV : bytesVal .ld (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat) = ra := by
    rw [word]; exact r.savedRa
  have input : BarrierReload.Input (sp + -32#64)
      (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 0).toNat)
      (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 8).toNat)
      (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 24).toNat)
      (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat) d :=
    { good := r.ready.good, tick := r.ready.tick, minstret := r.ready.minstret, code0 := r.code
      registers := ⟨r.ready.stack, trivial⟩
      route := {
        read1 := r.frame0.read, pins1 := read8_pins _ _
        read2 := r.frame8.read, pins2 := read8_pins _ _
        read3 := by rw [tblV]; exact r.ptrWrite.read
        pins3 := by rw [tblV]; exact read8_pins _ _
        write1 := by rw [tblV]; exact r.ptrWrite
        write2 := by rw [ptrV]; exact r.entryWrite
        read4 := r.frame24.read
        pins4 := by
          dsimp only [BarrierReload.mem2, BarrierReload.mem1, BarrierReload.mem0]
          rw [tblV, ptrV, slotV]; exact raPins
        control2 := by rw [raV]; exact r.raAligned } }
  obtain ⟨d1, run, post⟩ := (BarrierReload.run input).run d ⟨pc, rfl⟩
  have regs := post.regs
  rw [BarrierReload.registers] at regs
  obtain ⟨r2, r1, -⟩ := regs
  rw [raV] at r1
  rw [frame_pop32] at r2
  have memory : d1.σ.mem = writeLog d.σ.mem (reloadLog tbl p slot) := by
    rw [post.memory, BarrierReload.log, tblV, ptrV, slotV]; rfl
  have frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [1, 2, 10, 13, 14, 15], (gprReg n == r) = false) → d1.σ.regs.get? r = d.σ.regs.get? r :=
    fun q noise out => post.frame q noise fun n hn => out n (BarrierReload.written n hn)
  have present : GprPresent d1.σ :=
    BarrierReload.gpr_present post ⟨fun n lo hi => r.ready.platform.gpr n lo (by omega)⟩
  refine ⟨d1, run, ⟨?_, ?_, memory, post.output, frame⟩⟩
  · exact ready_step r.ready post.good post.tick post.minstret memory frame present (by decide) (by decide)
      r2 r1 r.raAligned r.arena r.foot
  · rw [post.pc, BarrierReload.endpoint _ _ _ _ _ (by rw [raV]; exact r.raAligned), raV]

/-- Total-byte agreement plus presence on both sides: option agreement. -/
theorem option_of_getD {m m' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} (h' : (m'[a]?).isSome)
    (h : (m[a]?).isSome) (e : (m'[a]?).getD 0 = (m[a]?).getD 0) : m'[a]? = m[a]? := by
  revert e h h'
  cases m'[a]? <;> cases m[a]? <;> simp_all

/-- The growth path's outcome. -/
structure GrowDone (H : List (Nat × Nat)) (capacity : Nat) (slot v ra sp tbl wsz : BitVec 64)
    (before after : Config) where
  p : BitVec 64
  ready : RuntimeReady ((p.toNat, (Realloc.request wsz).toNat) :: H) capacity sp ra after
  pc : after.σ.regs.get? Register.PC = some ra
  saved : ∀ k ∈ calleeSaved, gprGet after.σ k = gprGet before.σ k
  fresh : heapStart ≤ p.toNat ∧ p.toNat + (Realloc.request wsz).toNat ≤ heapEnd
  disjoint : ∀ e ∈ H, ∀ a, InExt (p.toNat, (Realloc.request wsz).toNat) a → ¬ InExt e a
  slotWord : bytesT after.σ.mem (slot + BitVec.ofNat 64 0).toNat 8 = v
  base : bytesT after.σ.mem tbl.toNat 8 = p
  ptr : bytesT after.σ.mem (tbl + BitVec.ofNat 64 24).toNat 8 = p + 8#64
  entry : bytesT after.σ.mem (p + BitVec.ofNat 64 0).toNat 8 = slot

/-- A word inside a live block misses the fresh block's first word. -/
theorem fresh_apart {H : List (Nat × Nat)} {p r q n x : Nat}
    (disjoint : ∀ e ∈ H, ∀ a, InExt (p, r) a → ¬ InExt e a) (member : (q, n) ∈ H)
    (inside : q ≤ x ∧ x + 8 ≤ q + n) (big : 8 ≤ r) : p + 8 ≤ x ∨ x + 8 ≤ p := by
  rcases Nat.lt_or_ge x (p + 8) with h | h
  · rcases Nat.lt_or_ge p (x + 8) with h' | h'
    · exfalso
      rcases Nat.le_total p x with o | o
      · exact disjoint _ member x ⟨o, by omega⟩ ⟨inside.1, by omega⟩
      · exact disjoint _ member p ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩
    · exact Or.inr h'
  · exact Or.inl h

/-- **`caml_modify` growing an unallocated remembered set**, entry to return. -/
theorem barrier_grow {H capacity charge slot v ra sp dom ys ye old tbl ptr limit wsz} {c : Config}
    (e : Entry slot v ra sp dom ys ye old c) (rem : Remembered sp ra slot v dom tbl ptr limit c)
    (g : Grow H capacity charge slot v ra sp tbl wsz c)
    (notYoung : ¬ YoungIn ys ye slot) (notOld : ¬ OldYoung ys ye old) (young : ValueYoung ys ye v)
    (full : limit.toNat ≤ ptr.toNat) :
    FnSummary BarrierYoung.pc (fun d => d = c)
      (fun after => Nonempty (GrowDone H capacity slot v ra sp tbl wsz c after)) := by
  constructor
  rintro d ⟨pc, rfl⟩
  obtain ⟨d4, run4, A⟩ := (grow_to_call e rem g notYoung notOld young full).run d ⟨pc, rfl⟩
  obtain ⟨d5, run5, ⟨D⟩⟩ := (Realloc.realloc_run A.entry).run d4 ⟨A.pc, rfl⟩
  -- geometry
  have lower := g.frame.lower
  have f32 : NativeFrame sp 32 := g.frame.resize (by decide) (by decide)
  have fspNat : (sp + -32#64).toNat = sp.toNat - 32 := f32.stack_nat
  obtain ⟨w24, n24⟩ := frame32 g.frame 24 (by decide) (by decide)
  obtain ⟨w8, n8⟩ := frame32 g.frame 8 (by decide) (by decide)
  obtain ⟨w0, n0⟩ := frame32 g.frame 0 (by decide) (by decide)
  obtain ⟨q, n, member, qLow, qHigh, slotLo, slotHi⟩ := g.slotLive
  obtain ⟨tLow, tHigh⟩ := g.ready.block_bounds g.table
  have t24 := Realloc.field_nat tHigh 24 (by decide)
  have p0 : (D.p + BitVec.ofNat 64 0).toNat = D.p.toNat := by simp
  have pRoom : D.p.toNat + 8 ≤ heapEnd := by
    have := D.high; have := g.requestBig; omega
  simp only [heapStart, heapEnd, allocHeadroom, Realloc.tableBytes] at lower tHigh tLow qLow qHigh pRoom
  -- the frame words before the call
  have mem4 := A.memory
  have list4 : majorLog sp ra slot v ++ fullLog (sp + -32#64) slot tbl =
      [(((sp + -32#64) + BitVec.ofNat 64 24).toNat, 8, ra), (((slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0).toNat, 8, v),
       (((sp + -32#64) + BitVec.ofNat 64 8).toNat, 8, slot), (((sp + -32#64) + BitVec.ofNat 64 0).toNat, 8, tbl)] := rfl
  rw [list4] at mem4
  have slotFrame := e.slotFrame
  have sFrame (off : Nat) (h : off + 8 ≤ 32) :
      (slot + BitVec.ofNat 64 0).toNat + 8 ≤ sp.toNat - 32 + off ∨ sp.toNat - 32 + off + 8 ≤ (slot + BitVec.ofNat 64 0).toNat := by
    left; omega
  have tbl4 : bytesT d4.σ.mem ((sp + -32#64) + BitVec.ofNat 64 0).toNat 8 = tbl := by
    rw [mem4]; exact word_writeLog_at _ _ 3 _ _ rfl trivial
  have slot4 : bytesT d4.σ.mem ((sp + -32#64) + BitVec.ofNat 64 8).toNat 8 = slot := by
    rw [mem4]
    apply word_writeLog_at _ _ 2 _ _ rfl
    exact ⟨by dsimp only; rw [n8, n0]; omega, trivial⟩
  have ra4 : bytesT d4.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat 8 = ra := by
    rw [mem4]
    apply word_writeLog_at _ _ 0 _ _ rfl
    refine ⟨?_, ⟨by dsimp only; rw [n24, n8]; omega, ⟨by dsimp only; rw [n24, n0]; omega, trivial⟩⟩⟩
    dsimp only; rw [slot_exact, n24]; rw [n24] at slotFrame; omega
  have value4 : bytesT d4.σ.mem (slot + BitVec.ofNat 64 0).toNat 8 = v := by
    have h := word_writeLog_at d.σ.mem
      [(((sp + -32#64) + BitVec.ofNat 64 24).toNat, 8, ra), (((slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0).toNat, 8, v),
       (((sp + -32#64) + BitVec.ofNat 64 8).toNat, 8, slot), (((sp + -32#64) + BitVec.ofNat 64 0).toNat, 8, tbl)]
      1 (((slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0).toNat) v rfl
      ⟨by rw [slot_exact, n8]; omega, ⟨by rw [slot_exact, n0]; omega, trivial⟩⟩
    have heq : ((slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0).toNat = (slot + BitVec.ofNat 64 0).toNat := by
      rw [slot_exact]
    rw [mem4, ← heq]; exact h
  -- across the callee: the caller's frame, the slot's block and the code are kept
  have keptWord (x : Nat) (k : ∀ i, i < 8 → Realloc.Kept H (sp + -32#64) tbl (x + i)) :
      bytesT d5.σ.mem x 8 = bytesT d4.σ.mem x 8 :=
    word_observed _ fun i hi => D.kept (x + i) (k i hi)
  have aboveFsp (x : Nat) (h : sp.toNat - 32 ≤ x) : ∀ i, i < 8 → Realloc.Kept H (sp + -32#64) tbl (x + i) :=
    fun i _ => Or.inl (by rw [fspNat]; omega)
  have tbl5 : bytesT d5.σ.mem ((sp + -32#64) + BitVec.ofNat 64 0).toNat 8 = tbl := by
    rw [keptWord _ (aboveFsp _ (by rw [n0]; omega))]; exact tbl4
  have slot5 : bytesT d5.σ.mem ((sp + -32#64) + BitVec.ofNat 64 8).toNat 8 = slot := by
    rw [keptWord _ (aboveFsp _ (by rw [n8]; omega))]; exact slot4
  have ra5 : bytesT d5.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat 8 = ra := by
    rw [keptWord _ (aboveFsp _ (by rw [n24]; omega))]; exact ra4
  have value5 : bytesT d5.σ.mem (slot + BitVec.ofNat 64 0).toNat 8 = v := by
    rw [keptWord _ fun i hi => Or.inr (Or.inr ⟨q, n, member, qLow, qHigh, by omega, by omega, by
      rcases g.slotTable with t | t <;> (try simp only [Realloc.tableBytes] at t) <;> simp only [Realloc.tableBytes]
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)⟩)]
    exact value4
  have code5 : Code.Caml_modifyLoaded d5.σ.mem := by
    apply Code.caml_modify_transport e.code
    intro a lo hi
    have live : startupLive a := by unfold startupLive Vsa.Densify.ramBase Vsa.Densify.ramSize; omega
    rw [option_of_getD (D.ready.platform.live a live) (A.entry.ready.platform.live a live)
      (D.kept a (Or.inr (Or.inl ⟨by unfold heapStart; omega, by unfold allocGlobal InRange; omega⟩)))]
    rw [mem4]
    apply writeLog_out
    apply outL_of_range (n := 1) ?_ (Nat.le_refl a) (Nat.lt_succ_self a)
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> dsimp only <;>
      first | (rw [n24]; omega) | (rw [n8]; omega) | (rw [n0]; omega) | (rw [slot_exact]; omega)
  -- the insertion's windows and separation
  have tblP : D.p.toNat + 8 ≤ tbl.toNat ∨ tbl.toNat + 56 ≤ D.p.toNat := by
    rcases fresh_apart D.disjoint g.table (x := tbl.toNat) ⟨Nat.le_refl _, by simp only [Realloc.tableBytes]; omega⟩
      g.requestBig with h | h
    · exact Or.inl h
    · right
      rcases fresh_apart D.disjoint g.table (x := tbl.toNat + 48) ⟨by omega, by simp only [Realloc.tableBytes]; omega⟩
        g.requestBig with h' | h'
      · exfalso
        have := D.disjoint _ g.table D.p.toNat ⟨Nat.le_refl _, by have := g.requestBig; omega⟩
        exact this ⟨by omega, by simp only [Realloc.tableBytes]; omega⟩
      · omega
  have slotP : D.p.toNat + 8 ≤ (slot + BitVec.ofNat 64 0).toNat ∨ (slot + BitVec.ofNat 64 0).toNat + 8 ≤ D.p.toNat :=
    fresh_apart D.disjoint member ⟨slotLo, slotHi⟩ g.requestBig
  have entryW : WriteWindow (D.p + BitVec.ofNat 64 0) 8 := by
    have al := D.aligned
    have pl := D.low
    constructor <;> rw [p0] <;> (try simp only [heapStart, heapEnd, Layout.sym_tohost] at *) <;> omega
  have reloading : Reloading ((D.p.toNat, (Realloc.request wsz).toNat) :: H) capacity sp ra slot tbl D.p
      0x8000aa88#64 d5 :=
    { ready := D.ready, code := code5, savedTbl := tbl5, savedSlot := slot5, savedRa := ra5
      ptr := by rw [t24]; exact D.ptr
      frame0 := w0, frame8 := w8, frame24 := w24, ptrWrite := rem.table.ptrWrite, entryWrite := entryW
      raApart := by
        intro x hx
        simp only [reloadLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> dsimp only <;> rw [n24]
        · rw [t24]; omega
        · rw [p0]; omega
      raAligned := e.raAligned
      arena := by
        intro x hx
        simp only [reloadLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> dsimp only
        · rw [t24]; unfold heapStart; omega
        · rw [p0]; exact D.low
      foot := by
        intro a ha
        apply outL_of_range (n := 1) ?_ (Nat.le_refl a) (Nat.lt_succ_self a)
        apply outLRange_of_forall
        intro x hx
        simp only [reloadLog, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> dsimp only
        · rw [t24]
          rcases allocator_payload_outside (List.mem_cons_of_mem _ g.table) (by unfold heapStart; omega) ha with o | o
          · left; omega
          · right; simp only [Realloc.tableBytes] at o; omega
        · rw [p0]
          rcases allocator_payload_outside List.mem_cons_self D.low ha with o | o
          · left; omega
          · right; have := g.requestBig; omega }
  obtain ⟨d6, run6, R⟩ := reload_run reloading D.pc
  -- the outcome
  have out6 (x : Nat) (apart : ∀ y ∈ reloadLog tbl D.p slot, x + 8 ≤ y.1 ∨ y.1 + y.2.1 ≤ x) :
      bytesT d6.σ.mem x 8 = bytesT d5.σ.mem x 8 := by
    rw [R.memory, bytesT_writeLog_out _ (outLRange_of_forall apart)]
  have reloadEntries : ∀ y ∈ reloadLog tbl D.p slot,
      (y.1 = tbl.toNat + 24 ∧ y.2.1 = 8) ∨ (y.1 = D.p.toNat ∧ y.2.1 = 8) := by
    intro y hy
    simp only [reloadLog, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · left; exact ⟨t24, rfl⟩
    · right; exact ⟨p0, rfl⟩
  refine ⟨d6, run4.trans (run5.trans run6), ⟨⟨D.p, R.ready, R.pc, ?_, ⟨D.low, D.high⟩, D.disjoint, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro k hk
    have b : 1 ≤ k ∧ k ≤ 31 ∧ k ∉ [1, 2, 10, 13, 14, 15] := by
      simp only [calleeSaved, Realloc.calleeRest, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hk ⊢
      omega
    have r6 : gprGet d6.σ k = gprGet d5.σ k := frame_gpr (by decide) R.frame k b.1 b.2.1 b.2.2
    rw [r6]
    rcases List.mem_append.1 hk with s | s
    · obtain ⟨g8, g9, g18, g19, -⟩ := D.saved
      have viaC : ∀ k ∈ [8, 9, 18, 19], gprGet d.σ k = some (vsaReg d k) := fun k hk => by
        have : 1 ≤ k ∧ k ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
        exact library_gpr g.ready.platform this.1 this.2 rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at s
      rcases s with rfl | rfl | rfl | rfl
      · rw [g8, viaC 8 (by decide)]
      · rw [g9, viaC 9 (by decide)]
      · rw [g18, viaC 18 (by decide)]
      · rw [g19, viaC 19 (by decide)]
    · exact (D.callee k s).trans (A.saved k hk)
  · rw [out6 _ fun y hy => by
      rcases reloadEntries y hy with ⟨h, w⟩ | ⟨h, w⟩ <;> rw [h, w]
      · rcases g.slotTable with t | t <;> (try simp only [Realloc.tableBytes] at t)
        · left; omega
        · right; omega
      · rcases slotP with t | t
        · right; omega
        · left; omega]
    exact value5
  · rw [out6 _ fun y hy => by
      rcases reloadEntries y hy with ⟨h, w⟩ | ⟨h, w⟩ <;> rw [h, w]
      · left; omega
      · rcases tblP with t | t
        · right; omega
        · left; omega]
    exact D.base
  · rw [R.memory]
    apply word_writeLog_at _ _ 0 _ _ rfl
    refine ⟨?_, trivial⟩
    dsimp only; rw [t24, p0]
    rcases tblP with t | t
    · right; omega
    · left; omega
  · rw [R.memory]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial

end OCaml.Vm.Gc.Barrier
