import OCaml.Vm.Gc.Generated.ReallocEntry
import OCaml.Vm.Gc.Generated.ReallocAllocCall
import OCaml.Vm.Sim.Muldi3
import OCaml.Vm.Boot.Startup.StatAllocReady
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Boot.Startup.ReadyPerm
import OCaml.Vm.Boot.Startup.DomainInit
import OCaml.Vm.Boot.Startup.TableAllocatorInput
import OCaml.Vm.Boot.Startup.TableHeap
import OCaml.Vm.Gc.ReadyCalls

/-!
# `caml_realloc_ref_table` on an unallocated table: up to the allocation

From `caml_realloc_ref_table`'s entry with `base == NULL`: the generated
entry chain (`ReallocEntry`: tail jump, frame saves, `size := wsz / 8`,
`reserve := 256`), `__muldi3((size + 256), 8)`, and
`caml_stat_alloc_noexc` of the product (a0-boot's `stat_alloc_ready`).
Readiness (`RuntimeReady`) is carried through every step with a0-boot's
transport lemmas.
-/

namespace OCaml.Vm.Gc.Realloc
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris VsaIris.VsaHeap
  LeanRV64DExecutable

/-- `struct caml_ref_table`: base, end, threshold, ptr, limit, size, reserve. -/
def tableBytes : Nat := 56

/-- The table's element count: `Caml_state->minor_heap_wsz / 8`. -/
def size (wsz : BitVec 64) : BitVec 64 := wsz >>> 3

/-- The allocation request `(size + reserve) * sizeof(value *)`. -/
def request (wsz : BitVec 64) : BitVec 64 := (size wsz + 0x100#64) * 0x8#64

/-- The callee's entry: readiness, a native frame with allocator headroom
below its 64-byte frame, the table as a live block with `base == NULL`. -/
structure Entry (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra tbl s0 s1 s2 s3 wsz : BitVec 64)
    (c : Config) : Prop where
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (64 + allocHeadroom)
  saved : GHolds c.σ [(8, s0), (9, s1), (18, s2), (19, s3), (10, tbl)]
  refCode : Code.Caml_realloc_ref_tableLoaded c.σ.mem
  genCode : Code.Realloc_generic_table_isra_0Loaded c.σ.mem
  table : (tbl.toNat, tableBytes) ∈ H
  tableAligned : tbl.toNat % 8 = 0
  empty : bytesT c.σ.mem tbl.toNat 8 = 0#64
  minorWsz : bytesT c.σ.mem (firstDomainPtr.toNat + 80) 8 = wsz
  charged : vsaChg (request wsz).toNat charge

/-- The entry chain's three loads: `base`, `Caml_state`, `minor_heap_wsz`. -/
def entryLoads (m : Std.ExtHashMap Nat (BitVec 8)) (tbl : BitVec 64) : List (List (BitVec 8)) :=
  ReallocEntry.loads (read8 m tbl.toNat) (read8 m Layout.sym_Caml_state) (read8 m (firstDomainPtr.toNat + 80))

/-- The frame slots of the callee's 64-byte native frame. -/
theorem frame_slot {sp : BitVec 64} (f : NativeFrame sp 64) (off : Nat) (bound : off ≤ 64) :
    (sp + -64#64) + BitVec.ofNat 64 off = BitVec.ofNat 64 (nativeFrameBase sp 64 + off) :=
  f.address off bound

theorem frame_write {sp : BitVec 64} (f : NativeFrame sp 64) (off : Nat) (bound : off + 8 ≤ 64)
    (aligned : off % 8 = 0) : WriteWindow ((sp + -64#64) + BitVec.ofNat 64 off) 8 := by
  rw [frame_slot f off (by omega)]; exact f.word bound aligned

theorem frame_nat {sp : BitVec 64} (f : NativeFrame sp 64) (off : Nat) (bound : off ≤ 64) :
    ((sp + -64#64) + BitVec.ofNat 64 off).toNat = sp.toNat - 64 + off := by
  rw [frame_slot f off bound, f.slot_nat bound]; rfl

/-- A table field address, numerically. -/
theorem field_nat {tbl : BitVec 64} (high : tbl.toNat + tableBytes ≤ heapEnd) (off : Nat) (bound : off ≤ tableBytes) :
    (tbl + BitVec.ofNat 64 off).toNat = tbl.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold heapEnd tableBytes at *
  omega

theorem field_read {tbl : BitVec 64} (low : heapStart ≤ tbl.toNat) (high : tbl.toNat + tableBytes ≤ heapEnd)
    (off : Nat) (bound : off + 8 ≤ tableBytes) : ReadWindow (tbl + BitVec.ofNat 64 off) 8 := by
  have n := field_nat high off (by omega)
  constructor <;> rw [n] <;> simp only [heapStart, heapEnd, tableBytes, Layout.sym_tohost] at * <;> omega

theorem field_write {tbl : BitVec 64} (low : heapStart ≤ tbl.toNat) (high : tbl.toNat + tableBytes ≤ heapEnd)
    (aligned : tbl.toNat % 8 = 0) (off : Nat) (bound : off + 8 ≤ tableBytes) (offAligned : off % 8 = 0) :
    WriteWindow (tbl + BitVec.ofNat 64 off) 8 := by
  have n := field_nat high off (by omega)
  constructor <;> rw [n] <;> simp only [heapStart, heapEnd, tableBytes, Layout.sym_tohost] at * <;> omega

/-- The callee's write windows: its 64-byte native frame and the table. -/
def windows (sp tbl : BitVec 64) : List W :=
  [⟨sp.toNat - 64, sp.toNat⟩, ⟨tbl.toNat, tbl.toNat + tableBytes⟩]

/-- What a0-boot's `RuntimeReady.window_log` needs of the windows. -/
structure Separate (H : List (Nat × Nat)) (sp tbl : BitVec 64) : Prop where
  pins : ∀ pin ∈ VsaIris.Sym.allocText, OutW (windows sp tbl) pin.1
  domain : OutWRange (windows sp tbl) Layout.sym_Caml_state 8
  pool : OutWRange (windows sp tbl) Layout.sym_pool 8
  heap : ∀ a, vsaFoot H a → OutW (windows sp tbl) a

theorem separate {H : List (Nat × Nat)} {sp tbl : BitVec 64} (frame : NativeFrame sp 64)
    (member : (tbl.toNat, tableBytes) ∈ H) (low : heapStart ≤ tbl.toNat) (high : tbl.toNat + tableBytes ≤ heapEnd) :
    Separate H sp tbl := by
  have lower := frame.lower
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pin hp
    have g := (allocator_sources pin hp).geometry.high
    simp only [windows, OutW, heapStart, heapEnd, tableBytes] at *
    refine ⟨?_, ?_, trivial⟩ <;> omega
  · simp only [windows, OutWRange, heapStart, heapEnd, tableBytes, Layout.sym_Caml_state] at *
    refine ⟨?_, ?_, trivial⟩ <;> omega
  · simp only [windows, OutWRange, heapStart, heapEnd, tableBytes, Layout.sym_pool] at *
    refine ⟨?_, ?_, trivial⟩ <;> omega
  · intro a owned
    have below := allocator_foot_below owned
    have outside := allocator_payload_outside member low owned
    simp only [windows, OutW, heapStart, heapEnd, tableBytes] at *
    refine ⟨?_, ?_, trivial⟩ <;> omega

/-- **The entry chain's route** from the callee's entry. -/
theorem entry_route {H capacity charge sp ra tbl s0 s1 s2 s3 wsz} {c : Config}
    (e : Entry H capacity charge sp ra tbl s0 s1 s2 s3 wsz c) :
    ReallocEntry.Route c.σ.mem sp s0 s3 ra s2 tbl s1 (read8 c.σ.mem tbl.toNat)
      (read8 c.σ.mem Layout.sym_Caml_state) (read8 c.σ.mem (firstDomainPtr.toNat + 80)) := by
  have f64 : NativeFrame sp 64 := e.frame.resize (by decide) (by decide)
  have lower := e.frame.lower
  have upper := e.frame.upper
  obtain ⟨tLow, tHigh⟩ := e.ready.block_bounds e.table
  have dom : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = firstDomainPtr := by
    rw [read8_value]; exact e.ready.domainWord
  have stackApart : ∀ x : Nat, x + 8 ≤ heapEnd → ∀ off, off + 8 ≤ 64 →
      x + 8 ≤ ((sp + -64#64) + BitVec.ofNat 64 off).toNat ∨
        ((sp + -64#64) + BitVec.ofNat 64 off).toNat + 8 ≤ x := fun x hx off h => by
    rw [frame_nat f64 off (by omega)]; simp only [allocHeadroom] at lower; omega
  have domNat : (firstDomainPtr + BitVec.ofNat 64 80).toNat = firstDomainPtr.toNat + 80 := by decide
  have csNat : (0x80064d08#64 : BitVec 64).toNat = Layout.sym_Caml_state := by decide
  have heapCS : Layout.sym_Caml_state + 8 ≤ heapEnd := by decide
  have heapDom : firstDomainPtr.toNat + 80 + 8 ≤ heapEnd := by decide
  have tNat0 := field_nat tHigh 0 (by decide)
  refine {
    control1 := by rw [read8_value]; exact e.empty
    write1 := frame_write f64 48 (by decide) (by decide)
    write2 := frame_write f64 24 (by decide) (by decide)
    write3 := frame_write f64 56 (by decide) (by decide)
    write4 := frame_write f64 32 (by decide) (by decide)
    read1 := field_read tLow tHigh 0 (by decide)
    pins1 := by
      change LPins8 (writeLog c.σ.mem []) _ _
      rw [tNat0]; exact read8_pins _ _
    apart1_1 := stackApart _ (by rw [tNat0]; unfold tableBytes at tHigh; omega) 48 (by decide)
    apart1_2 := stackApart _ (by rw [tNat0]; unfold tableBytes at tHigh; omega) 24 (by decide)
    apart1_3 := stackApart _ (by rw [tNat0]; unfold tableBytes at tHigh; omega) 56 (by decide)
    apart1_4 := stackApart _ (by rw [tNat0]; unfold tableBytes at tHigh; omega) 32 (by decide)
    read2 := by constructor <;> decide
    pins2 := by
      change LPins8 (writeLog (writeLog c.σ.mem []) _) _ _
      rw [csNat]
      apply lpins8_writeLog (read8_pins _ _)
      apply outLRange_of_forall
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact stackApart _ heapCS _ (by decide)
    write5 := frame_write f64 40 (by decide) (by decide)
    read3 := by rw [dom]; constructor <;> decide
    pins3 := by
      change LPins8 (writeLog (writeLog c.σ.mem []) _) _ _
      rw [dom, domNat]
      apply lpins8_writeLog (read8_pins _ _)
      apply outLRange_of_forall
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact stackApart _ heapDom _ (by decide)
    apart3_5 := by rw [dom, domNat]; exact stackApart _ heapDom 40 (by decide)
    write6 := field_write tLow tHigh e.tableAligned 48 (by decide) (by decide)
    write7 := field_write tLow tHigh e.tableAligned 40 (by decide) (by decide) }

/-- The entry chain's stores: the five saves and `reserve`/`size`. -/
def entryLog (sp tbl s0 s1 s2 s3 ra wsz : BitVec 64) : List WEntry :=
  [(((sp + -64#64) + BitVec.ofNat 64 48).toNat, 8, s0), (((sp + -64#64) + BitVec.ofNat 64 24).toNat, 8, s3),
   (((sp + -64#64) + BitVec.ofNat 64 56).toNat, 8, ra), (((sp + -64#64) + BitVec.ofNat 64 32).toNat, 8, s2),
   (((sp + -64#64) + BitVec.ofNat 64 40).toNat, 8, s1), ((tbl + BitVec.ofNat 64 48).toNat, 8, 0x100#64),
   ((tbl + BitVec.ofNat 64 40).toNat, 8, size wsz)]

theorem entryLog_inside {sp tbl s0 s1 s2 s3 ra wsz : BitVec 64} (frame : NativeFrame sp 64)
    (high : tbl.toNat + tableBytes ≤ heapEnd) :
    LogInW (windows sp tbl) (entryLog sp tbl s0 s1 s2 s3 ra wsz) := by
  simp only [entryLog, LogInW, windows, InsideW, frame_nat frame _ (by decide : 48 ≤ 64),
    frame_nat frame _ (by decide : 24 ≤ 64), frame_nat frame _ (by decide : 56 ≤ 64),
    frame_nat frame _ (by decide : 32 ≤ 64), frame_nat frame _ (by decide : 40 ≤ 64),
    field_nat high 48 (by decide), field_nat high 40 (by decide), tableBytes]
  have := frame.lower
  simp only [heapEnd, tableBytes] at this high ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

theorem windows_image {sp tbl : BitVec 64} (frame : NativeFrame sp 64) (low : heapStart ≤ tbl.toNat)
    {log : List WEntry} (inside : LogInW (windows sp tbl) log) : ImageOutside log := by
  have lower := frame.lower
  have text : Image.textBase + Image.textSize ≤ heapStart := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ heapStart := by decide
  constructor <;> apply OCaml.Vm.Sim.outLRange_of_windows inside <;>
    simp only [windows, OutWRange, heapStart, heapEnd] at * <;> refine ⟨?_, ?_, trivial⟩ <;> omega

/-- At the size product's `__muldi3` call (`9774`). -/
structure AtSizeCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra tbl s0 s1 s2 s3 wsz : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReady H (capacity + charge) (sp + -64#64) ra after
  pc : after.σ.regs.get? Register.PC = some ReallocEntry.call.pc
  regs : GHolds after.σ (ReallocEntry.state3 sp s0 s3 ra s2 tbl s1 0#64 firstDomainPtr wsz)
  memory : after.σ.mem = writeLog before.σ.mem (entryLog sp tbl s0 s1 s2 s3 ra wsz)

/-- **The entry chain under readiness.** -/
theorem entry_step {H capacity charge sp ra tbl s0 s1 s2 s3 wsz} {c : Config}
    (e : Entry H capacity charge sp ra tbl s0 s1 s2 s3 wsz c) :
    FnSummary ReallocEntry.pc (fun d => d = c) (AtSizeCall H capacity charge sp ra tbl s0 s1 s2 s3 wsz c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have f64 : NativeFrame sp 64 := e.frame.resize (by decide) (by decide)
  obtain ⟨tLow, tHigh⟩ := e.ready.block_bounds e.table
  obtain ⟨h8, h9, h18, h19, h10, -⟩ := e.saved
  have b1 : bytesVal .ld (read8 d.σ.mem tbl.toNat) = 0#64 := by rw [read8_value]; exact e.empty
  have b2 : bytesVal .ld (read8 d.σ.mem Layout.sym_Caml_state) = firstDomainPtr := by
    rw [read8_value]; exact e.ready.domainWord
  have b3 : bytesVal .ld (read8 d.σ.mem (firstDomainPtr.toNat + 80)) = wsz := by
    rw [read8_value]; exact e.minorWsz
  have input : ReallocEntry.Input sp s0 s3 ra s2 tbl s1 (read8 d.σ.mem tbl.toNat)
      (read8 d.σ.mem Layout.sym_Caml_state) (read8 d.σ.mem (firstDomainPtr.toNat + 80)) d :=
    { good := e.ready.good, tick := e.ready.tick, minstret := e.ready.minstret,
      code0 := e.refCode, code1 := e.genCode,
      registers := ⟨e.ready.stack, h8, h19, e.ready.raReg, h18, h10, h9, trivial⟩
      route := entry_route e }
  have log := ReallocEntry.log sp s0 s3 ra s2 tbl s1 (read8 d.σ.mem tbl.toNat)
      (read8 d.σ.mem Layout.sym_Caml_state) (read8 d.σ.mem (firstDomainPtr.toNat + 80))
  rw [b3] at log
  have inside := entryLog_inside (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (ra := ra) (wsz := wsz) f64 tHigh
  have W := registers_of_blocks (writes := [2, 8, 10, 11, 12, 13, 14, 15, 18, 19]) e.ready.image
    (windows_image f64 tLow inside) (ReallocEntry.run input) log (ReallocEntry.endpoint _ _ _ _ _ _ _ _)
    (ReallocEntry.registers _ _ _ _ _ _ _ _ _ _) rfl ReallocEntry.written
  obtain ⟨c1, run, post⟩ := W.run d ⟨pc, rfl⟩
  rw [b1, b2, b3] at post
  have sep := separate (H := H) f64 e.table tLow tHigh
  refine ⟨c1, run, ⟨?_, post.pc, post.regs, post.memory⟩⟩
  exact e.ready.window_log post (by decide) (by simp only [ReallocEntry.state3, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs rfl) (gholds_lookup (n := 1) _ post.regs rfl) e.ready.aligned
    inside sep.pins sep.domain sep.pool sep.heap

/-- Memory below the arena and outside malloc's globals: the realloc code. -/
def LowKept (m m' : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, startupLive a → a < heapStart → ¬ allocGlobal a → m'[a]? = m[a]?

theorem genCode_keep {m m' : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Realloc_generic_table_isra_0Loaded m)
    (same : LowKept m m') : Code.Realloc_generic_table_isra_0Loaded m' :=
  Code.realloc_generic_table_isra_0_transport code fun a lo hi =>
    same a (by unfold startupLive Vsa.Densify.ramBase Vsa.Densify.ramSize; omega) (by unfold heapStart; omega)
      (by unfold allocGlobal InRange; omega)

theorem refCode_keep {m m' : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Caml_realloc_ref_tableLoaded m)
    (same : LowKept m m') : Code.Caml_realloc_ref_tableLoaded m' :=
  Code.caml_realloc_ref_table_transport code fun a lo hi =>
    same a (by unfold startupLive Vsa.Densify.ramBase Vsa.Densify.ramSize; omega) (by unfold heapStart; omega)
      (by unfold allocGlobal InRange; omega)

/-- A store log inside the callee's windows keeps the low memory. -/
theorem lowKept_windows {sp tbl : BitVec 64} (frame : NativeFrame sp 64) (low : heapStart ≤ tbl.toNat)
    {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} (inside : LogInW (windows sp tbl) log) :
    LowKept m (writeLog m log) := by
  intro a _ below _
  apply frameOn_writeLog _ _ _ inside a
  have := frame.lower
  simp only [windows, OutW, heapStart, heapEnd] at *
  exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩

/-- After `caml_stat_alloc_noexc` returns (`977c`). -/
structure Allocated (H : List (Nat × Nat)) (capacity : Nat) (sp ra tbl s0 s1 s2 s3 wsz : BitVec 64)
    (before after : Config) where
  atAlloc : Config
  stat : StatAllocated H capacity (request wsz) (sp + -64#64) 0x8000977c#64 atAlloc after
  memory : atAlloc.σ.mem = writeLog before.σ.mem (entryLog sp tbl s0 s1 s2 s3 ra wsz)
  s0Reg : gprGet atAlloc.σ 8 = some tbl
  s1Reg : gprGet atAlloc.σ 9 = some s1
  s2Reg : gprGet atAlloc.σ 18 = some 0#64
  s3Reg : gprGet atAlloc.σ 19 = some 0x8#64

/-- **The prefix**: the entry chain, the size product and the allocation. -/
theorem prefix_run {H capacity charge sp ra tbl s0 s1 s2 s3 wsz} {c : Config}
    (e : Entry H capacity charge sp ra tbl s0 s1 s2 s3 wsz c) :
    FnSummary ReallocEntry.pc (fun d => d = c)
      (fun after => Nonempty (Allocated H capacity sp ra tbl s0 s1 s2 s3 wsz c after)) := by
  constructor
  rintro d ⟨pc, rfl⟩
  obtain ⟨c1, run1, A⟩ := (entry_step e).run d ⟨pc, rfl⟩
  have r := A.regs
  simp only [ReallocEntry.state3, GHolds] at r
  obtain ⟨ha0, -, -, h19, h8, h18, -, h11, -, -, -, h9, -⟩ := r
  have f64 : NativeFrame sp 64 := e.frame.resize (by decide) (by decide)
  obtain ⟨tLow, tHigh⟩ := e.ready.block_bounds e.table
  have code1 : Code.Realloc_generic_table_isra_0Loaded c1.σ.mem := by
    rw [A.memory]; exact genCode_keep e.genCode (lowKept_windows f64 tLow (entryLog_inside f64 tHigh))
  obtain ⟨c2, run2, M⟩ := (ready_muldi3 ReallocEntry.call_shape ReallocEntry.call_decode
    ReallocEntry.call_target (ReallocEntry.call_pins code1) A.ready ha0 h11 (by decide)).run c1 ⟨A.pc, rfl⟩
  rw [ReallocEntry.call_link] at M
  have keep (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (other : n ∉ [1, 10, 11, 12, 13]) :
      gprGet c2.σ n = gprGet c1.σ n := M.frame n lower upper other
  have code2 : Code.Realloc_generic_table_isra_0Loaded c2.σ.mem := by rw [M.memory]; exact code1
  obtain ⟨c3, run3, C⟩ := (ready_call ReallocAllocCall.call_shape ReallocAllocCall.call_decode
    (ReallocAllocCall.call_pins code2) M.ready [(10, request wsz)] ⟨M.result, trivial⟩
    (by simp only [keysG, List.map]; decide) (by simp [KeysAvoidRa, keysG]) _ rfl (by decide)).run c2 ⟨M.pc, rfl⟩
  have ready3 : RuntimeReady H (capacity + charge) (sp + -64#64) 0x8000977c#64 c3 := by
    have r := C.ready; rw [ReallocAllocCall.call_link] at r; exact r
  have frameA : NativeFrame (sp + -64#64) allocHeadroom := e.frame.nested (front := 64) (by decide)
  obtain ⟨c4, run4, ⟨S⟩⟩ := (stat_alloc_ready c3 H capacity charge (request wsz) _ _ ready3 frameA
    C.regs.1 e.charged).run c3
    ⟨by have h := C.pc; rw [ReallocAllocCall.call_target] at h; exact h, rfl⟩
  have via (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (other : n ∉ [1, 10, 11, 12, 13]) :
      gprGet c3.σ n = gprGet c1.σ n :=
    (C.frame n lower upper (by simp at other; omega)).trans (keep n lower upper other)
  exact ⟨c4, run1.trans (run2.trans (run3.trans run4)), ⟨⟨c3, S, by rw [C.memory, M.memory, A.memory],
    (via 8 (by decide) (by decide) (by decide)).trans h8, (via 9 (by decide) (by decide) (by decide)).trans h9,
    (via 18 (by decide) (by decide) (by decide)).trans h18, (via 19 (by decide) (by decide) (by decide)).trans h19⟩⟩⟩

end OCaml.Vm.Gc.Realloc
