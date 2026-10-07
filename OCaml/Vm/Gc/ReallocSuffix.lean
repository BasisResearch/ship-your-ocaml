import OCaml.Vm.Gc.ReallocPrefix
import OCaml.Vm.Gc.Generated.ReallocInstall
import OCaml.Vm.Gc.Generated.ReallocLimit
import OCaml.Vm.Gc.Generated.ReallocReturn
import OCaml.Vm.Sim.LogRead

/-!
# `caml_realloc_ref_table` on an unallocated table: after the allocation

From `caml_stat_alloc_noexc`'s return: `base`/`ptr` installed
(`ReallocInstall`), `__muldi3(8, size)`, `threshold`/`limit`
(`ReallocLimit`), `__muldi3(size + reserve, 8)`, `end`, the frame restored and
`ret` (`ReallocReturn`).
-/

namespace OCaml.Vm.Gc.Realloc
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris VsaIris.VsaHeap
  LeanRV64DExecutable

/-- The words the suffix reads: the table's `base`, `size` and `reserve`,
and the five saved registers in the native frame. -/
structure Words (m : Std.ExtHashMap Nat (BitVec 8)) (sp tbl s0 s1 s2 s3 ra wsz : BitVec 64) : Prop where
  base : bytesT m tbl.toNat 8 = 0#64
  size : bytesT m (tbl.toNat + 40) 8 = size wsz
  reserve : bytesT m (tbl.toNat + 48) 8 = 0x100#64
  savedS0 : bytesT m (sp.toNat - 64 + 48) 8 = s0
  savedS3 : bytesT m (sp.toNat - 64 + 24) 8 = s3
  savedRa : bytesT m (sp.toNat - 64 + 56) 8 = ra
  savedS2 : bytesT m (sp.toNat - 64 + 32) 8 = s2
  savedS1 : bytesT m (sp.toNat - 64 + 40) 8 = s1

/-- The entry chain leaves the words in place. -/
theorem words_entry {H capacity charge sp ra tbl s0 s1 s2 s3 wsz} {c : Config}
    (e : Entry H capacity charge sp ra tbl s0 s1 s2 s3 wsz c) :
    Words (writeLog c.σ.mem (entryLog sp tbl s0 s1 s2 s3 ra wsz)) sp tbl s0 s1 s2 s3 ra wsz := by
  have f64 : NativeFrame sp 64 := e.frame.resize (by decide) (by decide)
  obtain ⟨tLow, tHigh⟩ := e.ready.block_bounds e.table
  have lower := e.frame.lower
  have n48 := frame_nat f64 48 (by decide)
  have n24 := frame_nat f64 24 (by decide)
  have n56 := frame_nat f64 56 (by decide)
  have n32 := frame_nat f64 32 (by decide)
  have n40 := frame_nat f64 40 (by decide)
  have t48 := field_nat tHigh 48 (by decide)
  have t40 := field_nat tHigh 40 (by decide)
  simp only [heapEnd, tableBytes, allocHeadroom] at tHigh lower
  have read (i : Nat) (a : Nat) (v : BitVec 64)
      (selected : (entryLog sp tbl s0 s1 s2 s3 ra wsz)[i]? = some (a, 8, v))
      (outside : ∀ x ∈ (entryLog sp tbl s0 s1 s2 s3 ra wsz).drop (i + 1), a + 8 ≤ x.1 ∨ x.1 + x.2.1 ≤ a) :
      bytesT (writeLog c.σ.mem (entryLog sp tbl s0 s1 s2 s3 ra wsz)) a 8 = v :=
    word_writeLog_at _ _ i a v selected (outLRange_of_forall outside)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bytesT_writeLog_out _ (outLRange_of_forall fun x hx => by
      simp only [entryLog, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)]
    exact e.empty
  · exact read 6 _ _ (by simp only [entryLog, t40, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => absurd hx (by simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.not_mem_nil,
        not_false_eq_true]))
  · exact read 5 _ _ (by simp only [entryLog, t48, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => by
        simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)
  · exact read 0 _ _ (by simp only [entryLog, n48, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => by
        simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)
  · exact read 1 _ _ (by simp only [entryLog, n24, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => by
        simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)
  · exact read 2 _ _ (by simp only [entryLog, n56, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => by
        simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)
  · exact read 3 _ _ (by simp only [entryLog, n32, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => by
        simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)
  · exact read 4 _ _ (by simp only [entryLog, n40, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (fun x hx => by
        simp only [entryLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [n48, n24, n56, n32, n40, t48, t40] <;> omega)

/-- The allocation keeps every byte of another live block. -/
theorem alloc_live_byte {H capacity n sp ra before after} (w : StatAllocated H capacity n sp ra before after)
    (frame : NativeFrame sp allocHeadroom) {q m a : Nat} (member : (q, m) ∈ H) (low : heapStart ≤ q)
    (high : q + m ≤ heapEnd) (inside : q ≤ a ∧ a < q + m) :
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 := by
  have unchanged := w.allocation.memory a (by
    intro owned
    rcases owned with scratch | foot
    · unfold stackWin InExt at scratch
      have := frame.lower
      omega
    · rcases allocator_payload_outside member low foot with h | h <;> omega)
  change (after.σ.mem[a]?).getD 0 = (w.atMalloc.σ.mem[a]?).getD 0 at unchanged
  rw [unchanged, w.dispatch.memory]

theorem frameSp_nat {sp : BitVec 64} (f : NativeFrame sp 64) : (sp + -64#64).toNat = sp.toNat - 64 :=
  f.stack_nat

/-- The words survive the allocation. -/
theorem words_alloc {H capacity n sp ra' before after} {ra tbl s0 s1 s2 s3 wsz : BitVec 64}
    (w : StatAllocated H capacity n (sp + -64#64) ra' before after)
    (frame : NativeFrame sp (64 + allocHeadroom)) (member : (tbl.toNat, tableBytes) ∈ H)
    (low : heapStart ≤ tbl.toNat) (high : tbl.toNat + tableBytes ≤ heapEnd)
    (words : Words before.σ.mem sp tbl s0 s1 s2 s3 ra wsz) : Words after.σ.mem sp tbl s0 s1 s2 s3 ra wsz := by
  have frameA : NativeFrame (sp + -64#64) allocHeadroom := frame.nested (front := 64) (by decide)
  have f64 : NativeFrame sp 64 := frame.resize (by decide) (by decide)
  have base := frameSp_nat f64
  have slot (off : Nat) (h : off + 8 ≤ 64) : bytesT after.σ.mem (sp.toNat - 64 + off) 8 =
      bytesT before.σ.mem (sp.toNat - 64 + off) 8 :=
    word_observed _ fun i _ => w.caller_byte frameA (by rw [base]; omega)
  have field (off : Nat) (h : off + 8 ≤ tableBytes) : bytesT after.σ.mem (tbl.toNat + off) 8 =
      bytesT before.σ.mem (tbl.toNat + off) 8 :=
    word_observed _ fun i hi => alloc_live_byte w frameA member low high (by unfold tableBytes at *; omega)
  have field0 : bytesT after.σ.mem tbl.toNat 8 = bytesT before.σ.mem tbl.toNat 8 := field 0 (by decide)
  exact ⟨by rw [field0]; exact words.base, by rw [field 40 (by decide)]; exact words.size,
    by rw [field 48 (by decide)]; exact words.reserve, by rw [slot 48 (by decide)]; exact words.savedS0,
    by rw [slot 24 (by decide)]; exact words.savedS3, by rw [slot 56 (by decide)]; exact words.savedRa,
    by rw [slot 32 (by decide)]; exact words.savedS2, by rw [slot 40 (by decide)]; exact words.savedS1⟩

/-- A store chain inside the callee's windows that keeps `sp` and `ra` keeps readiness. -/
theorem chain_ready {H capacity fsp ra before after writes log pc value regs} {sp tbl : BitVec 64}
    (ready : RuntimeReady H capacity fsp ra before) (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gp : 3 ∉ writes)
    (noSp : 2 ∉ writes) (noRa : 1 ∉ writes) (inside : LogInW (windows sp tbl) log)
    (sep : Separate H sp tbl) : RuntimeReady H capacity fsp ra after :=
  ready.window_log post keys cover gp
    ((post.toEffectPost.gpr_frame keys 2 (by decide) (by decide) noSp).trans ready.stack)
    ((post.toEffectPost.gpr_frame keys 1 (by decide) (by decide) noRa).trans ready.raReg) ready.aligned
    inside sep.pins sep.domain sep.pool sep.heap

/-- After the allocation, at `977c`. -/
structure AfterAlloc (H : List (Nat × Nat)) (capacity : Nat) (sp tbl s0 s1 s2 s3 ra wsz p : BitVec 64)
    (c : Config) : Prop where
  ready : RuntimeReady H capacity (sp + -64#64) 0x8000977c#64 c
  frame : NativeFrame sp (64 + allocHeadroom)
  table : (tbl.toNat, tableBytes) ∈ H
  tableAligned : tbl.toNat % 8 = 0
  words : Words c.σ.mem sp tbl s0 s1 s2 s3 ra wsz
  result : gprGet c.σ 10 = some p
  nonzero : p ≠ 0#64
  s0Reg : gprGet c.σ 8 = some tbl
  s3Reg : gprGet c.σ 19 = some 0x8#64
  code : Code.Realloc_generic_table_isra_0Loaded c.σ.mem

/-- `base` and `ptr` installed. -/
def installLog (tbl p : BitVec 64) : List WEntry :=
  [((tbl + BitVec.ofNat 64 0).toNat, 8, p), ((tbl + BitVec.ofNat 64 24).toNat, 8, p)]

/-- At the threshold product's `__muldi3` call (`97a4`). -/
structure AtThresholdCall (H : List (Nat × Nat)) (capacity : Nat) (sp tbl wsz p : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReady H capacity (sp + -64#64) 0x8000977c#64 after
  pc : after.σ.regs.get? Register.PC = some ReallocInstall.call.pc
  regs : GHolds after.σ (ReallocInstall.state3 p tbl 0x8#64 0#64 (size wsz))
  memory : after.σ.mem = writeLog before.σ.mem (installLog tbl p)
  out : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  callee : ∀ k ∈ calleeRest, gprGet after.σ k = gprGet before.σ k

/-- **`base == NULL`, so no free; `base` and `ptr` are installed.** -/
theorem install_step {H capacity sp tbl s0 s1 s2 s3 ra wsz p} {c : Config}
    (a : AfterAlloc H capacity sp tbl s0 s1 s2 s3 ra wsz p c) :
    FnSummary ReallocInstall.pc (fun d => d = c) (AtThresholdCall H capacity sp tbl wsz p c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have f64 : NativeFrame sp 64 := a.frame.resize (by decide) (by decide)
  obtain ⟨tLow, tHigh⟩ := a.ready.block_bounds a.table
  have t0 := field_nat tHigh 0 (by decide)
  have t40 := field_nat tHigh 40 (by decide)
  have b1 : bytesVal .ld (read8 d.σ.mem tbl.toNat) = 0#64 := by rw [read8_value]; exact a.words.base
  have b2 : bytesVal .ld (read8 d.σ.mem (tbl.toNat + 40)) = size wsz := by rw [read8_value]; exact a.words.size
  have input : ReallocInstall.Input p tbl 0x8#64 (read8 d.σ.mem tbl.toNat) (read8 d.σ.mem (tbl.toNat + 40)) d :=
    { good := a.ready.good, tick := a.ready.tick, minstret := a.ready.minstret, code0 := a.code,
      registers := ⟨a.result, a.s0Reg, a.s3Reg, trivial⟩
      route := {
        control0 := a.nonzero
        read1 := field_read tLow tHigh 0 (by decide)
        pins1 := by change LPins8 (writeLog d.σ.mem []) _ _; rw [t0]; exact read8_pins _ _
        control1 := b1
        read2 := field_read tLow tHigh 40 (by decide)
        pins2 := by change LPins8 (writeLog (writeLog d.σ.mem []) []) _ _; rw [t40]; exact read8_pins _ _
        write1 := field_write tLow tHigh a.tableAligned 0 (by decide) (by decide)
        write2 := field_write tLow tHigh a.tableAligned 24 (by decide) (by decide) } }
  have inside : LogInW (windows sp tbl) (installLog tbl p) := by
    simp only [installLog, LogInW, windows, InsideW, t0, field_nat tHigh 24 (by decide), tableBytes]
    refine ⟨?_, ?_, trivial⟩ <;> right <;> left <;> omega
  have W := registers_of_blocks (writes := [9, 10, 11, 18]) a.ready.image (windows_image f64 tLow inside)
    (ReallocInstall.run input) (ReallocInstall.log _ _ _ _ _) (ReallocInstall.endpoint _ _ _ _)
    (ReallocInstall.registers _ _ _ _ _) rfl ReallocInstall.written
  obtain ⟨c1, run, post⟩ := W.run d ⟨pc, rfl⟩
  rw [b1, b2] at post
  refine ⟨c1, run, ⟨?_, post.pc, post.regs, post.memory,
    by simp only [Vsa.Machine.output, post.output],
    callee_of_frame (fun n lo hi out => post.toEffectPost.gpr_frame (by decide) n lo hi out) (by decide)⟩⟩
  exact chain_ready a.ready post (by decide) (by simp only [ReallocInstall.state3, keysG]; decide) (by decide)
    (by decide) (by decide) inside (separate f64 a.table tLow tHigh)

/-- `Words` without `base`: what survives the stores to the table's first five fields. -/
structure Rest (m : Std.ExtHashMap Nat (BitVec 8)) (sp tbl s0 s1 s2 s3 ra wsz : BitVec 64) : Prop where
  size : bytesT m (tbl.toNat + 40) 8 = size wsz
  reserve : bytesT m (tbl.toNat + 48) 8 = 0x100#64
  savedS0 : bytesT m (sp.toNat - 64 + 48) 8 = s0
  savedS3 : bytesT m (sp.toNat - 64 + 24) 8 = s3
  savedRa : bytesT m (sp.toNat - 64 + 56) 8 = ra
  savedS2 : bytesT m (sp.toNat - 64 + 32) 8 = s2
  savedS1 : bytesT m (sp.toNat - 64 + 40) 8 = s1

theorem Words.rest {m : Std.ExtHashMap Nat (BitVec 8)} {sp tbl s0 s1 s2 s3 ra wsz : BitVec 64}
    (w : Words m sp tbl s0 s1 s2 s3 ra wsz) : Rest m sp tbl s0 s1 s2 s3 ra wsz :=
  ⟨w.size, w.reserve, w.savedS0, w.savedS3, w.savedRa, w.savedS2, w.savedS1⟩

/-- Stores to the table's first five fields keep the rest. -/
theorem Rest.writeLog {m : Std.ExtHashMap Nat (BitVec 8)} {sp tbl s0 s1 s2 s3 ra wsz : BitVec 64}
    {log : List WEntry} (r : Rest m sp tbl s0 s1 s2 s3 ra wsz) (frame : NativeFrame sp 64)
    (high : tbl.toNat + tableBytes ≤ heapEnd)
    (fields : ∀ e ∈ log, tbl.toNat ≤ e.1 ∧ e.1 + e.2.1 ≤ tbl.toNat + 40) :
    Rest (Vsa.Sim.writeLog m log) sp tbl s0 s1 s2 s3 ra wsz := by
  have lower := frame.lower
  simp only [heapEnd, tableBytes] at lower high
  have keep (x : Nat) (out : tbl.toNat + 40 ≤ x) : bytesT (Vsa.Sim.writeLog m log) x 8 = bytesT m x 8 :=
    bytesT_writeLog_out _ (outLRange_of_forall fun e he => Or.inr (by have := fields e he; omega))
  exact ⟨by rw [keep _ (by omega)]; exact r.size, by rw [keep _ (by omega)]; exact r.reserve,
    by rw [keep _ (by omega)]; exact r.savedS0, by rw [keep _ (by omega)]; exact r.savedS3,
    by rw [keep _ (by omega)]; exact r.savedRa, by rw [keep _ (by omega)]; exact r.savedS2,
    by rw [keep _ (by omega)]; exact r.savedS1⟩

/-- `threshold` and `limit` installed. -/
def limitLog (tbl v : BitVec 64) : List WEntry :=
  [((tbl + BitVec.ofNat 64 16).toNat, 8, v), ((tbl + BitVec.ofNat 64 32).toNat, 8, v)]

/-- Before the threshold/limit stores, at `97a8`. -/
structure BeforeLimit (H : List (Nat × Nat)) (capacity : Nat) (sp tbl s0 s1 s2 s3 ra wsz p link : BitVec 64)
    (c : Config) : Prop where
  ready : RuntimeReady H capacity (sp + -64#64) link c
  frame : NativeFrame sp (64 + allocHeadroom)
  table : (tbl.toNat, tableBytes) ∈ H
  tableAligned : tbl.toNat % 8 = 0
  rest : Rest c.σ.mem sp tbl s0 s1 s2 s3 ra wsz
  s0Reg : gprGet c.σ 8 = some tbl
  s1Reg : gprGet c.σ 9 = some p
  result : gprGet c.σ 10 = some (0x8#64 * size wsz)
  s3Reg : gprGet c.σ 19 = some 0x8#64
  s2Reg : gprGet c.σ 18 = some (size wsz)
  code : Code.Realloc_generic_table_isra_0Loaded c.σ.mem

/-- At the end product's `__muldi3` call (`97c0`). -/
structure AtEndCall (H : List (Nat × Nat)) (capacity : Nat) (sp tbl wsz p link : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReady H capacity (sp + -64#64) link after
  pc : after.σ.regs.get? Register.PC = some ReallocLimit.call.pc
  regs : GHolds after.σ (ReallocLimit.state1 tbl p (0x8#64 * size wsz) 0x8#64 (size wsz) 0x100#64)
  memory : after.σ.mem = writeLog before.σ.mem (limitLog tbl (p + 0x8#64 * size wsz))
  out : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  callee : ∀ k ∈ calleeRest, gprGet after.σ k = gprGet before.σ k

/-- **`threshold := limit := base + size * 8`.** -/
theorem limit_step {H capacity sp tbl s0 s1 s2 s3 ra wsz p link} {c : Config}
    (b : BeforeLimit H capacity sp tbl s0 s1 s2 s3 ra wsz p link c) :
    FnSummary ReallocLimit.pc (fun d => d = c) (AtEndCall H capacity sp tbl wsz p link c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have f64 : NativeFrame sp 64 := b.frame.resize (by decide) (by decide)
  obtain ⟨tLow, tHigh⟩ := b.ready.block_bounds b.table
  have t48 := field_nat tHigh 48 (by decide)
  have b1 : bytesVal .ld (read8 d.σ.mem (tbl.toNat + 48)) = 0x100#64 := by rw [read8_value]; exact b.rest.reserve
  have input : ReallocLimit.Input tbl p (0x8#64 * size wsz) 0x8#64 (size wsz) (read8 d.σ.mem (tbl.toNat + 48)) d :=
    { good := b.ready.good, tick := b.ready.tick, minstret := b.ready.minstret, code0 := b.code,
      registers := ⟨b.s0Reg, b.s1Reg, b.result, b.s3Reg, b.s2Reg, trivial⟩
      route := {
        read1 := field_read tLow tHigh 48 (by decide)
        pins1 := by change LPins8 d.σ.mem _ _; rw [t48]; exact read8_pins _ _
        write1 := field_write tLow tHigh b.tableAligned 16 (by decide) (by decide)
        write2 := field_write tLow tHigh b.tableAligned 32 (by decide) (by decide) } }
  have inside : LogInW (windows sp tbl) (limitLog tbl (p + 0x8#64 * size wsz)) := by
    simp only [limitLog, LogInW, windows, InsideW, field_nat tHigh 16 (by decide),
      field_nat tHigh 32 (by decide), tableBytes]
    refine ⟨?_, ?_, trivial⟩ <;> right <;> left <;> omega
  have W := registers_of_blocks (writes := [10, 11, 14, 15]) b.ready.image (windows_image f64 tLow inside)
    (ReallocLimit.run input) (ReallocLimit.log _ _ _ _ _ _) (ReallocLimit.endpoint _ _ _ _ _ _)
    (ReallocLimit.registers _ _ _ _ _ _) rfl ReallocLimit.written
  obtain ⟨c1, run, post⟩ := W.run d ⟨pc, rfl⟩
  rw [b1] at post
  refine ⟨c1, run, ⟨?_, post.pc, post.regs, post.memory,
    by simp only [Vsa.Machine.output, post.output],
    callee_of_frame (fun n lo hi out => post.toEffectPost.gpr_frame (by decide) n lo hi out) (by decide)⟩⟩
  exact chain_ready b.ready post (by decide) (by simp only [ReallocLimit.state1, keysG]; decide) (by decide)
    (by decide) (by decide) inside (separate f64 b.table tLow tHigh)

/-- `end` installed. -/
def endLog (tbl v : BitVec 64) : List WEntry := [((tbl + BitVec.ofNat 64 8).toNat, 8, v)]

/-- Before `end` and the return, at `97c4`. -/
structure BeforeReturn (H : List (Nat × Nat)) (capacity : Nat) (sp tbl s0 s1 s2 s3 ra wsz p link : BitVec 64)
    (c : Config) : Prop where
  ready : RuntimeReady H capacity (sp + -64#64) link c
  frame : NativeFrame sp (64 + allocHeadroom)
  table : (tbl.toNat, tableBytes) ∈ H
  tableAligned : tbl.toNat % 8 = 0
  rest : Rest c.σ.mem sp tbl s0 s1 s2 s3 ra wsz
  raAligned : ra.toNat % 4 = 0
  s0Reg : gprGet c.σ 8 = some tbl
  s1Reg : gprGet c.σ 9 = some p
  result : gprGet c.σ 10 = some ((size wsz + 0x100#64) * 0x8#64)
  code : Code.Realloc_generic_table_isra_0Loaded c.σ.mem

/-- Returned to the caller. -/
structure Returned (H : List (Nat × Nat)) (capacity : Nat) (sp tbl s0 s1 s2 s3 ra wsz p : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReady H capacity sp ra after
  pc : after.σ.regs.get? Register.PC = some ra
  regs : GHolds after.σ (ReallocReturn.state1 p ((size wsz + 0x100#64) * 0x8#64) tbl (sp + -64#64) ra s0 s1 s2 s3)
  memory : after.σ.mem = writeLog before.σ.mem (endLog tbl (p + (size wsz + 0x100#64) * 0x8#64))
  out : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  callee : ∀ k ∈ calleeRest, gprGet after.σ k = gprGet before.σ k

theorem frame_pop (sp : BitVec 64) : sp + -64#64 + 64#64 = sp := by
  rw [BitVec.add_assoc]; simp

/-- **`end := base + (size + reserve) * 8`, restore and `ret`.** -/
theorem return_step {H capacity sp tbl s0 s1 s2 s3 ra wsz p link} {c : Config}
    (b : BeforeReturn H capacity sp tbl s0 s1 s2 s3 ra wsz p link c) :
    FnSummary ReallocReturn.pc (fun d => d = c) (Returned H capacity sp tbl s0 s1 s2 s3 ra wsz p c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have f64 : NativeFrame sp 64 := b.frame.resize (by decide) (by decide)
  obtain ⟨tLow, tHigh⟩ := b.ready.block_bounds b.table
  have lower := b.frame.lower
  have t8 := field_nat tHigh 8 (by decide)
  have slot (off : Nat) (h : off + 8 ≤ 64) :
      ((sp + -64#64) + BitVec.ofNat 64 off).toNat = sp.toNat - 64 + off := frame_nat f64 off (by omega)
  have value (off : Nat) (h : off + 8 ≤ 64) (v : BitVec 64) (hv : bytesT d.σ.mem (sp.toNat - 64 + off) 8 = v) :
      bytesVal .ld (read8 d.σ.mem (sp.toNat - 64 + off)) = v := by rw [read8_value]; exact hv
  have apart (off : Nat) (h : off + 8 ≤ 64) :
      ((sp + -64#64) + BitVec.ofNat 64 off).toNat + 8 ≤ (tbl + BitVec.ofNat 64 8).toNat ∨
        (tbl + BitVec.ofNat 64 8).toNat + 8 ≤ ((sp + -64#64) + BitVec.ofNat 64 off).toNat := by
    rw [slot off h, t8]; simp only [heapEnd, tableBytes, allocHeadroom] at tHigh lower; omega
  have pins (off : Nat) (h : off + 8 ≤ 64) :
      LPins8 d.σ.mem ((sp + -64#64) + BitVec.ofNat 64 off).toNat (read8 d.σ.mem (sp.toNat - 64 + off)) := by
    rw [slot off h]; exact read8_pins _ _
  have v1 := value 56 (by decide) _ b.rest.savedRa
  have input : ReallocReturn.Input p ((size wsz + 0x100#64) * 0x8#64) tbl (sp + -64#64)
      (read8 d.σ.mem (sp.toNat - 64 + 56)) (read8 d.σ.mem (sp.toNat - 64 + 48)) (read8 d.σ.mem (sp.toNat - 64 + 40))
      (read8 d.σ.mem (sp.toNat - 64 + 32)) (read8 d.σ.mem (sp.toNat - 64 + 24)) d :=
    { good := b.ready.good, tick := b.ready.tick, minstret := b.ready.minstret, code0 := b.code,
      registers := ⟨b.s1Reg, b.result, b.s0Reg, b.ready.stack, trivial⟩
      route := {
        write1 := field_write tLow tHigh b.tableAligned 8 (by decide) (by decide)
        read1 := (frame_write f64 56 (by decide) (by decide)).read
        pins1 := pins 56 (by decide)
        apart1_1 := apart 56 (by decide)
        read2 := (frame_write f64 48 (by decide) (by decide)).read
        pins2 := pins 48 (by decide)
        apart2_1 := apart 48 (by decide)
        read3 := (frame_write f64 40 (by decide) (by decide)).read
        pins3 := pins 40 (by decide)
        apart3_1 := apart 40 (by decide)
        read4 := (frame_write f64 32 (by decide) (by decide)).read
        pins4 := pins 32 (by decide)
        apart4_1 := apart 32 (by decide)
        read5 := (frame_write f64 24 (by decide) (by decide)).read
        pins5 := pins 24 (by decide)
        apart5_1 := apart 24 (by decide)
        control0 := by rw [v1]; exact b.raAligned } }
  have inside : LogInW (windows sp tbl) (endLog tbl (p + (size wsz + 0x100#64) * 0x8#64)) := by
    simp only [endLog, LogInW, windows, InsideW, t8, tableBytes]
    refine ⟨?_, trivial⟩; right; left; omega
  have W := registers_of_blocks (writes := [1, 2, 8, 9, 18, 19]) b.ready.image (windows_image f64 tLow inside)
    (ReallocReturn.run input) (ReallocReturn.log _ _ _ _ _ _ _ _ _)
    (ReallocReturn.endpoint _ _ _ _ _ _ _ _ _ (by rw [v1]; exact b.raAligned))
    (ReallocReturn.registers _ _ _ _ _ _ _ _ _) rfl ReallocReturn.written
  obtain ⟨c1, run, post⟩ := W.run d ⟨pc, rfl⟩
  rw [v1, value 48 (by decide) _ b.rest.savedS0, value 40 (by decide) _ b.rest.savedS1,
    value 32 (by decide) _ b.rest.savedS2, value 24 (by decide) _ b.rest.savedS3] at post
  refine ⟨c1, run, ⟨?_, post.pc, post.regs, post.memory,
    by simp only [Vsa.Machine.output, post.output],
    callee_of_frame (fun n lo hi out => post.toEffectPost.gpr_frame (by decide) n lo hi out) (by decide)⟩⟩
  have sep := separate f64 b.table tLow tHigh
  exact b.ready.window_log post (by decide) (by simp only [ReallocReturn.state1, keysG]; decide) (by decide)
    (by rw [← frame_pop sp]; exact gholds_lookup (n := 2) _ post.regs rfl)
    (gholds_lookup (n := 1) _ post.regs rfl) b.raAligned inside sep.pins sep.domain sep.pool sep.heap

end OCaml.Vm.Gc.Realloc
