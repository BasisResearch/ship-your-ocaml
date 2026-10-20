import OCaml.Vm.Primitives.Uncaught.Sflush
import OCaml.Vm.Primitives.Uncaught.StdioClose

/-!
# `__sflush_r` on the three standard streams at `exit`

The `FILE`s live in `.bss` at `__sf` (stdin), `__sf + 184` (stdout) and
`__sf + 368` (stderr). At the fatal path's `exit` none has pending output:
stdin was never read (flags `__SRD`, `_r = _ur = 0`), stdout was never
written through stdio (flags `__SWR | __SLBF`, no buffer), and stderr was
written unbuffered by the report (flags `__SORD | __SRW | __SWR | __SNBF`,
`_p = _base`). Each flush returns 0 (`flush_stdin`, `flush_stdout`,
`flush_stderr`).
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioFlush
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some)
open OCaml.Vm.Boot.Startup (NativeFrame)
open OCaml.Vm.Primitives.Uncaught.StdioClose (frame_nat frame_word frame_outside)

def stdinFile : BitVec 64 := 0x8007ca38#64
def stdoutFile : BitVec 64 := 0x8007caf0#64
def stderrFile : BitVec 64 := 0x8007cba8#64

/-- The flush prologue's three saves (`s0`, `s3`, `ra`). -/
def flushSaves (sp ra s0 s3 : BitVec 64) : List WEntry :=
  [((sp - 48#64 + 32#64).toNat, 8, s0), ((sp - 48#64 + 8#64).toNat, 8, s3), ((sp - 48#64 + 40#64).toNat, 8, ra)]

/-- stdin's flush: the saves, then `_flags |= __SNPT`'s neighbour bit 0x800. -/
def stdinFlushLog (sp ra s0 s3 : BitVec 64) : List WEntry :=
  flushSaves sp ra s0 s3 ++ [((stdinFile + 16#64).toNat, 2, 0x804#64)]


/-- **`__sflush_r`'s epilogue** at `0x8003e620`: `ra`, `s0`, `s3` reloaded from
the 48-byte frame, `0` returned. -/
theorem flush_epilogue {r ra sp s0 s3 v : BitVec 64} {c : Config} (h : LeafInput r c)
    (spR : gprGet c.σ 2 = some (sp + 18446744073709551568#64)) (a0 : gprGet c.σ 10 = some v)
    (frame : NativeFrame sp 48)
    (raS : bytesVal .ld (read8 c.σ.mem (sp + 18446744073709551568#64 + 40#64).toNat) = ra) (raAl : ra.toNat % 4 = 0)
    (s0S : bytesVal .ld (read8 c.σ.mem (sp + 18446744073709551568#64 + 32#64).toNat) = s0)
    (s3S : bytesVal .ld (read8 c.σ.mem (sp + 18446744073709551568#64 + 8#64).toNat) = s3) :
    FnSummary 0x8003e620#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 10, 19] [] c ra 0#64 [(2, sp), (8, s0), (19, s3)]) := by
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have l : LeafInput (regsAt c 1) c := by rw [regsAt_of h.raReg]; exact h
  have w (off : Nat) (ho : off + 8 ≤ 48) (al : off % 8 = 0) : ReadWindow (sp + 18446744073709551568#64 +
      BitVec.ofNat 64 off) 8 := by
    rw [sp48]; exact (frame_word (k := 48) frame (by decide) ho (by decide) al).read
  apply (Sflush.leave_fast c ra (regsAt c) l
    (by simp only [Sflush.leave_input, GHolds, regsAt_of spR, regsAt_of a0]; exact ⟨spR, a0, trivial⟩)
    (by rw [regsAt_of spR]; exact w 40 (by decide) (by decide))
    (by rw [regsAt_of spR]; exact w 32 (by decide) (by decide))
    (by rw [regsAt_of spR]; exact w 8 (by decide) (by decide))
    (by rw [regsAt_of spR]; exact raS) raAl).weaken (fun _ e => e)
  intro d p
  have o := p.regs
  simp only [Sflush.leave_regs, Sflush.leave_loads, regsAt_of spR, List.getD_cons_zero, List.getD_cons_succ,
    GHolds] at o
  exact ⟨p.toEffectPost, by rw [o.1, BitVec.add_assoc]; simp, by rw [o.2.2.2.1, s0S], by rw [o.2.2.1, s3S], trivial⟩

/-- **`__sflush_r(reent, stdin)`**, stdin never read: returns 0. -/
theorem flush_stdin {ra sp s0 s3 reent : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s3r : gprGet c.σ 19 = some s3)
    (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some stdinFile) (frame : NativeFrame sp 48)
    (flags : bytesVal .lh (read8 c.σ.mem (stdinFile + 16#64).toNat) = 4#64)
    (r : bytesVal .lw (read8 c.σ.mem (stdinFile + 8#64).toNat) = 0#64)
    (ur : bytesVal .lw (read8 c.σ.mem (stdinFile + 112#64).toNat) = 0#64) :
    FnSummary 0x8003e4f4#64 (fun d => d = c)
      (WriteRegistersPost ([2, 8, 14, 15, 19] ++ [13, 15] ++ [13] ++ [] ++ [1, 2, 8, 10, 19])
        (stdinFlushLog sp ra s0 s3) c ra 0#64 [(2, sp), (8, s0), (19, s3)]) := by
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have r8 := regsAt_of s0r
  have r19 := regsAt_of s3r
  have r10 := regsAt_of a0
  have r11 := regsAt_of a1
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have lo := frame.lower
  have hiS := frame.upper
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo hiS
  have nat (off : Nat) (ho : off ≤ 48) : (sp - 48#64 + BitVec.ofNat 64 off).toNat = sp.toNat - 48 + off :=
    frame_nat (k := 48) frame (by decide) ho
  have saves : ImageOutside (flushSaves sp ra s0 s3) := by
    have f32 := frame_outside (k := 48) (off := 32) (w := 8) (v := s0) frame (by decide) (by decide)
    have f8 := frame_outside (k := 48) (off := 8) (w := 8) (v := s3) frame (by decide) (by decide)
    have f40 := frame_outside (k := 48) (off := 40) (w := 8) (v := ra) frame (by decide) (by decide)
    exact ⟨⟨f32.1.1, f8.1.1, f40.1.1, trivial⟩, ⟨f32.2.1, f8.2.1, f40.2.1, trivial⟩⟩
  -- prologue: saves; stdin is a read stream
  apply summary_bind (Sflush.proRead_fast c (regsAt c) l0
    (by simp only [Sflush.proRead_input, GHolds, r1, r2, r8, r10, r11, r19]; exact ⟨h.raReg, sp0, s0r, a0, a1, s3r, trivial⟩)
    (by rw [r11]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by rw [r2, sp48]; exact frame_word (k := 48) (off := 32) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [r2, sp48]; exact frame_word (k := 48) (off := 8) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [r2, sp48]; exact frame_word (k := 48) (off := 40) frame (by decide) (by decide) (by decide) (by decide))
    (by simp only [Sflush.proReadLog, r1, r2, r8, r19]; exact saves)
    (by simp only [Sflush.proRead_loads, List.getD_cons_zero, r11, flags]; decide)) (fun _ p => p.pc)
  intro c1 p1
  have o1 := p1.regs
  simp only [Sflush.proRead_regs, Sflush.proRead_loads, r1, r2, r8, r10, r11, r19, flags, GHolds,
    List.getD_cons_zero] at o1
  obtain ⟨-, -, -, g2, g14, g1, g10, g11, -⟩ := o1
  have m1 : c1.σ.mem = writeLog c.σ.mem (flushSaves sp ra s0 s3) := by
    rw [p1.memory]; simp only [Sflush.proReadLog, r1, r2, r8, r19, flushSaves]
  have keepLow (a : Nat) (ha : a + 8 ≤ sp.toNat - 48) : read8 c1.σ.mem a = read8 c.σ.mem a := by
    rw [m1]
    exact ConsoleWrite.read8_same fun i hi => by
      rw [writeLog_out _ _ _ (show OutL (flushSaves sp ra s0 s3) (a + i) by
        simp only [flushSaves, OutL, nat 32 (by decide), nat 8 (by decide), nat 40 (by decide)]
        exact ⟨by omega, by omega, by omega, trivial⟩)]
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of g1]; exact ⟨p1.good, p1.image, p1.minstret, g1, h.aligned, p1.tick⟩
  -- `_flags |= 0x800`; `_r <= 0`
  apply summary_bind (Sflush.read_fast c1 (regsAt c1) l1
    (by simp only [Sflush.read_input, GHolds, regsAt_of g10, regsAt_of g11, regsAt_of g14]; exact ⟨g10, g11, g14, trivial⟩)
    (by rw [regsAt_of g11]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by rw [regsAt_of g11]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [Sflush.readLog, regsAt_of g11, regsAt_of g14]
        exact ⟨⟨Or.inl (by decide), trivial⟩, ⟨Or.inl (by decide), trivial⟩⟩)
    (by simp only [Sflush.read_loads, List.getD_cons_zero, regsAt_of g11]
        rw [keepLow _ (by rw [show (stdinFile + 8#64).toNat = 2147994176 by decide]; omega), r]; decide)) (fun _ p => p.pc)
  intro c2 p2
  have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [13, 15]) : gprGet c2.σ n = gprGet c1.σ n :=
    p2.gpr_frame (by decide) n lo hi out
  have m2 : c2.σ.mem = writeLog c.σ.mem (stdinFlushLog sp ra s0 s3) := by
    rw [p2.memory, m1, stdinFlushLog, writeLog_append]
    simp only [Sflush.readLog, regsAt_of g11, regsAt_of g14]
    rfl
  have h10 := (k2 10 (by decide) (by decide) (by decide)).trans g10
  have h11 := (k2 11 (by decide) (by decide) (by decide)).trans g11
  have h1 := (k2 1 (by decide) (by decide) (by decide)).trans g1
  have h2 := (k2 2 (by decide) (by decide) (by decide)).trans g2
  have l2 : LeafInput (regsAt c2 1) c2 := by
    rw [regsAt_of h1]; exact ⟨p2.good, p2.image, p2.minstret, h1, h.aligned, p2.tick⟩
  have urAt : read8 c2.σ.mem (stdinFile + 112#64).toNat = read8 c.σ.mem (stdinFile + 112#64).toNat := by
    rw [m2]
    have e : (stdinFile + 112#64).toNat = 2147994280 := by decide
    rw [e]
    exact ConsoleWrite.read8_same fun i hi => by
      rw [writeLog_out _ _ _ (show OutL (stdinFlushLog sp ra s0 s3) (2147994280 + i) by
        simp only [stdinFlushLog, flushSaves, List.cons_append, List.nil_append, OutL, nat 32 (by decide),
          nat 8 (by decide), nat 40 (by decide), show (stdinFile + 16#64).toNat = 2147994184 by decide]
        exact ⟨by omega, by omega, by omega, by omega, trivial⟩)]
  -- `_ur <= 0`
  apply summary_bind (Sflush.ur_fast c2 (regsAt c2) l2
    (by simp only [Sflush.ur_input, GHolds, regsAt_of h10, regsAt_of h11]; exact ⟨h10, h11, trivial⟩)
    (by rw [regsAt_of h11]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by simp only [Sflush.ur_loads, List.getD_cons_zero, regsAt_of h11]; rw [urAt, ur]; decide)) (fun _ p => p.pc)
  intro c3 p3
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [13]) : gprGet c3.σ n = gprGet c2.σ n :=
    p3.gpr_frame (by decide) n lo hi out
  have i1 := (k3 1 (by decide) (by decide) (by decide)).trans h1
  have i10 := (k3 10 (by decide) (by decide) (by decide)).trans h10
  have l3 : LeafInput (regsAt c3 1) c3 := by
    rw [regsAt_of i1]; exact ⟨p3.good, p3.image, p3.minstret, i1, h.aligned, p3.tick⟩
  apply summary_bind (Sflush.toEnd_fast c3 (regsAt c3) l3
    (by simp only [Sflush.toEnd_input, GHolds, regsAt_of i10]; exact ⟨i10, trivial⟩)) (fun _ p => p.pc)
  intro c4 p4
  have k4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c4.σ n = gprGet c3.σ n :=
    p4.gpr_frame (by decide) n lo hi (by simp)
  have j1 := (k4 1 (by decide) (by decide)).trans i1
  have j10 := (k4 10 (by decide) (by decide)).trans i10
  have j2 := (k4 2 (by decide) (by decide)).trans ((k3 2 (by decide) (by decide) (by decide)).trans h2)
  have l4 : LeafInput (regsAt c4 1) c4 := by
    rw [regsAt_of j1]; exact ⟨p4.good, p4.image, p4.minstret, j1, h.aligned, p4.tick⟩
  have m4 : c4.σ.mem = writeLog c.σ.mem (stdinFlushLog sp ra s0 s3) := by
    rw [p4.memory, Named.NamedValue.wl_nil, p3.memory, Named.NamedValue.wl_nil, m2]
  have later (off : Nat) (ho : off + 8 ≤ 48) (hs : off = 32 ∨ off = 8 ∨ off = 40) :
      OutLRange [((stdinFile + 16#64).toNat, 2, 0x804#64)] (sp - 48#64 + BitVec.ofNat 64 off).toNat 8 := by
    simp only [OutLRange, nat off (by omega), show (stdinFile + 16#64).toNat = 2147994184 by decide]
    exact ⟨Or.inr (by omega), trivial⟩
  have savedAt (k off : Nat) (v : BitVec 64) (sel : (stdinFlushLog sp ra s0 s3)[k]? =
      some ((sp - 48#64 + BitVec.ofNat 64 off).toNat, 8, v))
      (out : OutLRange ((stdinFlushLog sp ra s0 s3).drop (k + 1)) (sp - 48#64 + BitVec.ofNat 64 off).toNat 8) :
      bytesVal .ld (read8 c4.σ.mem (sp + 18446744073709551568#64 + BitVec.ofNat 64 off).toNat) = v := by
    rw [read8_value, m4, sp48]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ k _ _ sel out
  have raSaved := savedAt 2 40 ra rfl (later 40 (by decide) (by decide))
  have s0Saved := savedAt 0 32 s0 rfl (by
    simp only [stdinFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, OutLRange, nat 32 (by decide),
      nat 8 (by decide), nat 40 (by decide), show (stdinFile + 16#64).toNat = 2147994184 by decide]
    exact ⟨Or.inr (by omega), Or.inl (by omega), Or.inr (by omega), trivial⟩)
  have s3Saved := savedAt 1 8 s3 rfl (by
    simp only [stdinFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, OutLRange, nat 8 (by decide),
      nat 40 (by decide), show (stdinFile + 16#64).toNat = 2147994184 by decide]
    exact ⟨Or.inl (by omega), Or.inr (by omega), trivial⟩)
  -- epilogue
  apply (Sflush.leave_fast c4 ra (regsAt c4) l4
    (by simp only [Sflush.leave_input, GHolds, regsAt_of j2, regsAt_of j10]; exact ⟨j2, j10, trivial⟩)
    (by rw [regsAt_of j2, sp48]; exact (frame_word (k := 48) (off := 40) frame (by decide) (by decide) (by decide)
      (by decide)).read)
    (by rw [regsAt_of j2, sp48]; exact (frame_word (k := 48) (off := 32) frame (by decide) (by decide) (by decide)
      (by decide)).read)
    (by rw [regsAt_of j2, sp48]; exact (frame_word (k := 48) (off := 8) frame (by decide) (by decide) (by decide)
      (by decide)).read)
    (by rw [regsAt_of j2]; exact raSaved) h.aligned).weaken (fun _ e => e)
  intro d p5
  have o5 := p5.regs
  simp only [Sflush.leave_regs, Sflush.leave_loads, regsAt_of j2, List.getD_cons_zero, List.getD_cons_succ,
    GHolds] at o5
  have e := (((p1.toEffectPost.trans p2.toEffectPost).trans p3.toEffectPost).trans p4.toEffectPost).trans
    p5.toEffectPost
  have eff : WritePost ([2, 8, 14, 15, 19] ++ [13, 15] ++ [13] ++ [] ++ [1, 2, 8, 10, 19])
      (stdinFlushLog sp ra s0 s3) c ra 0#64 d :=
    { e with memory := by rw [p5.memory, Named.NamedValue.wl_nil, m4] }
  exact ⟨eff, by rw [o5.1, BitVec.add_assoc]; simp, by rw [o5.2.2.2.1, s0Saved], by rw [o5.2.2.1, s3Saved], trivial⟩

/-- **`__sflush_r`'s prologue on a write stream**: the three saves, `s0 = fp`,
`s3 = reent`, the flags in `a4`. -/
theorem flush_write_pro {ra sp s0 s3 reent fp fl : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s3r : gprGet c.σ 19 = some s3)
    (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some fp) (frame : NativeFrame sp 48)
    (flagsW : ReadWindow (fp + 16#64) 2) (flags : bytesVal .lh (read8 c.σ.mem (fp + 16#64).toNat) = fl)
    (writing : fl &&& 8#64 ≠ 0#64) :
    FnSummary 0x8003e4f4#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 14, 15, 19] (flushSaves sp ra s0 s3) c 0x8003e638#64 reent
        [(19, reent), (8, fp), (15, fl &&& 8#64), (2, sp + 18446744073709551568#64), (14, fl), (1, ra), (10, reent),
          (11, fp)]) := by
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have r8 := regsAt_of s0r
  have r19 := regsAt_of s3r
  have r10 := regsAt_of a0
  have r11 := regsAt_of a1
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have f32 := frame_outside (k := 48) (off := 32) (w := 8) (v := s0) frame (by decide) (by decide)
  have f8 := frame_outside (k := 48) (off := 8) (w := 8) (v := s3) frame (by decide) (by decide)
  have f40 := frame_outside (k := 48) (off := 40) (w := 8) (v := ra) frame (by decide) (by decide)
  apply (Sflush.proWrite_fast c (regsAt c) l0
    (by simp only [Sflush.proWrite_input, GHolds, r1, r2, r8, r10, r11, r19]; exact ⟨h.raReg, sp0, s0r, a0, a1, s3r, trivial⟩)
    (by rw [r11]; exact flagsW)
    (by rw [r2, sp48]; exact frame_word (k := 48) (off := 32) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [r2, sp48]; exact frame_word (k := 48) (off := 8) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [r2, sp48]; exact frame_word (k := 48) (off := 40) frame (by decide) (by decide) (by decide) (by decide))
    (by simp only [Sflush.proWriteLog, r1, r2, r8, r19]
        exact ⟨⟨f32.1.1, f8.1.1, f40.1.1, trivial⟩, ⟨f32.2.1, f8.2.1, f40.2.1, trivial⟩⟩)
    (by simp only [Sflush.proWrite_loads, List.getD_cons_zero, r11, flags, guardB]; simpa using writing)).weaken
    (fun _ e => e)
  intro d p
  have o := p.regs
  simp only [Sflush.proWrite_regs, Sflush.proWrite_loads, r1, r2, r8, r10, r11, r19, flags, GHolds,
    List.getD_cons_zero] at o
  have res : gpr d 10 = some reent := by have := p.result; rw [r10] at this; exact this
  have mem : d.σ.mem = writeLog c.σ.mem (flushSaves sp ra s0 s3) := by
    rw [p.memory]; simp only [Sflush.proWriteLog, r1, r2, r8, r19, flushSaves]
  have eff : WritePost [2, 8, 14, 15, 19] (flushSaves sp ra s0 s3) c 0x8003e638#64 reent d :=
    ⟨p.good, p.image, p.minstret, p.tick, p.pc, res, mem, p.output, p.frame, p.kept⟩
  exact ⟨eff, o⟩

/-- stdout's flush: the saves, then `s2`'s save. -/
def stdoutFlushLog (sp ra s0 s2 s3 : BitVec 64) : List WEntry :=
  flushSaves sp ra s0 s3 ++ [((sp + 18446744073709551568#64 + 16#64).toNat, 8, s2)]

/-- **`__sflush_r(reent, stdout)`**, stdout never written through stdio (no
buffer): returns 0. -/
theorem flush_stdout {ra sp s0 s2 s3 reent : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s2r : gprGet c.σ 18 = some s2)
    (s3r : gprGet c.σ 19 = some s3) (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some stdoutFile)
    (frame : NativeFrame sp 48)
    (flags : bytesVal .lh (read8 c.σ.mem (stdoutFile + 16#64).toNat) = 9#64)
    (base : bytesVal .ld (read8 c.σ.mem (stdoutFile + 24#64).toNat) = 0#64) :
    FnSummary 0x8003e4f4#64 (fun d => d = c)
      (WriteRegistersPost ([2, 8, 14, 15, 19] ++ [18] ++ [18] ++ [1, 2, 8, 10, 19]) (stdoutFlushLog sp ra s0 s2 s3) c ra
        0#64 [(2, sp), (8, s0), (18, s2), (19, s3)]) := by
  have lo := frame.lower
  have hiS := frame.upper
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo hiS
  have nat (off : Nat) (ho : off ≤ 48) : (sp - 48#64 + BitVec.ofNat 64 off).toNat = sp.toNat - 48 + off :=
    frame_nat (k := 48) frame (by decide) ho
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  apply summary_bind (flush_write_pro h sp0 s0r s3r a0 a1 frame ⟨by decide, by decide, Or.inr (by decide)⟩ flags
    (by decide)) (fun _ p => p.pc)
  intro c1 p1
  obtain ⟨-, -, -, g2, -, g1, g10, g11, -⟩ := p1.regs
  have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [2, 8, 14, 15, 19]) : gprGet c1.σ n = gprGet c.σ n :=
    p1.gpr_frame (by decide) n lo hi out
  have g18 := (k1 18 (by decide) (by decide) (by decide)).trans s2r
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of g1]; exact ⟨p1.good, p1.image, p1.minstret, g1, h.aligned, p1.tick⟩
  have keepLow (a : Nat) (ha : a + 8 ≤ sp.toNat - 48) : read8 c1.σ.mem a = read8 c.σ.mem a := by
    rw [p1.memory]
    exact ConsoleWrite.read8_same fun i hi => by
      rw [writeLog_out _ _ _ (show OutL (flushSaves sp ra s0 s3) (a + i) by
        simp only [flushSaves, OutL, nat 32 (by decide), nat 8 (by decide), nat 40 (by decide)]
        exact ⟨by omega, by omega, by omega, trivial⟩)]
  have slot16 : (sp + 18446744073709551568#64 + 16#64).toNat = sp.toNat - 32 := by
    rw [sp48, nat 16 (by decide)]; omega
  have w16 := frame_word (k := 48) (off := 16) frame (by decide) (by decide) (by decide) (by decide)
  -- save `s2`; no buffer
  apply summary_bind (Sflush.noBase_fast c1 (regsAt c1) l1
    (by simp only [Sflush.noBase_input, GHolds, regsAt_of g2, regsAt_of g10, regsAt_of g11, regsAt_of g18]
        exact ⟨g2, g10, g11, g18, trivial⟩)
    (by rw [regsAt_of g2, sp48]; exact w16)
    (by rw [regsAt_of g11]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by simp only [Sflush.noBaseLog, regsAt_of g2, regsAt_of g18, regsAt_of g11, List.take, OutLRange, slot16,
          show (stdoutFile + 24#64).toNat = 2147994376 by decide]
        exact ⟨Or.inl (by omega), trivial⟩)
    (by simp only [Sflush.noBaseLog, regsAt_of g2, regsAt_of g18]
        have f := frame_outside (k := 48) (off := 16) (w := 8) (v := s2) frame (by decide) (by decide)
        rw [sp48]; exact f)
    (by simp only [Sflush.noBase_loads, List.getD_cons_zero, regsAt_of g11]
        rw [keepLow _ (by rw [show (stdoutFile + 24#64).toNat = 2147994376 by decide]; omega), base]; decide))
    (fun _ p => p.pc)
  intro c2 p2
  have o2 := p2.regs
  simp only [Sflush.noBase_regs, Sflush.noBase_loads, regsAt_of g2, regsAt_of g10, regsAt_of g11, GHolds] at o2
  obtain ⟨-, h2, h10, -, -⟩ := o2
  have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [18]) : gprGet c2.σ n = gprGet c1.σ n :=
    p2.gpr_frame (by decide) n lo hi out
  have h1 := (k2 1 (by decide) (by decide) (by decide)).trans g1
  have m2 : c2.σ.mem = writeLog c.σ.mem (stdoutFlushLog sp ra s0 s2 s3) := by
    rw [p2.memory, p1.memory, stdoutFlushLog, writeLog_append]
    simp only [Sflush.noBaseLog, regsAt_of g2, regsAt_of g18]
  have l2 : LeafInput (regsAt c2 1) c2 := by
    rw [regsAt_of h1]; exact ⟨p2.good, p2.image, p2.minstret, h1, h.aligned, p2.tick⟩
  have s2Saved : bytesVal .ld (read8 c2.σ.mem (sp + 18446744073709551568#64 + 16#64).toNat) = s2 := by
    rw [read8_value, m2]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 3 _ _ rfl trivial
  -- restore `s2`, go to the epilogue
  apply summary_bind (Sflush.noBaseEnd_fast c2 (regsAt c2) l2
    (by simp only [Sflush.noBaseEnd_input, GHolds, regsAt_of h2, regsAt_of h10]; exact ⟨h2, h10, trivial⟩)
    (by rw [regsAt_of h2, sp48]; exact w16.read)) (fun _ p => p.pc)
  intro c3 p3
  have o3 := p3.regs
  simp only [Sflush.noBaseEnd_regs, Sflush.noBaseEnd_loads, regsAt_of h2, regsAt_of h10, GHolds,
    List.getD_cons_zero] at o3
  rw [s2Saved] at o3
  obtain ⟨i18, i2, i10, -⟩ := o3
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [18]) : gprGet c3.σ n = gprGet c2.σ n :=
    p3.gpr_frame (by decide) n lo hi out
  have i1 := (k3 1 (by decide) (by decide) (by decide)).trans h1
  have m3 : c3.σ.mem = writeLog c.σ.mem (stdoutFlushLog sp ra s0 s2 s3) := by
    rw [p3.memory, Named.NamedValue.wl_nil, m2]
  have saved (k off : Nat) (v : BitVec 64) (ho : off + 8 ≤ 48)
      (sel : (stdoutFlushLog sp ra s0 s2 s3)[k]? = some ((sp - 48#64 + BitVec.ofNat 64 off).toNat, 8, v))
      (out : OutLRange ((stdoutFlushLog sp ra s0 s2 s3).drop (k + 1)) (sp.toNat - 48 + off) 8) :
      bytesVal .ld (read8 c3.σ.mem (sp + 18446744073709551568#64 + BitVec.ofNat 64 off).toNat) = v := by
    rw [read8_value, m3, sp48]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ k _ _ sel (by rw [nat off (by omega)]; exact out)
  have stack (off : Nat) (ho : off ≤ 48) := nat off ho
  apply (flush_epilogue (ra := ra) (s0 := s0) (s3 := s3) ⟨p3.good, p3.image, p3.minstret, i1, h.aligned, p3.tick⟩
    i2 i10 frame
    (saved 2 40 ra (by decide) rfl (by
      simp only [stdoutFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, OutLRange, slot16]
      exact ⟨Or.inr (by omega), trivial⟩))
    h.aligned
    (saved 0 32 s0 (by decide) rfl (by
      simp only [stdoutFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, OutLRange, slot16,
        stack 8 (by decide), stack 40 (by decide)]
      exact ⟨Or.inr (by omega), Or.inl (by omega), Or.inr (by omega), trivial⟩))
    (saved 1 8 s3 (by decide) rfl (by
      simp only [stdoutFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, OutLRange, slot16,
        stack 40 (by decide)]
      exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩))).weaken (fun _ e => e)
  intro d p4
  have k4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 8, 10, 19]) : gprGet d.σ n = gprGet c3.σ n :=
    p4.gpr_frame (by decide) n lo hi out
  obtain ⟨d2, d8, d19, -⟩ := p4.regs
  have e := ((p1.toEffectPost.trans p2.toEffectPost).trans p3.toEffectPost).trans p4.toEffectPost
  have eff : WritePost ([2, 8, 14, 15, 19] ++ [18] ++ [18] ++ [1, 2, 8, 10, 19]) (stdoutFlushLog sp ra s0 s2 s3) c ra
      0#64 d :=
    ⟨e.good, e.image, e.minstret, e.tick, e.pc, e.result, by rw [p4.memory, Named.NamedValue.wl_nil, m3], e.output,
      e.frame, e.kept⟩
  exact ⟨eff, d2, d8, (k4 18 (by decide) (by decide) (by decide)).trans i18, d19, trivial⟩

/-- stderr's flush: the saves, `s2`'s and `s1`'s saves, `_p = _base`, `_w = 0`. -/
def stderrFlushLog (sp ra s0 s1 s2 s3 nb : BitVec 64) : List WEntry :=
  flushSaves sp ra s0 s3 ++ [((sp + 18446744073709551568#64 + 16#64).toNat, 8, s2)] ++
    [((sp + 18446744073709551568#64 + 24#64).toNat, 8, s1), (stderrFile.toNat, 8, nb)] ++
    [((stderrFile + 12#64).toNat, 4, 0#64)]

/-- **`__sflush_r(reent, stderr)`**, stderr unbuffered with nothing pending
(`_p = _base`): `_p` and `_w` reset, returns 0. -/
theorem flush_stderr {ra sp s0 s1 s2 s3 reent nb : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s1r : gprGet c.σ 9 = some s1)
    (s2r : gprGet c.σ 18 = some s2) (s3r : gprGet c.σ 19 = some s3) (a0 : gprGet c.σ 10 = some reent)
    (a1 : gprGet c.σ 11 = some stderrFile) (frame : NativeFrame sp 48)
    (flags : bytesVal .lh (read8 c.σ.mem (stderrFile + 16#64).toNat) = 0x201a#64)
    (base : bytesVal .ld (read8 c.σ.mem (stderrFile + 24#64).toNat) = nb) (nz : nb ≠ 0#64)
    (pos : bytesVal .ld (read8 c.σ.mem stderrFile.toNat) = nb) :
    FnSummary 0x8003e4f4#64 (fun d => d = c)
      (WriteRegistersPost ([2, 8, 14, 15, 19] ++ [18] ++ [9, 14, 15] ++ [] ++ [] ++ [9] ++ [18] ++ [1, 2, 8, 10, 19])
        (stderrFlushLog sp ra s0 s1 s2 s3 nb) c ra 0#64 [(2, sp), (8, s0), (9, s1), (18, s2), (19, s3)]) := by
  have lo := frame.lower
  have hiS := frame.upper
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo hiS
  have nat (off : Nat) (ho : off ≤ 48) : (sp - 48#64 + BitVec.ofNat 64 off).toNat = sp.toNat - 48 + off :=
    frame_nat (k := 48) frame (by decide) ho
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have slot (off : Nat) (ho : off ≤ 48) : (sp + 18446744073709551568#64 + BitVec.ofNat 64 off).toNat =
      sp.toNat - 48 + off := by rw [sp48, nat off ho]
  have fpN : stderrFile.toNat = 2147994536 := by decide
  have fp12 : (stderrFile + 12#64).toNat = 2147994548 := by decide
  have fp24 : (stderrFile + 24#64).toNat = 2147994560 := by decide
  have w16 := frame_word (k := 48) (off := 16) frame (by decide) (by decide) (by decide) (by decide)
  have w24 := frame_word (k := 48) (off := 24) frame (by decide) (by decide) (by decide) (by decide)
  apply summary_bind (flush_write_pro h sp0 s0r s3r a0 a1 frame ⟨by decide, by decide, Or.inr (by decide)⟩ flags
    (by decide)) (fun _ p => p.pc)
  intro c1 p1
  obtain ⟨-, g8, -, g2, g14, g1, g10, g11, -⟩ := p1.regs
  have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [2, 8, 14, 15, 19]) : gprGet c1.σ n = gprGet c.σ n :=
    p1.gpr_frame (by decide) n lo hi out
  have g18 := (k1 18 (by decide) (by decide) (by decide)).trans s2r
  have g9 := (k1 9 (by decide) (by decide) (by decide)).trans s1r
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of g1]; exact ⟨p1.good, p1.image, p1.minstret, g1, h.aligned, p1.tick⟩
  have saveOut (a : Nat) (ha : a + 8 ≤ sp.toNat - 48) :
      OutL (flushSaves sp ra s0 s3 ++ [((sp + 18446744073709551568#64 + 16#64).toNat, 8, s2)]) a := by
    simp only [flushSaves, List.cons_append, List.nil_append, OutL, nat 32 (by decide), nat 8 (by decide),
      nat 40 (by decide), slot 16 (by decide)]
    exact ⟨by omega, by omega, by omega, by omega, trivial⟩
  -- save `s2`; a buffer
  apply summary_bind (Sflush.base_fast c1 (regsAt c1) l1
    (by simp only [Sflush.base_input, GHolds, regsAt_of g2, regsAt_of g10, regsAt_of g11, regsAt_of g18]
        exact ⟨g2, g10, g11, g18, trivial⟩)
    (by rw [regsAt_of g2, sp48]; exact w16)
    (by rw [regsAt_of g11]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by simp only [Sflush.baseLog, regsAt_of g2, regsAt_of g18, regsAt_of g11, List.take, OutLRange, slot 16 (by decide),
          fp24]
        exact ⟨Or.inl (by omega), trivial⟩)
    (by simp only [Sflush.baseLog, regsAt_of g2, regsAt_of g18]
        have f := frame_outside (k := 48) (off := 16) (w := 8) (v := s2) frame (by decide) (by decide)
        rw [sp48]; exact f)
    (by simp only [Sflush.base_loads, List.getD_cons_zero, regsAt_of g11]
        rw [p1.memory, ConsoleWrite.read8_same (m := c.σ.mem) fun i hi => by
          rw [writeLog_out _ _ _ (show OutL (flushSaves sp ra s0 s3) ((stderrFile + 24#64).toNat + i) by
            simp only [flushSaves, OutL, nat 32 (by decide), nat 8 (by decide), nat 40 (by decide), fp24]
            exact ⟨by omega, by omega, by omega, trivial⟩)], base]
        simp only [guardB]; simpa using nz)) (fun _ p => p.pc)
  intro c2 p2
  have o2 := p2.regs
  simp only [Sflush.base_regs, Sflush.base_loads, regsAt_of g2, regsAt_of g10, regsAt_of g11, GHolds] at o2
  obtain ⟨-, h2, h10, h11, -⟩ := o2
  have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [18]) : gprGet c2.σ n = gprGet c1.σ n :=
    p2.gpr_frame (by decide) n lo hi out
  have h1 := (k2 1 (by decide) (by decide) (by decide)).trans g1
  have h9 := (k2 9 (by decide) (by decide) (by decide)).trans g9
  have h14 := (k2 14 (by decide) (by decide) (by decide)).trans g14
  have h8 := (k2 8 (by decide) (by decide) (by decide)).trans g8
  have m2 : c2.σ.mem = writeLog c.σ.mem (flushSaves sp ra s0 s3 ++ [((sp + 18446744073709551568#64 + 16#64).toNat, 8, s2)]) := by
    rw [p2.memory, p1.memory, writeLog_append]
    simp only [Sflush.baseLog, regsAt_of g2, regsAt_of g18]
  -- `_base` from the load (the `ld` pins it), then `s2` reloads it below
  have b18 : gprGet c2.σ 18 = some nb := by
    have := gholds_lookup (n := 18) _ p2.regs rfl
    rw [this]; simp only [Sflush.base_loads, List.getD_cons_zero, regsAt_of g11]
    rw [p1.memory, ConsoleWrite.read8_same (m := c.σ.mem) fun i hi => by
      rw [writeLog_out _ _ _ (show OutL (flushSaves sp ra s0 s3) ((stderrFile + 24#64).toNat + i) by
        simp only [flushSaves, OutL, nat 32 (by decide), nat 8 (by decide), nat 40 (by decide), fp24]
        exact ⟨by omega, by omega, by omega, trivial⟩)], base]
  have l2 : LeafInput (regsAt c2 1) c2 := by
    rw [regsAt_of h1]; exact ⟨p2.good, p2.image, p2.minstret, h1, h.aligned, p2.tick⟩
  have posAt : read8 c2.σ.mem stderrFile.toNat = read8 c.σ.mem stderrFile.toNat := by
    rw [m2]; exact ConsoleWrite.read8_same fun i hi => by rw [writeLog_out _ _ _ (saveOut _ (by omega))]
  -- save `s1`; `_p = _base`; unbuffered
  apply summary_bind (Sflush.unbuf_fast c2 (regsAt c2) l2
    (by simp only [Sflush.unbuf_input, GHolds, regsAt_of h2, regsAt_of h9, regsAt_of h10, regsAt_of h11, regsAt_of h14,
          regsAt_of b18]
        exact ⟨h2, h9, h10, h11, h14, b18, trivial⟩)
    (by rw [regsAt_of h2, sp48]; exact w24)
    (by rw [regsAt_of h11]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by simp only [Sflush.unbufLog, regsAt_of h2, regsAt_of h9, regsAt_of h11, regsAt_of b18, List.take, OutLRange,
          slot 24 (by decide), fpN]
        exact ⟨Or.inl (by omega), trivial⟩)
    (by rw [regsAt_of h11]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [Sflush.unbufLog, regsAt_of h2, regsAt_of h9, regsAt_of h11, regsAt_of b18]
        have f := frame_outside (k := 48) (off := 24) (w := 8) (v := s1) frame (by decide) (by decide)
        rw [sp48]
        exact ⟨⟨f.1.1, Or.inl (by show Image.textBase + Image.textSize ≤ stderrFile.toNat; rw [fpN]; decide), trivial⟩,
          ⟨f.2.1, Or.inl (by show Image.rodataBase + Image.rodataSize ≤ stderrFile.toNat; rw [fpN]; decide), trivial⟩⟩)
    (by rw [regsAt_of h14]; decide)) (fun _ p => p.pc)
  intro c3 p3
  have o3 := p3.regs
  simp only [Sflush.unbuf_regs, Sflush.unbuf_loads, regsAt_of h2, regsAt_of h9, regsAt_of h10, regsAt_of h11,
    regsAt_of h14, regsAt_of b18, GHolds, List.getD_cons_zero, posAt, pos] at o3
  obtain ⟨i15, i9, -, i2, i10, -, -, -⟩ := o3
  rw [show BitVec.signExtend 64 (Sail.BitVec.extractLsb nb 31 0 + -Sail.BitVec.extractLsb nb 31 0) = 0#64 by
    rw [← BitVec.sub_eq_add_neg, BitVec.sub_self]; decide] at i9
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [9, 14, 15]) : gprGet c3.σ n = gprGet c2.σ n :=
    p3.gpr_frame (by decide) n lo hi out
  have i1 := (k3 1 (by decide) (by decide) (by decide)).trans h1
  have i8 := (k3 8 (by decide) (by decide) (by decide)).trans h8
  have l3 : LeafInput (regsAt c3 1) c3 := by
    rw [regsAt_of i1]; exact ⟨p3.good, p3.image, p3.minstret, i1, h.aligned, p3.tick⟩
  -- `_w = 0`; nothing pending
  apply summary_bind (Sflush.w_fast c3 (regsAt c3) l3
    (by simp only [Sflush.w_input, GHolds, regsAt_of i8, regsAt_of i9, regsAt_of i10, regsAt_of i15]
        exact ⟨i8, i9, i10, i15, trivial⟩)
    (by rw [regsAt_of i8]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [Sflush.wLog, regsAt_of i8, regsAt_of i15]
        exact ⟨⟨Or.inl (by rw [fp12]; decide), trivial⟩, ⟨Or.inl (by rw [fp12]; decide), trivial⟩⟩)
    (by rw [regsAt_of i9]; decide)) (fun _ p => p.pc)
  intro c4 p4
  have k4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c4.σ n = gprGet c3.σ n :=
    p4.gpr_frame (by decide) n lo hi (by simp)
  have j1 := (k4 1 (by decide) (by decide)).trans i1
  have j10 := (k4 10 (by decide) (by decide)).trans i10
  have j2 := (k4 2 (by decide) (by decide)).trans i2
  have m4 : c4.σ.mem = writeLog c.σ.mem (stderrFlushLog sp ra s0 s1 s2 s3 nb) := by
    rw [p4.memory, p3.memory, m2]
    simp only [stderrFlushLog, writeLog_append, Sflush.unbufLog, Sflush.wLog, regsAt_of h2, regsAt_of h9,
      regsAt_of h11, regsAt_of b18, regsAt_of i8, regsAt_of i15]
  have l4 : LeafInput (regsAt c4 1) c4 := by
    rw [regsAt_of j1]; exact ⟨p4.good, p4.image, p4.minstret, j1, h.aligned, p4.tick⟩
  apply summary_bind (Sflush.toDone_fast c4 (regsAt c4) l4
    (by simp only [Sflush.toDone_input, GHolds, regsAt_of j10]; exact ⟨j10, trivial⟩)) (fun _ p => p.pc)
  intro c5 p5
  have k5 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c5.σ n = gprGet c4.σ n :=
    p5.gpr_frame (by decide) n lo hi (by simp)
  have q1 := (k5 1 (by decide) (by decide)).trans j1
  have q2 := (k5 2 (by decide) (by decide)).trans j2
  have q10 := (k5 10 (by decide) (by decide)).trans j10
  have m5 : c5.σ.mem = writeLog c.σ.mem (stderrFlushLog sp ra s0 s1 s2 s3 nb) := by
    rw [p5.memory, Named.NamedValue.wl_nil, m4]
  have later (off : Nat) (ho : off + 8 ≤ 48) (hs : off = 32 ∨ off = 8 ∨ off = 40 ∨ off = 16 ∨ off = 24) :
      OutLRange [(stderrFile.toNat, 8, nb), ((stderrFile + 12#64).toNat, 4, 0#64)] (sp.toNat - 48 + off) 8 := by
    simp only [OutLRange, fpN, fp12]; exact ⟨Or.inr (by omega), Or.inr (by omega), trivial⟩
  have saved (k off : Nat) (v : BitVec 64) (ho : off + 8 ≤ 48) (c' : Config)
      (mem : c'.σ.mem = writeLog c.σ.mem (stderrFlushLog sp ra s0 s1 s2 s3 nb))
      (sel : (stderrFlushLog sp ra s0 s1 s2 s3 nb)[k]? =
        some ((sp + 18446744073709551568#64 + BitVec.ofNat 64 off).toNat, 8, v))
      (out : OutLRange ((stderrFlushLog sp ra s0 s1 s2 s3 nb).drop (k + 1)) (sp.toNat - 48 + off) 8) :
      bytesVal .ld (read8 c'.σ.mem (sp + 18446744073709551568#64 + BitVec.ofNat 64 off).toNat) = v := by
    rw [read8_value, mem]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ k _ _ sel (by rw [slot off (by omega)]; exact out)
  have l5 : LeafInput (regsAt c5 1) c5 := by
    rw [regsAt_of q1]; exact ⟨p5.good, p5.image, p5.minstret, q1, h.aligned, p5.tick⟩
  -- reload `s1`, then `s2`
  apply summary_bind (Sflush.done_fast c5 (regsAt c5) l5
    (by simp only [Sflush.done_input, GHolds, regsAt_of q2, regsAt_of q10]; exact ⟨q2, q10, trivial⟩)
    (by rw [regsAt_of q2, sp48]; exact w24.read)) (fun _ p => p.pc)
  intro c6 p6
  have o6 := p6.regs
  simp only [Sflush.done_regs, Sflush.done_loads, regsAt_of q2, regsAt_of q10, GHolds, List.getD_cons_zero] at o6
  obtain ⟨r9, r2, r10, -⟩ := o6
  rw [saved 4 24 s1 (by decide) c5 m5 (by simp [stderrFlushLog, flushSaves, sp48]) (by
    simp only [stderrFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, List.append_assoc]
    exact later 24 (by decide) (by decide))] at r9
  have k6 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [9]) : gprGet c6.σ n = gprGet c5.σ n :=
    p6.gpr_frame (by decide) n lo hi out
  have r1 := (k6 1 (by decide) (by decide) (by decide)).trans q1
  have m6 : c6.σ.mem = writeLog c.σ.mem (stderrFlushLog sp ra s0 s1 s2 s3 nb) := by
    rw [p6.memory, Named.NamedValue.wl_nil, m5]
  have l6 : LeafInput (regsAt c6 1) c6 := by
    rw [regsAt_of r1]; exact ⟨p6.good, p6.image, p6.minstret, r1, h.aligned, p6.tick⟩
  apply summary_bind (Sflush.noBaseEnd_fast c6 (regsAt c6) l6
    (by simp only [Sflush.noBaseEnd_input, GHolds, regsAt_of r2, regsAt_of r10]; exact ⟨r2, r10, trivial⟩)
    (by rw [regsAt_of r2, sp48]; exact w16.read)) (fun _ p => p.pc)
  intro c7 p7
  have o7 := p7.regs
  simp only [Sflush.noBaseEnd_regs, Sflush.noBaseEnd_loads, regsAt_of r2, regsAt_of r10, GHolds,
    List.getD_cons_zero] at o7
  obtain ⟨t18, t2, t10, -⟩ := o7
  rw [saved 3 16 s2 (by decide) c6 m6 (by simp [stderrFlushLog, flushSaves, sp48]) (by
    simp only [stderrFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, List.append_assoc, OutLRange,
      slot 24 (by decide), fpN, fp12]
    exact ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩)] at t18
  have k7 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [18]) : gprGet c7.σ n = gprGet c6.σ n :=
    p7.gpr_frame (by decide) n lo hi out
  have t1 := (k7 1 (by decide) (by decide) (by decide)).trans r1
  have m7 : c7.σ.mem = writeLog c.σ.mem (stderrFlushLog sp ra s0 s1 s2 s3 nb) := by
    rw [p7.memory, Named.NamedValue.wl_nil, m6]
  apply (flush_epilogue (ra := ra) (s0 := s0) (s3 := s3) ⟨p7.good, p7.image, p7.minstret, t1, h.aligned, p7.tick⟩
    t2 t10 frame
    (saved 2 40 ra (by decide) c7 m7 (by simp [stderrFlushLog, flushSaves, sp48]) (by
      simp only [stderrFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, List.append_assoc, OutLRange,
        slot 16 (by decide), slot 24 (by decide), fpN, fp12]
      exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩))
    h.aligned
    (saved 0 32 s0 (by decide) c7 m7 (by simp [stderrFlushLog, flushSaves, sp48]) (by
      simp only [stderrFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, List.append_assoc, OutLRange,
        nat 8 (by decide), nat 40 (by decide), slot 16 (by decide), slot 24 (by decide), fpN, fp12]
      exact ⟨Or.inr (by omega), Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
        Or.inr (by omega), trivial⟩))
    (saved 1 8 s3 (by decide) c7 m7 (by simp [stderrFlushLog, flushSaves, sp48]) (by
      simp only [stderrFlushLog, flushSaves, List.drop, List.cons_append, List.nil_append, List.append_assoc, OutLRange,
        nat 40 (by decide), slot 16 (by decide), slot 24 (by decide), fpN, fp12]
      exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inr (by omega), Or.inr (by omega),
        trivial⟩))).weaken (fun _ e => e)
  intro d p8
  have k8 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 8, 10, 19]) : gprGet d.σ n = gprGet c7.σ n :=
    p8.gpr_frame (by decide) n lo hi out
  obtain ⟨d2, d8, d19, -⟩ := p8.regs
  have e := ((((((p1.toEffectPost.trans p2.toEffectPost).trans p3.toEffectPost).trans p4.toEffectPost).trans
    p5.toEffectPost).trans p6.toEffectPost).trans p7.toEffectPost).trans p8.toEffectPost
  have eff : WritePost ([2, 8, 14, 15, 19] ++ [18] ++ [9, 14, 15] ++ [] ++ [] ++ [9] ++ [18] ++ [1, 2, 8, 10, 19])
      (stderrFlushLog sp ra s0 s1 s2 s3 nb) c ra 0#64 d :=
    ⟨e.good, e.image, e.minstret, e.tick, e.pc, e.result, by rw [p8.memory, Named.NamedValue.wl_nil, m7], e.output,
      e.frame, e.kept⟩
  exact ⟨eff, d2, d8, (k8 9 (by decide) (by decide) (by decide)).trans ((k7 9 (by decide) (by decide) (by decide)).trans r9),
    (k8 18 (by decide) (by decide) (by decide)).trans t18, d19, trivial⟩

end OCaml.Vm.Primitives.Uncaught.StdioFlush
