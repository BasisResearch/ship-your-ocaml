import OCaml.Vm.Primitives.Uncaught.StdioFlush

/-!
# A returned stdio call, as a frame

The stdio calls of `exit`'s handler (`__sflush_r`, `__sclose`, `_fclose_r`,
`_fwalk_sglue`) are summarized exactly (a write log); what their callers use
is coarser: the call returned to `ra` with `0`, kept `sp` and the
callee-saved registers, printed nothing, and changed no byte of a given set
(`Returned`). `Returned.of_post` reads it off an exact post.
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioReturned
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Named.NamedValue (gprReg_ne_htif)

/-- `sp` and the callee-saved registers `s0`–`s11`. -/
def CalleeKept (k : Nat) : Prop := k = 2 ∨ k = 8 ∨ k = 9 ∨ (18 ≤ k ∧ k ≤ 27)

/-- **A returned call**: back at `ra` with `a0 = 0`; `sp`, the callee-saved
registers and the console as at the call; no byte of `keep` changed. -/
structure Returned (ra : BitVec 64) (keep : Nat → Prop) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : pcOf d = some ra
  result : gprGet d.σ 10 = some 0#64
  saved : ∀ k, CalleeKept k → gprGet d.σ k = gprGet c.σ k
  output : d.σ.sailOutput = c.σ.sailOutput
  htif : d.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes
  gprs : GprsKept c d
  kept : ∀ a, keep a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

/-- Read a `Returned` off an exact post: the saved registers from the post's
register list and frame, the kept bytes from a log that misses them. -/
theorem Returned.of_post {writes : List Nat} {log : List WEntry} {ra : BitVec 64} {regs : GRegs}
    {keep : Nat → Prop} {c d : Config} (p : WriteRegistersPost writes log c ra 0#64 regs d)
    (saved : ∀ k, CalleeKept k → gprGet d.σ k = gprGet c.σ k) (out : ∀ a, keep a → OutL log a) :
    Returned ra keep c d where
  good := p.good
  image := p.image
  minstret := p.minstret
  tick := p.tick
  pc := p.pc
  result := p.result
  saved := saved
  output := p.output
  htif := p.frame _ (fun n _ => gprReg_ne_htif n) (by decide)
  gprs := p.kept
  kept a ha := by rw [p.memory, writeLog_out _ _ _ (out a ha)]

/-- Weaken the kept set. -/
theorem Returned.mono {ra : BitVec 64} {keep keep' : Nat → Prop} {c d : Config} (h : Returned ra keep c d)
    (sub : ∀ a, keep' a → keep a) : Returned ra keep' c d :=
  { h with kept := fun a ha => h.kept a (sub a ha) }

open OCaml.Vm.Boot.Startup (NativeFrame)
open OCaml.Vm.Primitives.Uncaught.StdioFlush
open OCaml.Vm.Primitives.Uncaught.StdioClose (frame_nat fdSlot fdSlot_toNat FdLive sclose_console scloseLog closeLog)

/-- Bytes a flush of `fp` leaves alone: outside its 48-byte frame below `sp`
and outside the `FILE`'s first 24 bytes. -/
def FlushKeep (sp fp : BitVec 64) (a : Nat) : Prop :=
  (a < sp.toNat - 48 ∨ sp.toNat ≤ a) ∧ (a < fp.toNat ∨ fp.toNat + 24 ≤ a)

theorem flushSaves_out {sp ra s0 s3 fp : BitVec 64} (frame : NativeFrame sp 48) {a : Nat} (h : FlushKeep sp fp a) :
    OutL (flushSaves sp ra s0 s3) a := by
  have n (off : Nat) (ho : off ≤ 48) := frame_nat (k := 48) (off := off) frame (by decide) ho
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  simp only [flushSaves, OutL, n 32 (by decide), n 8 (by decide), n 40 (by decide)]
  rcases h.1 with h | h <;> exact ⟨by omega, by omega, by omega, trivial⟩

/-- `flush_stdin` as a returned call. -/
theorem flush_stdin_returned {ra sp s0 s3 reent : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s3r : gprGet c.σ 19 = some s3)
    (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some stdinFile) (frame : NativeFrame sp 48)
    (flags : bytesVal .lh (read8 c.σ.mem (stdinFile + 16#64).toNat) = 4#64)
    (r : bytesVal .lw (read8 c.σ.mem (stdinFile + 8#64).toNat) = 0#64)
    (ur : bytesVal .lw (read8 c.σ.mem (stdinFile + 112#64).toNat) = 0#64) :
    FnSummary 0x8003e4f4#64 (fun d => d = c) (Returned ra (FlushKeep sp stdinFile) c) := by
  apply (flush_stdin h sp0 s0r s3r a0 a1 frame flags r ur).weaken (fun _ e => e)
  intro d p
  obtain ⟨d2, d8, d19, -⟩ := p.regs
  refine Returned.of_post p (fun k hk => ?_) (fun a ha => ?_)
  · rcases hk with rfl | rfl | rfl | ⟨lo, hi⟩
    · rw [d2, sp0]
    · rw [d8, s0r]
    · exact p.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)
    · by_cases e19 : k = 19
      · subst e19; rw [d19, s3r]
      · exact p.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)
  · have fo := flushSaves_out (ra := ra) (s0 := s0) (s3 := s3) frame ha
    simp only [stdinFlushLog, List.cons_append, List.nil_append, flushSaves, OutL] at fo ⊢
    refine ⟨fo.1, fo.2.1, fo.2.2.1, ?_, trivial⟩
    have := ha.2
    rw [show (stdinFile + 16#64).toNat = stdinFile.toNat + 16 by decide]
    omega

/-- `flush_stdout` as a returned call. -/
theorem flush_stdout_returned {ra sp s0 s2 s3 reent : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s2r : gprGet c.σ 18 = some s2)
    (s3r : gprGet c.σ 19 = some s3) (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some stdoutFile)
    (frame : NativeFrame sp 48)
    (flags : bytesVal .lh (read8 c.σ.mem (stdoutFile + 16#64).toNat) = 9#64)
    (base : bytesVal .ld (read8 c.σ.mem (stdoutFile + 24#64).toNat) = 0#64) :
    FnSummary 0x8003e4f4#64 (fun d => d = c) (Returned ra (FlushKeep sp stdoutFile) c) := by
  apply (flush_stdout h sp0 s0r s2r s3r a0 a1 frame flags base).weaken (fun _ e => e)
  intro d p
  obtain ⟨d2, d8, d18, d19, -⟩ := p.regs
  have n16 := frame_nat (k := 48) (off := 16) frame (by decide) (by decide)
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  refine Returned.of_post p (fun k hk => ?_) (fun a ha => ?_)
  · rcases hk with rfl | rfl | rfl | ⟨lo, hi⟩
    · rw [d2, sp0]
    · rw [d8, s0r]
    · exact p.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)
    · by_cases e19 : k = 19
      · subst e19; rw [d19, s3r]
      · by_cases e18 : k = 18
        · subst e18; rw [d18, s2r]
        · exact p.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)
  · have fo := flushSaves_out (ra := ra) (s0 := s0) (s3 := s3) frame ha
    simp only [stdoutFlushLog, List.cons_append, List.nil_append, flushSaves, OutL, sp48, n16] at fo ⊢
    refine ⟨fo.1, fo.2.1, fo.2.2.1, ?_, trivial⟩
    rcases ha.1 with h | h <;> omega

/-- `flush_stderr` as a returned call. -/
theorem flush_stderr_returned {ra sp s0 s1 s2 s3 reent nb : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s1r : gprGet c.σ 9 = some s1)
    (s2r : gprGet c.σ 18 = some s2) (s3r : gprGet c.σ 19 = some s3) (a0 : gprGet c.σ 10 = some reent)
    (a1 : gprGet c.σ 11 = some stderrFile) (frame : NativeFrame sp 48)
    (flags : bytesVal .lh (read8 c.σ.mem (stderrFile + 16#64).toNat) = 0x201a#64)
    (base : bytesVal .ld (read8 c.σ.mem (stderrFile + 24#64).toNat) = nb) (nz : nb ≠ 0#64)
    (pos : bytesVal .ld (read8 c.σ.mem stderrFile.toNat) = nb) :
    FnSummary 0x8003e4f4#64 (fun d => d = c) (Returned ra (FlushKeep sp stderrFile) c) := by
  apply (flush_stderr h sp0 s0r s1r s2r s3r a0 a1 frame flags base nz pos).weaken (fun _ e => e)
  intro d p
  obtain ⟨d2, d8, d9, d18, d19, -⟩ := p.regs
  have n16 := frame_nat (k := 48) (off := 16) frame (by decide) (by decide)
  have n24 := frame_nat (k := 48) (off := 24) frame (by decide) (by decide)
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  refine Returned.of_post p (fun k hk => ?_) (fun a ha => ?_)
  · rcases hk with rfl | rfl | rfl | ⟨lo, hi⟩
    · rw [d2, sp0]
    · rw [d8, s0r]
    · rw [d9, s1r]
    · by_cases e19 : k = 19
      · subst e19; rw [d19, s3r]
      · by_cases e18 : k = 18
        · subst e18; rw [d18, s2r]
        · exact p.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)
  · have fo := flushSaves_out (ra := ra) (s0 := s0) (s3 := s3) frame ha
    simp only [stderrFlushLog, List.cons_append, List.nil_append, List.append_assoc, flushSaves, OutL, sp48, n16, n24,
      show (stderrFile + 12#64).toNat = stderrFile.toNat + 12 by decide] at fo ⊢
    refine ⟨fo.1, fo.2.1, fo.2.2.1, ?_, ?_, ?_, ?_, trivial⟩ <;> rcases ha with ⟨h1 | h1, h2 | h2⟩ <;> omega

/-- Bytes a close of descriptor `fd` leaves alone: outside its 48 bytes of
frames below `sp`, `errno`, and the descriptor's slot. -/
def CloseKeep (sp fd : BitVec 64) (a : Nat) : Prop :=
  (a < sp.toNat - 48 ∨ sp.toNat ≤ a) ∧ (a < 0x80064d48 ∨ 0x80064d48 + 4 ≤ a) ∧
    (a < (fdSlot fd).toNat ∨ (fdSlot fd).toNat + 4 ≤ a)

/-- `sclose_console` as a returned call. -/
theorem sclose_returned {ra sp s0 reent fp : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (a0 : gprGet c.σ 10 = some reent)
    (a1 : gprGet c.σ 11 = some fp) (frame : NativeFrame sp 48) (fileR : ReadWindow (fp + 18#64) 2)
    (fdOk : FdLive c.σ.mem (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) :
    FnSummary 0x80040184#64 (fun d => d = c)
      (Returned ra (CloseKeep sp (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) c) := by
  generalize hfd : bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat) = fd at fdOk ⊢
  have S := sclose_console h sp0 s0r a0 a1 frame fileR (by rw [hfd]; exact fdOk)
  rw [hfd] at S
  apply S.weaken (fun _ e => e)
  intro d p
  obtain ⟨d2, d8, -⟩ := p.regs
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have n0 : (sp - 16#64).toNat = sp.toNat - 16 := by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have n8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by rw [BitVec.toNat_add, n0, BitVec.toNat_ofNat]; omega
  have n24 : ((sp + 18446744073709551600#64) - 32#64 + 24#64).toNat = sp.toNat - 24 := by
    rw [show sp + 18446744073709551600#64 = sp - 16#64 by rw [BitVec.sub_eq_add_neg]; rfl, BitVec.toNat_add,
      BitVec.toNat_sub, n0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  refine Returned.of_post p (fun k hk => ?_) (fun a ha => ?_)
  · rcases hk with rfl | rfl | rfl | ⟨lo, hi⟩
    · rw [d2, sp0]
    · rw [d8, s0r]
    · exact p.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)
    · exact p.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)
  · obtain ⟨hs, he, hf⟩ := ha
    simp only [scloseLog, closeLog, List.cons_append, List.nil_append, OutL, n0, n8, n24, BitVec.toNat_ofNat]
    refine ⟨by omega, by omega, by omega, by omega, hf, trivial⟩

end OCaml.Vm.Primitives.Uncaught.StdioReturned
