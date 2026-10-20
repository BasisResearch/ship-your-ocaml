import OCaml.Vm.Primitives.Uncaught.StdioFclose
import OCaml.Vm.Primitives.Uncaught.FwalkSglue
import OCaml.Vm.Primitives.Uncaught.StdioExitHandler

/-!
# `_fwalk_sglue` closing the standard streams

`_fwalk_sglue(reent, _fclose_r, &__sglue)` walks the glue's `FILE`s and
calls `_fclose_r` on each live one (`_flags > 1`, `_file != -1`), or-ing the
results into `s6`. Its loop state is a `StdioFrame.Frame` pinning `sp`, the
current stream `s0`, the end `s1`, the glue `s2`, the constants `s3 = -1`,
`s7 = 1`, the arguments `s4`, `s5` and the result `s6` (`walkPins`); the
bytes kept shrink by each closed stream's footprint (`Done`). One visit is
`fwalk_visit`.
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioWalk
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives VsaIris.Inst
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif)
open OCaml.Vm.Boot.Startup (NativeFrame)
open OCaml.Vm.Primitives.ExitPath (KeepCtx ExitOk exitReads)
open OCaml.Vm.Primitives.Uncaught.StdioReturned
open OCaml.Vm.Primitives.Uncaught.StdioFrame (Frame)
open OCaml.Vm.Primitives.Uncaught.StdioClose (fdSlot fdSlot_toNat FdLive frame_nat frame_word frame_callee)
open OCaml.Vm.Primitives.Uncaught.StdioFclose

/-- `lhu` and `lh` agree on a halfword below `0x8000`. -/
theorem ext_small (x : BitVec 16) (small : (x.signExtend 64).toNat < 0x8000) :
    x.zeroExtend 64 = x.signExtend 64 := by
  have msb : x.msb = false := by
    cases hm : x.msb
    · rfl
    · exfalso
      have b15 : (x.signExtend 64).getLsbD 15 = true := by
        rw [BitVec.getLsbD_signExtend]
        simp only [show (15 < 64) = True by decide, decide_true, Bool.true_and, show (15 < 16) = True by decide,
          ite_true]
        rw [← hm, BitVec.msb_eq_getLsbD_last]
      have := Nat.ge_two_pow_of_testBit b15
      omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb, BitVec.zeroExtend_eq_setWidth]

theorem lhu_of_lh (bs : List (BitVec 8)) (small : (bytesVal .lh bs).toNat < 0x8000) :
    bytesVal .lhu bs = bytesVal .lh bs := by
  simp only [bytesVal, Functions.sign_extend, zero_extend, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend] at small ⊢
  exact ext_small _ small

/-- A flush premise moves along a stretch that kept `_fclose_r`'s outside. -/
theorem FlushCall.transport {c c' : Config} {sp fp reent : BitVec 64} (h : FlushCall c sp fp reent)
    (k : KeepCtx (Out32 sp) c c') : FlushCall c' sp fp reent :=
  fun c1 l ok r2 r8 r9 r10 r11 ctx => h c1 l ok r2 r8 r9 r10 r11 (k.trans ctx)

/-- The walk's pinned registers. -/
def walkPins (spw reent g fp e acc : BitVec 64) : GRegs :=
  [(2, spw), (8, fp), (9, e), (18, g), (19, 18446744073709551615#64), (20, reent), (21, 0x8004ce68#64),
    (22, acc), (23, 1#64)]

theorem walkPins_keys (spw reent g fp e acc : BitVec 64) :
    keysG (walkPins spw reent g fp e acc) = [2, 8, 9, 18, 19, 20, 21, 22, 23] := rfl

/-- `s8`–`s11`, held. -/
abbrev WalkHold (k : Nat) : Prop := 24 ≤ k ∧ k ≤ 27

/-- Bytes kept by the walk once the streams `ds` (with descriptors) are
closed: outside the callee's 80 bytes below `spw`, `errno`, and each closed
stream's first 18 bytes and descriptor slot. -/
def Done (spw : BitVec 64) (ds : List (BitVec 64 × BitVec 64)) (a : Nat) : Prop :=
  (a < spw.toNat - 80 ∨ spw.toNat ≤ a) ∧ (a < 0x80064d48 ∨ 0x80064d48 + 4 ≤ a) ∧
    ∀ p ∈ ds, (a < p.1.toNat ∨ p.1.toNat + 18 ≤ a) ∧ (a < (fdSlot p.2).toNat ∨ (fdSlot p.2).toNat + 4 ≤ a)

theorem done_cons {spw fp fd : BitVec 64} {ds : List (BitVec 64 × BitVec 64)} (a : Nat)
    (h : Done spw ((fp, fd) :: ds) a) : Done spw ds a :=
  ⟨h.1, h.2.1, fun p hp => h.2.2 p (List.mem_cons_of_mem _ hp)⟩

theorem done_fclose {spw fp fd : BitVec 64} {ds : List (BitVec 64 × BitVec 64)} (a : Nat)
    (h : Done spw ((fp, fd) :: ds) a) : FcloseKeep spw fp fd a :=
  ⟨h.1, (h.2.2 _ (List.mem_cons_self ..)).1, h.2.1, (h.2.2 _ (List.mem_cons_self ..)).2⟩

/-- The walk's state at a block boundary. -/
abbrev Walk (b : Config) (spw reent g : BitVec 64) (ds : List (BitVec 64 × BitVec 64)) (fp e acc : BitVec 64) :=
  Frame b (Done spw ds) (walkPins spw reent g fp e acc) WalkHold

theorem walk_pinsOk (spw reent g fp e acc : BitVec 64) :
    ∀ n ∈ keysG (walkPins spw reent g fp e acc), 2 ≤ n ∧ n ≤ 31 := by
  rw [walkPins_keys]; decide

theorem walk_pinsKept (spw reent g fp e acc : BitVec 64) :
    ∀ n ∈ keysG (walkPins spw reent g fp e acc), CalleeKept n := by
  rw [walkPins_keys]; intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; unfold CalleeKept; omega

/-- **One visit of the walk**: the stream at `s0` is live (`_flags > 1`) and
open (`_file = fd ≠ -1`); `_fclose_r(reent, fp)` returns 0, `s6` stays 0. -/
theorem fwalk_visit {b c : Config} {spw reent g fp e fd : BitVec 64} {ds : List (BitVec 64 × BitVec 64)}
    (W : Walk b spw reent g ds fp e 0#64 c) (frame : NativeFrame spw 80) (file : Closable c.σ.mem reent fp)
    (pl : Placed reent fp) (flush : FlushCall c spw fp reent)
    (fdAt : bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat) = fd) (fdNe : fd ≠ 18446744073709551615#64)
    (live : guardB .BGEU 1#64 (bytesVal .lhu (read8 c.σ.mem (fp + 16#64).toNat)) = false) :
    FnSummary 0x8003f6c8#64 (fun d => d = c)
      (fun d => PCAt 0x8003f6ec#64 d ∧ Walk b spw reent g ((fp, fd) :: ds) fp e 0#64 d) := by
  have pk := walk_pinsOk spw reent g fp e 0#64
  have pk1 (n : Nat) (hn : n ∈ keysG (walkPins spw reent g fp e 0#64)) : 1 ≤ n ∧ n ≤ 31 :=
    ⟨by have := pk n hn; omega, (pk n hn).2⟩
  have s0 : gprGet c.σ 8 = some fp := W.pin rfl
  -- `_flags > 1`
  apply summary_bind (FwalkSglue.flagsOk_fast c (regsAt c) W.leaf
    (by simp only [FwalkSglue.flagsOk_input, GHolds]
        exact ⟨gpr_some (gpr_some_of s0), W.reg 10 (by decide), gpr_some (gpr_some_of (W.pin (n := 23) rfl)), trivial⟩)
    (by rw [regsAt_of s0]; exact file.flagsR)
    (by simp only [FwalkSglue.flagsOk_loads, List.getD_cons_zero, regsAt_of s0, regsAt_of (W.pin (n := 23) rfl)]
        exact live)) (fun _ p => p.pc)
  intro c1 p1
  have W1 := W.step p1 (fun _ _ => trivial) (by decide) (by simp [FwalkSglue.flagsOk_regs, keysG]) (by decide)
    (fun n hn => ⟨(pk1 n hn).1, (pk1 n hn).2, by
      rw [walkPins_keys] at hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega⟩)
  -- `_file != -1`; `a0 = reent`, `a1 = fp`
  have s0' : gprGet c1.σ 8 = some fp := W1.pin rfl
  have m1 : c1.σ.mem = c.σ.mem := by rw [p1.memory, Named.NamedValue.wl_nil]
  apply summary_bind (FwalkSglue.fileOk_fast c1 (regsAt c1) W1.leaf
    (by simp only [FwalkSglue.fileOk_input, GHolds]
        exact ⟨gpr_some (gpr_some_of s0'), W1.reg 10 (by decide), gpr_some (gpr_some_of (W1.pin (n := 19) rfl)),
          gpr_some (gpr_some_of (W1.pin (n := 20) rfl)), trivial⟩)
    (by rw [regsAt_of s0']; exact file.fileR)
    (by simp only [FwalkSglue.fileOk_loads, List.getD_cons_zero, regsAt_of s0', regsAt_of (W1.pin (n := 19) rfl), m1,
          fdAt]
        simpa [guardB] using fdNe)) (fun _ p => p.pc)
  intro c2 p2
  have W2 := W1.step p2 (fun _ _ => trivial) (by decide) (by simp [FwalkSglue.fileOk_regs, keysG]) (by decide)
    (fun n hn => ⟨(pk1 n hn).1, (pk1 n hn).2, by
      rw [walkPins_keys] at hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega⟩)
  have o2 := p2.regs
  simp only [FwalkSglue.fileOk_regs, regsAt_of s0', regsAt_of (W1.pin (n := 20) rfl), GHolds] at o2
  obtain ⟨a0, a1, -⟩ := o2
  have m2 : c2.σ.mem = c.σ.mem := by rw [p2.memory, Named.NamedValue.wl_nil, m1]
  -- `jalr s5`
  apply summary_bind (FwalkSglue.call_fast c2 (regsAt c2) W2.leaf
    (by simp only [FwalkSglue.call_input, GHolds]
        exact ⟨W2.reg 1 (by decide), gpr_some (gpr_some_of a0), gpr_some (gpr_some_of a1),
          gpr_some (gpr_some_of (W2.pin (n := 21) rfl)), trivial⟩)) (fun _ p => p.pc)
  intro c3 p3
  have W3 := W2.step p3 (fun _ _ => trivial) (by decide) (by simp) (by decide)
    (fun n hn => ⟨(pk1 n hn).1, (pk1 n hn).2, by simp⟩)
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c3.σ n = gprGet c2.σ n := p3.gpr_frame (by decide) n lo hi (by simp)
  have m3 : c3.σ.mem = c.σ.mem := by rw [p3.memory, Named.NamedValue.wl_nil, m2]
  apply summary_bind (indirect_registers_summary FwalkSglue.call_call_shape FwalkSglue.call_call_decode c3
    (FwalkSglue.call_call_pins W3.ctx.image) W3.ctx.ok.good W3.ctx.image W3.ctx.ok.tick W3.ctx.minstret
    [(21, 0x8004ce68#64), (10, reent), (11, fp)]
    ⟨W3.pin (n := 21) rfl, (k3 10 (by decide) (by decide)).trans a0, (k3 11 (by decide) (by decide)).trans a1, trivial⟩
    (by change KeysOK [21, 10, 11]; decide) (by simp [KeysAvoidRa, keysG]) 0x8004ce68#64 rfl (by decide) rfl)
    (fun _ q => q.pc)
  intro c4 q4
  have W4 := W3.call q4 (by decide) (by decide) pk
  have m4 : c4.σ.mem = c.σ.mem := by rw [q4.memory, m3]
  have link4 : gprGet c4.σ 1 = some 0x8003f6e4#64 := gholds_lookup (n := 1) _ q4.regs rfl
  rw [show FwalkSglue.call_call.target 0x8004ce68#64 = 0x8004ce68#64 by decide]
  -- `_fclose_r(reent, fp)`
  have ctx4 : KeepCtx (Out32 spw) c c4 :=
    ((((KeepCtx.refl (keep := fun _ => True) W.ctx.ok W.ctx.image W.ctx.minstret).step p1 (fun _ _ => trivial)
      (by decide) (by simp [FwalkSglue.flagsOk_regs, keysG])).step p2 (fun _ _ => trivial) (by decide)
      (by simp [FwalkSglue.fileOk_regs, keysG])).step p3 (fun _ _ => trivial) (by decide) (by simp)).call q4
      (by simp [keysG]) |>.mono fun _ _ => trivial
  have S := fclose_returned (W4.ctx.leaf link4 (by decide)) W4.ctx.ok (W4.pin (n := 2) rfl)
    (gholds_lookup (n := 10) _ q4.regs rfl) (gholds_lookup (n := 11) _ q4.regs rfl) frame (m4 ▸ file) pl
    (FlushCall.transport flush ctx4)
  rw [m4, fdAt] at S
  apply summary_bind S (fun _ r => r.pc)
  intro c5 r5
  have W5 := (W4.mono (keep' := Done spw ((fp, fd) :: ds)) done_cons).returned r5 (by decide) done_fclose
    (walk_pinsKept spw reent g fp e 0#64) fun n hn => Or.inr (Or.inr (Or.inr ⟨by omega, hn.2⟩))
  -- `s6 |= 0`
  apply (FwalkSglue.acc_fast c5 (regsAt c5) W5.leaf
    (by simp only [FwalkSglue.acc_input, GHolds]
        exact ⟨W5.reg 10 (by decide), gpr_some (gpr_some_of (W5.pin (n := 22) rfl)), trivial⟩)).weaken (fun _ e => e)
  intro c6 p6
  have k6 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [22]) : gprGet c6.σ n = gprGet c5.σ n :=
    p6.gpr_frame (by decide) n lo hi out
  have acc : gprGet c6.σ 22 = some 0#64 := by
    have := gholds_lookup (n := 22) _ p6.regs rfl
    rw [this, regsAt_of r5.result, regsAt_of (W5.pin (n := 22) rfl)]; rfl
  refine ⟨p6.pc, W5.stepTo p6 (fun _ _ => trivial) (by decide) (by simp [FwalkSglue.acc_regs, keysG]) (by decide) ?_⟩
  exact ⟨(k6 2 (by decide) (by decide) (by decide)).trans (W5.pin rfl),
    (k6 8 (by decide) (by decide) (by decide)).trans (W5.pin rfl), (k6 9 (by decide) (by decide) (by decide)).trans (W5.pin rfl),
    (k6 18 (by decide) (by decide) (by decide)).trans (W5.pin rfl),
    (k6 19 (by decide) (by decide) (by decide)).trans (W5.pin rfl),
    (k6 20 (by decide) (by decide) (by decide)).trans (W5.pin rfl),
    (k6 21 (by decide) (by decide) (by decide)).trans (W5.pin rfl), acc,
    (k6 23 (by decide) (by decide) (by decide)).trans (W5.pin rfl), trivial⟩

open OCaml.Vm.Primitives.Uncaught.StdioFlush (stdinFile stdoutFile stderrFile)

/-- `_impure_data`, newlib's reentrancy structure. -/
def impure : BitVec 64 := 0x80064668#64
/-- `__sglue`, the glue of the three standard streams. -/
def sglue : BitVec 64 := 0x800643a0#64

/-- **A standard stream at exit**: flags, descriptor, no lock flag, closed by
`__sclose` on itself, no buffers, a live console descriptor. -/
structure StdStream (m : Std.ExtHashMap Nat (BitVec 8)) (fp fd flags : BitVec 64) : Prop where
  flagsAt : bytesVal .lh (read8 m (fp + 16#64).toNat) = flags
  fileAt : bytesVal .lh (read8 m (fp + 18#64).toNat) = fd
  flags2 : bytesVal .lw (read8 m (fp + 176#64).toNat) &&& 1#64 = 0#64
  close : bytesVal .ld (read8 m (fp + 80#64).toNat) = scloseFn
  cookie : bytesVal .ld (read8 m (fp + 48#64).toNat) = fp
  ub : bytesVal .ld (read8 m (fp + 88#64).toNat) = 0#64
  lb : bytesVal .ld (read8 m (fp + 120#64).toNat) = 0#64
  slot : FdLive m fd

/-- **newlib's stdio at exit**: one glue of three streams (stdin read-only and
never read, stdout never written, stderr unbuffered with nothing pending),
and `__cleanup` set. Supplied by the state `fprintf(stderr, …)` leaves
(`FprintfReport`). -/
structure StdioAtExit (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  next : bytesVal .ld (read8 m sglue.toNat) = 0#64
  niobs : bytesVal .lw (read8 m (sglue + 8#64).toNat) = 3#64
  iobs : bytesVal .ld (read8 m (sglue + 16#64).toNat) = stdinFile
  cleanup : bytesVal .ld (read8 m (impure + 72#64).toNat) ≠ 0#64
  stdin : StdStream m stdinFile 0#64 4#64
  stdout : StdStream m stdoutFile 1#64 9#64
  stderr : StdStream m stderrFile 2#64 0x201a#64
  stdinR : bytesVal .lw (read8 m (stdinFile + 8#64).toNat) = 0#64
  stdinUR : bytesVal .lw (read8 m (stdinFile + 112#64).toNat) = 0#64
  stdoutBase : bytesVal .ld (read8 m (stdoutFile + 24#64).toNat) = 0#64
  stderrBase : bytesVal .ld (read8 m (stderrFile + 24#64).toNat) ≠ 0#64
  stderrPos : bytesVal .ld (read8 m stderrFile.toNat) = bytesVal .ld (read8 m (stderrFile + 24#64).toNat)

/-- The address facts of a stream's fields. -/
structure StreamWindows (fp : BitVec 64) : Prop where
  flags2R : ReadWindow (fp + 176#64) 4
  flagsR : ReadWindow (fp + 16#64) 2
  flagsW : WriteWindow (fp + 16#64) 2
  flagsOut : ImageOutside [((fp + 16#64).toNat, 2, 0#64)]
  lockR : ReadWindow (fp + 160#64) 8
  closeR : ReadWindow (fp + 80#64) 8
  cookieR : ReadWindow (fp + 48#64) 8
  fileR : ReadWindow (fp + 18#64) 2
  ubR : ReadWindow (fp + 88#64) 8
  lbR : ReadWindow (fp + 120#64) 8

theorem streamWindows {fp : BitVec 64} (lo : Layout.sym_tohost + 16 ≤ fp.toNat) (ro : 0x80061fb0 ≤ fp.toNat)
    (hi : fp.toNat + 184 ≤ 0x100000000) (al : fp.toNat % 8 = 0) : StreamWindows fp := by
  have n (k : Nat) (hk : k ≤ 184) : (fp + BitVec.ofNat 64 k).toNat = fp.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t : 0x80000000 ≤ Layout.sym_tohost := by decide
  have rw_ (k w : Nat) (hk : k + w ≤ 184) : ReadWindow (fp + BitVec.ofNat 64 k) w :=
    ⟨by rw [n k (by omega)]; omega, by rw [n k (by omega)]; omega, Or.inr (by rw [n k (by omega)]; omega)⟩
  exact ⟨rw_ 176 4 (by decide), rw_ 16 2 (by decide),
    ⟨by rw [n 16 (by decide)]; omega, by rw [n 16 (by decide)]; omega, by rw [n 16 (by decide)]; omega,
      by rw [n 16 (by decide)]; omega⟩,
    StdioFrame.imageOutside_above fun e he => by
      rcases List.mem_singleton.mp he with rfl; show 0x80061fb0 ≤ (fp + 16#64).toNat; rw [n 16 (by decide)]; omega,
    rw_ 160 8 (by decide), rw_ 80 8 (by decide), rw_ 48 8 (by decide), rw_ 18 2 (by decide), rw_ 88 8 (by decide),
    rw_ 120 8 (by decide)⟩

/-- `Closable` from a stream's facts. -/
theorem StdStream.closable {m : Std.ExtHashMap Nat (BitVec 8)} {reent fp fd flags : BitVec 64}
    (h : StdStream m fp fd flags) (w : StreamWindows fp) (cleanupR : ReadWindow (reent + 72#64) 8)
    (cleanup : bytesVal .ld (read8 m (reent + 72#64).toNat) ≠ 0#64) (live : flags ≠ 0#64)
    (notStr : flags &&& 512#64 = 0#64) : Closable m reent fp where
  cleanupR := cleanupR
  cleanup := cleanup
  flags2R := w.flags2R
  flags2 := h.flags2
  flagsR := w.flagsR
  flagsW := w.flagsW
  flagsOut := w.flagsOut
  live := by rw [h.flagsAt]; exact live
  notStr := by rw [h.flagsAt]; exact notStr
  lockR := w.lockR
  closeR := w.closeR
  close := h.close
  cookieR := w.cookieR
  cookie := h.cookie
  fileR := w.fileR
  fd := by rw [h.fileAt]; exact h.slot
  ubR := w.ubR
  ub := h.ub
  lbR := w.lbR
  lb := h.lb

/-- The words a stream's close reads. -/
def StreamReads (fp fd : BitVec 64) (a : Nat) : Prop :=
  a = (fp + 16#64).toNat ∨ a = (fp + 18#64).toNat ∨ a = (fp + 176#64).toNat ∨ a = (fp + 80#64).toNat ∨
    a = (fp + 48#64).toNat ∨ a = (fp + 88#64).toNat ∨ a = (fp + 120#64).toNat ∨ a = (0x80064918#64).toNat ∨
    a = (fdSlot fd).toNat

theorem StdStream.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {fp fd flags : BitVec 64}
    (h : StdStream m fp fd flags) (r : ∀ a, StreamReads fp fd a → read8 m' a = read8 m a) : StdStream m' fp fd flags where
  flagsAt := by rw [r _ (Or.inl rfl)]; exact h.flagsAt
  fileAt := by rw [r _ (Or.inr (Or.inl rfl))]; exact h.fileAt
  flags2 := by rw [r _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.flags2
  close := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact h.close
  cookie := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact h.cookie
  ub := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]; exact h.ub
  lb := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))]; exact h.lb
  slot := fdLive_of_read h.slot (r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
    (r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))

theorem readWindow_of {a : BitVec 64} {w : Nat}
    (h : 0x80000000 ≤ a.toNat ∧ a.toNat + w ≤ 0x100000000 ∧
      (a.toNat + w ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ a.toNat)) : ReadWindow a w :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- The walk's frame, 80 bytes below the entry `sp`. -/
def walkSp (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551536#64

/-- Outside the walk's own frame. -/
def Out80 (sp : BitVec 64) (a : Nat) : Prop := a < sp.toNat - 80 ∨ sp.toNat ≤ a

/-- The walk's registers before the loop: `sp`, the glue, `-1`, the
arguments, `0`, `1`. -/
def startPins (sp : BitVec 64) : GRegs :=
  [(2, walkSp sp), (18, sglue), (19, 18446744073709551615#64), (20, impure), (21, 0x8004ce68#64), (22, 0#64),
    (23, 1#64)]

/-- After `stdio_exit_handler` and `_fwalk_sglue`'s prologue (at `0x8003f69c`). -/
structure WalkStarted (c : Config) (sp code : BitVec 64) (d : Config) : Prop where
  frame : Frame d (Done (walkSp sp) []) (startPins sp) WalkHold d
  ctx : KeepCtx (Out80 sp) c d
  raS : bytesVal .ld (read8 d.σ.mem (walkSp sp + 72#64).toNat) = 0x800373f0#64
  s0S : bytesVal .ld (read8 d.σ.mem (walkSp sp + 64#64).toNat) = code

/-- **`stdio_exit_handler`, then `_fwalk_sglue`'s prologue**: the handler
passes `(_impure_data, _fclose_r, &__sglue)` and jumps; the walk saves `ra`,
`s0`–`s7` and sets up its registers. -/
theorem fwalk_open {c : Config} {sp code : BitVec 64} (ok : ExitOk c) (image : ExecutableImage c)
    (minstret : ∃ v, c.σ.regs.get? Register.minstret = some v) (ra : gprGet c.σ 1 = some 0x800373f0#64)
    (spR : gprGet c.σ 2 = some sp) (codeR : gprGet c.σ 8 = some code) (frame : NativeFrame sp 160) :
    FnSummary 0x8003e900#64 (fun d => d = c) (fun d => PCAt 0x8003f69c#64 d ∧ WalkStarted c sp code d) := by
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have l0 : LeafInput (regsAt c 1) c := by rw [regsAt_of ra]; exact ⟨ok.good, image, minstret, ra, by decide, ok.tick⟩
  apply summary_bind (StdioExitHandler.enter_fast c (regsAt c) l0
    (by simp only [StdioExitHandler.enter_input, GHolds]
        exact ⟨gpr_some (gpr_some_of ra), gpr_some (ok.present 10 (by decide)), trivial⟩)) (fun _ p => p.pc)
  intro c1 p1
  have o1 := p1.regs
  simp only [StdioExitHandler.enter_regs, regsAt_of ra, GHolds] at o1
  obtain ⟨g10, g11, g12, g1, -⟩ := o1
  have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 12]) : gprGet c1.σ n = gprGet c.σ n :=
    p1.gpr_frame (by decide) n lo hi out
  have ctx1 : KeepCtx (Out80 sp) c c1 :=
    (KeepCtx.refl ok image minstret).step p1 (fun _ _ => trivial) (by decide)
      (by simp [StdioExitHandler.enter_regs, keysG])
  have pr (n : Nat) (hn : n ∈ exitReads) : gprGet c1.σ n = some (regsAt c1 n) := gpr_some (ctx1.ok.present n hn)
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of g1]; exact ⟨p1.good, p1.image, p1.minstret, g1, by decide, p1.tick⟩
  have sp80 : sp + 18446744073709551536#64 = sp - 80#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have g2 : gprGet c1.σ 2 = some sp := (k1 2 (by decide) (by decide) (by decide)).trans spR
  have g8 : gprGet c1.σ 8 = some code := (k1 8 (by decide) (by decide) (by decide)).trans codeR
  have ww (off : Nat) (ho : off + 8 ≤ 80) (ao : off % 8 = 0) :
      WriteWindow (regsAt c1 2 + 18446744073709551536#64 + BitVec.ofNat 64 off) 8 := by
    rw [regsAt_of g2, sp80]; exact frame_word (k := 80) (off := off) frame (by decide) ho (by decide) ao
  have n (off : Nat) (ho : off ≤ 80) := frame_nat (k := 80) (off := off) frame (by decide) ho
  apply (FwalkSglue.pro_fast c1 (regsAt c1) l1
    (by simp only [FwalkSglue.pro_input, GHolds]
        exact ⟨pr 1 (by decide), pr 2 (by decide), pr 8 (by decide), pr 9 (by decide), pr 10 (by decide),
          gpr_some (gpr_some_of g11), gpr_some (gpr_some_of g12), pr 18 (by decide), pr 19 (by decide),
          pr 20 (by decide), pr 21 (by decide), pr 22 (by decide), pr 23 (by decide), trivial⟩)
    (ww 48 (by decide) (by decide)) (ww 40 (by decide) (by decide)) (ww 32 (by decide) (by decide))
    (ww 24 (by decide) (by decide)) (ww 16 (by decide) (by decide)) (ww 8 (by decide) (by decide))
    (ww 72 (by decide) (by decide)) (ww 64 (by decide) (by decide)) (ww 56 (by decide) (by decide))
    (StdioFrame.imageOutside_above fun e he => by
      simp only [FwalkSglue.proLog, regsAt_of g2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [n 48 (by decide), n 40 (by decide), n 32 (by decide), n 24 (by decide), n 16 (by decide),
          n 8 (by decide), n 72 (by decide), n 64 (by decide), n 56 (by decide)] <;> omega)).weaken (fun _ e => e)
  intro c2 p2
  have o2 := p2.regs
  simp only [FwalkSglue.pro_regs, regsAt_of g10, regsAt_of g11, regsAt_of g12, regsAt_of g2, GHolds] at o2
  obtain ⟨h19, h23, h22, h21, h20, h18, h2, h1, -⟩ := o2
  have log2 : FwalkSglue.proLog (regsAt c1) (FwalkSglue.pro_loads c1.σ.mem (regsAt c1)) =
      FwalkSglue.proLog (regsAt c1) [] := rfl
  refine ⟨p2.pc, ⟨Frame.start (ctx1.step p2 (fun x hx => ?_) (by decide) (by simp [FwalkSglue.pro_regs, keysG])).ok
    p2.image p2.minstret ⟨0x800373f0#64, by rw [h1, regsAt_of g1], by decide⟩
    ⟨by rw [h2]; rfl, h18, h19, h20, h21, h22, h23, trivial⟩,
    ctx1.step p2 (fun x hx => ?_) (by decide) (by simp [FwalkSglue.pro_regs, keysG]), ?_, ?_⟩⟩
  · simp only [FwalkSglue.proLog, regsAt_of g2, OutL, n 48 (by decide), n 40 (by decide), n 32 (by decide),
      n 24 (by decide), n 16 (by decide), n 8 (by decide), n 72 (by decide), n 64 (by decide), n 56 (by decide), and_true]
    unfold Out80 at hx; omega
  · simp only [FwalkSglue.proLog, regsAt_of g2, OutL, n 48 (by decide), n 40 (by decide), n 32 (by decide),
      n 24 (by decide), n 16 (by decide), n 8 (by decide), n 72 (by decide), n 64 (by decide), n 56 (by decide), and_true]
    unfold Out80 at hx; omega
  · rw [read8_value, p2.memory, log2, p1.memory, Named.NamedValue.wl_nil]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 6 _ _ (by simp only [FwalkSglue.proLog, regsAt_of g1, regsAt_of g2, walkSp, sp80]; rfl)
      (by simp only [FwalkSglue.proLog, List.drop, OutLRange, regsAt_of g2, walkSp, sp80, n 72 (by decide),
            n 64 (by decide), n 56 (by decide), and_true]; omega)
  · rw [read8_value, p2.memory, log2, p1.memory, Named.NamedValue.wl_nil]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 7 _ _ (by simp only [FwalkSglue.proLog, regsAt_of g8, regsAt_of g2, walkSp, sp80]; rfl)
      (by simp only [FwalkSglue.proLog, List.drop, OutLRange, regsAt_of g2, walkSp, sp80, n 64 (by decide),
            n 56 (by decide), and_true]; omega)

end OCaml.Vm.Primitives.Uncaught.StdioWalk
