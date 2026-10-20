import OCaml.Vm.Primitives.Uncaught.StdioFclose
import OCaml.Vm.Primitives.Uncaught.FwalkSglue

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
open OCaml.Vm.Primitives.Uncaught.StdioClose (fdSlot fdSlot_toNat FdLive)
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

end OCaml.Vm.Primitives.Uncaught.StdioWalk
