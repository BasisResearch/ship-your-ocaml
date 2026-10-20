import OCaml.Vm.Primitives.Uncaught.StdioState
import OCaml.Vm.Primitives.Uncaught.FwalkSglue
import OCaml.Vm.Primitives.Uncaught.StdioExitHandler
import OCaml.Vm.Primitives.ExitPath.LibcExitHandler

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
open OCaml.Vm.Primitives.Uncaught.StdioState

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

theorem startPins_keys (sp : BitVec 64) : keysG (startPins sp) = [2, 18, 19, 20, 21, 22, 23] := rfl

/-- Repin the stream `s0` after an `addi s0, s0, 184` block. -/
theorem Walk.setFp {b c d : Config} {spw reent g e acc fp fp' pc v : BitVec 64} {ds : List (BitVec 64 × BitVec 64)}
    {regs : GRegs} (W : Walk b spw reent g ds fp e acc c) (p : WriteRegistersPost [8] [] c pc v regs d)
    (cover : 8 ∈ keysG regs) (h8 : gprGet d.σ 8 = some fp') : Walk b spw reent g ds fp' e acc d :=
  have fr (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [8]) : gprGet d.σ n = gprGet c.σ n :=
    p.toEffectPost.gpr_frame (by decide) n lo hi out
  W.stepTo p (fun _ _ => trivial) (by decide) (fun n hn => by simp at hn; subst hn; exact cover) (by decide)
    ⟨(fr 2 (by decide) (by decide) (by decide)).trans (W.pin rfl), h8,
      (fr 9 (by decide) (by decide) (by decide)).trans (W.pin rfl), (fr 18 (by decide) (by decide) (by decide)).trans (W.pin rfl),
      (fr 19 (by decide) (by decide) (by decide)).trans (W.pin rfl), (fr 20 (by decide) (by decide) (by decide)).trans (W.pin rfl),
      (fr 21 (by decide) (by decide) (by decide)).trans (W.pin rfl), (fr 22 (by decide) (by decide) (by decide)).trans (W.pin rfl),
      (fr 23 (by decide) (by decide) (by decide)).trans (W.pin rfl), trivial⟩

/-- Repin the glue `s2` after `ld s2, 0(s2)`. -/
theorem Walk.setGlue {b c d : Config} {spw reent g g' e acc fp pc v : BitVec 64} {ds : List (BitVec 64 × BitVec 64)}
    {regs : GRegs} (W : Walk b spw reent g ds fp e acc c) (p : WriteRegistersPost [18] [] c pc v regs d)
    (cover : 18 ∈ keysG regs) (h18 : gprGet d.σ 18 = some g') : Walk b spw reent g' ds fp e acc d :=
  have fr (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [18]) : gprGet d.σ n = gprGet c.σ n :=
    p.toEffectPost.gpr_frame (by decide) n lo hi out
  W.stepTo p (fun _ _ => trivial) (by decide) (fun n hn => by simp at hn; subst hn; exact cover) (by decide)
    ⟨(fr 2 (by decide) (by decide) (by decide)).trans (W.pin rfl), (fr 8 (by decide) (by decide) (by decide)).trans (W.pin rfl),
      (fr 9 (by decide) (by decide) (by decide)).trans (W.pin rfl), h18,
      (fr 19 (by decide) (by decide) (by decide)).trans (W.pin rfl), (fr 20 (by decide) (by decide) (by decide)).trans (W.pin rfl),
      (fr 21 (by decide) (by decide) (by decide)).trans (W.pin rfl), (fr 22 (by decide) (by decide) (by decide)).trans (W.pin rfl),
      (fr 23 (by decide) (by decide) (by decide)).trans (W.pin rfl), trivial⟩

/-- **A visit of a standard stream**, from its facts at the walk's call. -/
theorem fwalk_visit_std {b c d : Config} {spw fp fd flags e : BitVec 64} {ds : List (BitVec 64 × BitVec 64)}
    (W : Walk b spw impure sglue ds fp e 0#64 d) (frame : NativeFrame spw 80) (hs : StdStream c.σ.mem fp fd flags)
    (reads : ∀ a, StreamReads fp fd a → read8 d.σ.mem a = read8 c.σ.mem a)
    (cleanup : read8 d.σ.mem (impure + 72#64).toNat = read8 c.σ.mem (impure + 72#64).toNat)
    (cleanupNz : bytesVal .ld (read8 c.σ.mem (impure + 72#64).toNat) ≠ 0#64) (win : StreamWindows fp)
    (pl : Placed impure fp) (flush : FlushCall d spw fp impure) (live : flags ≠ 0#64) (notStr : flags &&& 512#64 = 0#64)
    (small : flags.toNat < 0x8000) (gt : guardB .BGEU 1#64 flags = false) (fdNe : fd ≠ 18446744073709551615#64) :
    FnSummary 0x8003f6c8#64 (fun d' => d' = d)
      (fun d' => PCAt 0x8003f6ec#64 d' ∧ Walk b spw impure sglue ((fp, fd) :: ds) fp e 0#64 d') :=
  have hs' := hs.transport reads
  fwalk_visit W frame (StdStream.closable hs' win (readWindow_of (by decide)) (by rw [cleanup]; exact cleanupNz) live notStr) pl
    flush hs'.fileAt fdNe (by rw [lhu_of_lh _ (by rw [hs'.flagsAt]; exact small), hs'.flagsAt]; exact gt)

/-- The end of the three streams. -/
def streamsEnd : BitVec 64 := 0x8007cc60#64

/-- **`_fwalk_sglue` over the standard streams, back in `exit`**: one glue of
three streams, each closed; `s0` (the status) and `ra` restored. -/
theorem fwalk_rest {c c2 : Config} {sp code : BitVec 64} (S : WalkStarted c sp code c2) (frame : NativeFrame sp 160)
    (stdio : StdioAtExit c.σ.mem) :
    FnSummary 0x8003f69c#64 (fun d => d = c2) (ExitPath.HandlerReturned code c) := by
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have sp80 : walkSp sp = sp - 80#64 := by unfold walkSp; rw [BitVec.sub_eq_add_neg]; rfl
  have wN : (walkSp sp).toNat = sp.toNat - 80 := by rw [sp80, BitVec.toNat_sub]; simp; omega
  have frameW : NativeFrame (walkSp sp) 80 := frame_callee (front := 80) (size := 80) frame (by decide) _ (by decide)
  have rd {d : Config} {ds : List (BitVec 64 × BitVec 64)} {pins : GRegs}
      (F : Frame c2 (Done (walkSp sp) ds) pins WalkHold d) (a : Nat) (low : a + 8 ≤ Vsa.Sim.DlHeap.heapEnd)
      (kept : ∀ j, j < 8 → (a + j < 0x80064d48 ∨ 0x80064d48 + 4 ≤ a + j) ∧
        ∀ p ∈ ds, (a + j < p.1.toNat ∨ p.1.toNat + 18 ≤ a + j) ∧
          (a + j < (fdSlot p.2).toNat ∨ (fdSlot p.2).toNat + 4 ≤ a + j)) :
      read8 d.σ.mem a = read8 c.σ.mem a := by
    simp only [Vsa.Sim.DlHeap.heapEnd] at low
    exact (F.ctx.read fun j hj => ⟨Or.inl (by omega), (kept j hj).1, (kept j hj).2⟩).trans
      (S.ctx.read fun j _ => Or.inl (by omega))
  have F2 := S.frame
  have g18 : gprGet c2.σ 18 = some sglue := F2.pin rfl
  -- `g->_niobs = 3 > 0`
  apply summary_bind (FwalkSglue.niobs_fast c2 (regsAt c2) F2.leaf
    (by simp only [FwalkSglue.niobs_input, GHolds]; exact ⟨F2.reg 10 (by decide), gpr_some (gpr_some_of g18), trivial⟩)
    (by rw [regsAt_of g18]; exact readWindow_of (by decide))
    (by simp only [FwalkSglue.niobs_loads, List.getD_cons_zero, regsAt_of g18]
        rw [rd F2 _ (by decide) (by decide), stdio.niobs]; decide)) (fun _ p => p.pc)
  intro c3 p3
  have F3 := F2.step p3 (fun _ _ => trivial) (by decide) (by simp [FwalkSglue.niobs_regs, keysG]) (by decide)
    (by rw [startPins_keys]; decide)
  have g15 : gprGet c3.σ 15 = some 3#64 := by
    have := gholds_lookup (n := 15) _ p3.regs rfl
    simp only [FwalkSglue.niobs_loads, List.getD_cons_zero, regsAt_of g18] at this
    rw [this, rd F2 _ (by decide) (by decide), stdio.niobs]
  have g18' : gprGet c3.σ 18 = some sglue := F3.pin rfl
  -- `fp = g->_iobs`, `end = fp + 184 * 3`
  apply summary_bind (FwalkSglue.bound_fast c3 (regsAt c3) F3.leaf
    (by simp only [FwalkSglue.bound_input, GHolds]
        exact ⟨F3.reg 10 (by decide), gpr_some (gpr_some_of g15), gpr_some (gpr_some_of g18'), trivial⟩)
    (by rw [regsAt_of g18']; exact readWindow_of (by decide))) (fun _ p => p.pc)
  intro c4 p4
  have iobs : bytesVal .ld (read8 c3.σ.mem (sglue + 16#64).toNat) = stdinFile := by
    rw [rd F3 _ (by decide) (by decide), stdio.iobs]
  have o4 := p4.regs
  simp only [FwalkSglue.bound_regs, FwalkSglue.bound_loads, List.getD_cons_zero, regsAt_of g15, regsAt_of g18', iobs,
    GHolds] at o4
  obtain ⟨h9, h8, -⟩ := o4
  have fr4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [8, 9, 15]) : gprGet c4.σ n = gprGet c3.σ n :=
    p4.gpr_frame (by decide) n lo hi out
  have W4 : Walk c2 (walkSp sp) impure sglue [] stdinFile streamsEnd 0#64 c4 :=
    F3.stepTo p4 (fun _ _ => trivial) (by decide) (by simp [FwalkSglue.bound_regs, keysG]) (by decide)
      ⟨(fr4 2 (by decide) (by decide) (by decide)).trans (F3.pin rfl), h8, h9.trans (by decide),
        (fr4 18 (by decide) (by decide) (by decide)).trans (F3.pin rfl),
        (fr4 19 (by decide) (by decide) (by decide)).trans (F3.pin rfl),
        (fr4 20 (by decide) (by decide) (by decide)).trans (F3.pin rfl),
        (fr4 21 (by decide) (by decide) (by decide)).trans (F3.pin rfl),
        (fr4 22 (by decide) (by decide) (by decide)).trans (F3.pin rfl),
        (fr4 23 (by decide) (by decide) (by decide)).trans (F3.pin rfl), trivial⟩
  have pl (fp : BitVec 64) (h : 0x80065098 ≤ fp.toNat ∧ fp.toNat + 184 ≤ Vsa.Sim.DlHeap.heapEnd) : Placed impure fp :=
    ⟨h.2, h.1, by decide, by decide⟩
  have win (fp : BitVec 64) (h : Layout.sym_tohost + 16 ≤ fp.toNat ∧ 0x80061fb0 ≤ fp.toNat ∧
      fp.toNat + 184 ≤ 0x100000000 ∧ fp.toNat % 8 = 0) : StreamWindows fp :=
    streamWindows h.1 h.2.1 h.2.2.1 h.2.2.2
  -- stdin
  apply summary_bind (fwalk_visit_std W4 frameW stdio.stdin
    (fun a (ha : StreamReads stdinFile 0#64 a) => by
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact rd W4 _ (by decide) (by decide))
    (rd W4 _ (by decide) (by decide)) stdio.cleanup (win _ (by decide)) (pl _ (by decide))
    (flushCall_stdin frameW (by rw [rd W4 (stdinFile + 16#64).toNat (by decide) (by decide)]; exact stdio.stdin.flagsAt)
      (by rw [rd W4 (stdinFile + 8#64).toNat (by decide) (by decide)]; exact stdio.stdinR)
      (by rw [rd W4 (stdinFile + 112#64).toNat (by decide) (by decide)]; exact stdio.stdinUR))
    (by decide) (by decide) (by decide) (by decide) (by decide)) (fun _ p => p.1)
  intro c5 h5
  have W5 := h5.2
  apply summary_bind (FwalkSglue.nextMore_fast c5 (regsAt c5) W5.leaf
    (by simp only [FwalkSglue.nextMore_input, GHolds]
        exact ⟨gpr_some (gpr_some_of (W5.pin (n := 8) rfl)), gpr_some (gpr_some_of (W5.pin (n := 9) rfl)),
          W5.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of (W5.pin (n := 8) rfl), regsAt_of (W5.pin (n := 9) rfl)]; decide)) (fun _ p => p.pc)
  intro c6 p6
  have W6 : Walk c2 (walkSp sp) impure sglue [(stdinFile, 0#64)] stdoutFile streamsEnd 0#64 c6 :=
    W5.setFp p6 (by simp [FwalkSglue.nextMore_regs, keysG]) (by
      rw [gholds_lookup (n := 8) _ p6.regs rfl, regsAt_of (W5.pin (n := 8) rfl)]; decide)
  -- stdout
  apply summary_bind (fwalk_visit_std W6 frameW stdio.stdout
    (fun a (ha : StreamReads stdoutFile 1#64 a) => by
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact rd W6 _ (by decide) (by decide))
    (rd W6 _ (by decide) (by decide)) stdio.cleanup (win _ (by decide)) (pl _ (by decide))
    (flushCall_stdout frameW (by rw [rd W6 (stdoutFile + 16#64).toNat (by decide) (by decide)]; exact stdio.stdout.flagsAt)
      (by rw [rd W6 (stdoutFile + 24#64).toNat (by decide) (by decide)]; exact stdio.stdoutBase))
    (by decide) (by decide) (by decide) (by decide) (by decide)) (fun _ p => p.1)
  intro c7 h7
  have W7 := h7.2
  apply summary_bind (FwalkSglue.nextMore_fast c7 (regsAt c7) W7.leaf
    (by simp only [FwalkSglue.nextMore_input, GHolds]
        exact ⟨gpr_some (gpr_some_of (W7.pin (n := 8) rfl)), gpr_some (gpr_some_of (W7.pin (n := 9) rfl)),
          W7.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of (W7.pin (n := 8) rfl), regsAt_of (W7.pin (n := 9) rfl)]; decide)) (fun _ p => p.pc)
  intro c8 p8
  have W8 : Walk c2 (walkSp sp) impure sglue [(stdoutFile, 1#64), (stdinFile, 0#64)] stderrFile streamsEnd 0#64 c8 :=
    W7.setFp p8 (by simp [FwalkSglue.nextMore_regs, keysG]) (by
      rw [gholds_lookup (n := 8) _ p8.regs rfl, regsAt_of (W7.pin (n := 8) rfl)]; decide)
  -- stderr
  apply summary_bind (fwalk_visit_std W8 frameW stdio.stderr
    (fun a (ha : StreamReads stderrFile 2#64 a) => by
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact rd W8 _ (by decide) (by decide))
    (rd W8 _ (by decide) (by decide)) stdio.cleanup (win _ (by decide)) (pl _ (by decide))
    (flushCall_stderr frameW (by rw [rd W8 (stderrFile + 16#64).toNat (by decide) (by decide)]; exact stdio.stderr.flagsAt)
      (by rw [rd W8 (stderrFile + 24#64).toNat (by decide) (by decide)]) stdio.stderrBase
      (by rw [rd W8 stderrFile.toNat (by decide) (by decide)]; exact stdio.stderrPos))
    (by decide) (by decide) (by decide) (by decide) (by decide)) (fun _ p => p.1)
  intro c9 h9
  have W9 := h9.2
  apply summary_bind (FwalkSglue.nextDone_fast c9 (regsAt c9) W9.leaf
    (by simp only [FwalkSglue.nextDone_input, GHolds]
        exact ⟨gpr_some (gpr_some_of (W9.pin (n := 8) rfl)), gpr_some (gpr_some_of (W9.pin (n := 9) rfl)),
          W9.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of (W9.pin (n := 8) rfl), regsAt_of (W9.pin (n := 9) rfl)]; decide)) (fun _ p => p.pc)
  intro c10 p10
  have W10 : Walk c2 (walkSp sp) impure sglue [(stderrFile, 2#64), (stdoutFile, 1#64), (stdinFile, 0#64)] streamsEnd
      streamsEnd 0#64 c10 :=
    W9.setFp p10 (by simp [FwalkSglue.nextDone_regs, keysG]) (by
      rw [gholds_lookup (n := 8) _ p10.regs rfl, regsAt_of (W9.pin (n := 8) rfl)]; decide)
  -- `g->_next = NULL`
  have g18c : gprGet c10.σ 18 = some sglue := W10.pin rfl
  have nextAt : read8 c10.σ.mem sglue.toNat = read8 c.σ.mem sglue.toNat := rd W10 _ (by decide) (by decide)
  apply summary_bind (FwalkSglue.glue_fast c10 (regsAt c10) W10.leaf
    (by simp only [FwalkSglue.glue_input, GHolds]; exact ⟨W10.reg 10 (by decide), gpr_some (gpr_some_of g18c), trivial⟩)
    (by rw [regsAt_of g18c]; exact readWindow_of (by decide))
    (by simp only [FwalkSglue.glue_loads, List.getD_cons_zero, regsAt_of g18c, nextAt, stdio.next]; decide))
    (fun _ p => p.pc)
  intro c11 p11
  have W11 : Walk c2 (walkSp sp) impure 0#64 [(stderrFile, 2#64), (stdoutFile, 1#64), (stdinFile, 0#64)] streamsEnd
      streamsEnd 0#64 c11 :=
    W10.setGlue p11 (by simp [FwalkSglue.glue_regs, keysG]) (by
      rw [gholds_lookup (n := 18) _ p11.regs rfl]
      simp only [FwalkSglue.glue_loads, List.getD_cons_zero, regsAt_of g18c, nextAt, stdio.next])
  -- the epilogue
  have spw : gprGet c11.σ 2 = some (walkSp sp) := W11.pin rfl
  have n (off : Nat) (ho : off ≤ 80) := frame_nat (k := 80) (off := off) frame (by decide) ho
  have hds : ∀ p ∈ [(stderrFile, 2#64), (stdoutFile, 1#64), (stdinFile, 0#64)],
      p.1.toNat + 18 ≤ Vsa.Sim.DlHeap.heapEnd ∧ (fdSlot p.2).toNat + 4 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have rdS (off : Nat) (ho : off + 8 ≤ 80) :
      read8 c11.σ.mem (walkSp sp + BitVec.ofNat 64 off).toNat = read8 c2.σ.mem (walkSp sp + BitVec.ofNat 64 off).toNat := by
    have e : (walkSp sp + BitVec.ofNat 64 off).toNat = sp.toNat - 80 + off := by rw [sp80]; exact n off (by omega)
    exact W11.ctx.read fun j _ => by
      rw [e]
      exact ⟨Or.inr (by omega), Or.inr (by omega), fun p hp => by
        have := hds p hp; simp only [Vsa.Sim.DlHeap.heapEnd] at this; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩⟩
  have w (off : Nat) (ho : off + 8 ≤ 80) (ao : off % 8 = 0) : ReadWindow (regsAt c11 2 + BitVec.ofNat 64 off) 8 := by
    rw [regsAt_of spw, sp80]; exact (frame_word (k := 80) (off := off) frame (by decide) ho (by decide) ao).read
  have raAt : bytesVal .ld (read8 c11.σ.mem (walkSp sp + 72#64).toNat) = 0x800373f0#64 := by
    rw [rdS 72 (by decide)]; exact S.raS
  have s0At : bytesVal .ld (read8 c11.σ.mem (walkSp sp + 64#64).toNat) = code := by
    rw [rdS 64 (by decide)]; exact S.s0S
  apply (FwalkSglue.leave_fast c11 0x800373f0#64 (regsAt c11) W11.leaf
    (by simp only [FwalkSglue.leave_input, GHolds]
        exact ⟨gpr_some (gpr_some_of spw), W11.reg 10 (by decide), gpr_some (gpr_some_of (W11.pin (n := 22) rfl)), trivial⟩)
    (w 72 (by decide) (by decide)) (w 64 (by decide) (by decide)) (w 56 (by decide) (by decide))
    (w 48 (by decide) (by decide)) (w 40 (by decide) (by decide)) (w 32 (by decide) (by decide))
    (w 24 (by decide) (by decide)) (w 8 (by decide) (by decide)) (w 16 (by decide) (by decide))
    (by rw [regsAt_of spw]; exact raAt) (by decide)).weaken (fun _ e => e)
  intro e p
  have o := p.regs
  simp only [FwalkSglue.leave_regs, FwalkSglue.leave_loads, regsAt_of spw, List.getD_cons_zero, List.getD_cons_succ,
    GHolds] at o
  obtain ⟨-, -, -, -, -, -, -, -, -, e8, e1, -⟩ := o
  exact
    { ok := (W11.ctx.step p (fun _ _ => trivial) (by decide) (by simp [FwalkSglue.leave_regs, keysG])).ok
      image := p.image
      minstret := p.minstret
      pc := p.pc
      raReg := ⟨0x800373f0#64, show gprGet e.σ 1 = _ by rw [e1, raAt], by decide⟩
      codeReg := show gprGet e.σ 8 = _ by rw [e8, s0At]
      output := by unfold Vsa.Machine.output; rw [p.output]; exact W11.ctx.output.trans S.ctx.output }

/-- **`exit`'s stdio handler, discharged**: from the stdio state at exit's
entry (`StdioAtExit m0`), with a 160-byte native frame below the handler's
`sp`, `stdio_exit_handler` closes the three standard streams and returns to
`exit` with `s0` kept and nothing printed. -/
theorem stdioExitHandler_of {sp code : BitVec 64} {m0 : Std.ExtHashMap Nat (BitVec 8)}
    (frame : NativeFrame (sp - 16#64) 160) (deep : Vsa.Sim.DlHeap.heapEnd + ExitPath.libcExitDepth ≤ sp.toNat)
    (stdio : StdioAtExit m0) : ExitPath.StdioExitHandler sp code m0 where
  returns c pc ok image minstret ra spR codeR agree := by
    have st : StdioAtExit c.σ.mem := stdio.transport fun a ha =>
      ConsoleWrite.read8_same fun i hi => agree (a + i) (Or.inl (by
        have := (ha.low i hi).1
        simp only [Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd, ExitPath.libcExitDepth] at this deep ⊢
        omega))
    obtain ⟨e, run, h⟩ := (summary_bind (fwalk_open ok image minstret ra spR codeR frame) (fun _ p => p.1)
      fun d hd => fwalk_rest hd.2 frame st).run c ⟨pc, rfl⟩
    exact ⟨e, run, h⟩

end OCaml.Vm.Primitives.Uncaught.StdioWalk
