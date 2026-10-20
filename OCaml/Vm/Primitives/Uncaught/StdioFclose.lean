import OCaml.Vm.Primitives.Uncaught.StdioFrame
import OCaml.Vm.Primitives.Uncaught.Fclose
import OCaml.Vm.Primitives.Uncaught.SfpLockAcquire
import OCaml.Vm.Primitives.Uncaught.SfpLockRelease
import OCaml.Vm.Primitives.Uncaught.RetargetLockClose

/-!
# `_fclose_r` on a standard stream

`_fclose_r(reent, fp)` (single-threaded newlib: the locks are `ret` leaves)
flushes the stream (`__sflush_r`), closes its descriptor through the
stream's close function (`__sclose`), frees no buffer (none was allocated),
clears `_flags` and returns the flush's result. Between its prologue and
epilogue the function pins `sp - 32`, `s0 = fp`, `s1 = reent` and `s2` (the
result so far) and holds `s3`–`s11` (`Body`, a `StdioFrame.Frame`). Each
block, call and returned callee is one step of that state; the flush is a
premise of the composition (`FlushCall`), discharged per stream from
`StdioReturned`.
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioFclose
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives VsaIris.Inst
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif)
open OCaml.Vm.Boot.Startup (NativeFrame)
open OCaml.Vm.Primitives.ExitPath (KeepCtx ExitOk exitReads)
open OCaml.Vm.Primitives.Uncaught.StdioReturned
open OCaml.Vm.Primitives.Uncaught.StdioFrame (Frame)
open OCaml.Vm.Primitives.Uncaught.StdioFlush (stdinFile stdoutFile stderrFile)
open OCaml.Vm.Primitives.Uncaught.StdioClose (fdSlot fdSlot_toNat FdLive frame_nat frame_word frame_callee
  frame_outside)

/-- `_fclose_r`'s pinned registers: the frame 32 bytes down, `s0 = fp`,
`s1 = reent`, `s2` (the result so far). -/
def bodyPins (sp fp reent s2 : BitVec 64) : GRegs :=
  [(2, sp + 18446744073709551584#64), (8, fp), (9, reent), (18, s2)]

theorem bodyPins_keys (sp fp reent s2 : BitVec 64) : keysG (bodyPins sp fp reent s2) = [2, 8, 9, 18] := rfl

/-- `s3`–`s11`, held as after the prologue. -/
abbrev BodyHold (k : Nat) : Prop := 19 ≤ k ∧ k ≤ 27

/-- `_fclose_r`'s state between its prologue and epilogue, relative to `b`
(a `Frame`). -/
abbrev Body (b : Config) (sp fp reent : BitVec 64) (keep : Nat → Prop) (s2 : BitVec 64) :=
  Frame b keep (bodyPins sp fp reent s2) BodyHold

namespace Body
variable {b : Config} {sp0 fp reent v : BitVec 64} {keep : Nat → Prop}

theorem sp {c : Config} (h : Body b sp0 fp reent keep v c) : gprGet c.σ 2 = some (sp0 + 18446744073709551584#64) :=
  h.pin rfl
theorem s0 {c : Config} (h : Body b sp0 fp reent keep v c) : gprGet c.σ 8 = some fp := h.pin rfl
theorem s1 {c : Config} (h : Body b sp0 fp reent keep v c) : gprGet c.σ 9 = some reent := h.pin rfl
theorem s2 {c : Config} (h : Body b sp0 fp reent keep v c) : gprGet c.σ 18 = some v := h.pin rfl
theorem high {c : Config} (h : Body b sp0 fp reent keep v c) (k : Nat) (lo : 19 ≤ k) (hi : k ≤ 27) :
    gprGet c.σ k = gprGet b.σ k :=
  h.held k (by omega) (by omega) ⟨lo, hi⟩

theorem leaf {c : Config} (h : Body b sp0 fp reent keep v c) : LeafInput (regsAt c 1) c := Frame.leaf h

theorem reg {c : Config} (h : Body b sp0 fp reent keep v c) (n : Nat) (hn : n ∈ exitReads) :
    gprGet c.σ n = some (regsAt c n) :=
  Frame.reg h n hn

theorem mono {keep' : Nat → Prop} {c : Config} (h : Body b sp0 fp reent keep v c) (sub : ∀ x, keep' x → keep x) :
    Body b sp0 fp reent keep' v c :=
  Frame.mono h sub

/-- A generated block that writes none of the body's registers but possibly
`s2`, and no kept byte. -/
theorem stepS2 {c d : Config} {writes : List Nat} {log : List WEntry} {pc value s2' : BitVec 64} {regs : GRegs}
    (h : Body b sp0 fp reent keep v c) (post : WriteRegistersPost writes log c pc value regs d)
    (out : ∀ x, keep x → OutL log x) (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (avoid : ∀ n ∈ writes, n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 8 ∧ n ≠ 9 ∧ (n < 19 ∨ 27 < n))
    (s18 : gprGet d.σ 18 = some s2') : Body b sp0 fp reent keep s2' d :=
  have fr (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ writes) : gprGet d.σ n = gprGet c.σ n :=
    post.toEffectPost.gpr_frame keys n lo hi out
  Frame.stepTo h post out keys cover (fun n m => ⟨(avoid n m).1, by have := (avoid n m).2.2.2.2; omega⟩)
    ⟨(fr 2 (by decide) (by decide) fun m => (avoid 2 m).2.1 rfl).trans (Body.sp h),
      (fr 8 (by decide) (by decide) fun m => (avoid 8 m).2.2.1 rfl).trans (Body.s0 h),
      (fr 9 (by decide) (by decide) fun m => (avoid 9 m).2.2.2.1 rfl).trans (Body.s1 h), s18, trivial⟩

/-- A generated block that writes none of the body's registers and no kept byte. -/
theorem step {c d : Config} {writes : List Nat} {log : List WEntry} {pc value : BitVec 64} {regs : GRegs}
    (h : Body b sp0 fp reent keep v c) (post : WriteRegistersPost writes log c pc value regs d)
    (out : ∀ x, keep x → OutL log x) (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (avoid : ∀ n ∈ writes, n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 8 ∧ n ≠ 9 ∧ (n < 18 ∨ 27 < n)) : Body b sp0 fp reent keep v d :=
  h.stepS2 post out keys cover (fun n m => by have := avoid n m; omega)
    ((post.toEffectPost.gpr_frame keys 18 (by decide) (by decide) fun m => by
      have := (avoid 18 m).2.2.2.2; omega).trans (Body.s2 h))

/-- A direct call: only `ra` changes, to the aligned link. -/
theorem call {c d : Config} {target value link : BitVec 64} {regs : GRegs} (h : Body b sp0 fp reent keep v c)
    (post : RegistersPost [1] c.σ.mem c target value ((1, link) :: regs) d) (al : link.toNat % 4 = 0) :
    Body b sp0 fp reent keep v d :=
  Frame.call h post al (by decide) (by rw [bodyPins_keys]; decide)

/-- A returned callee that kept every byte of `keep`. -/
theorem returned {c d : Config} {ra : BitVec 64} {K : Nat → Prop} (h : Body b sp0 fp reent keep v c)
    (r : Returned ra K c d) (al : ra.toNat % 4 = 0) (sub : ∀ x, keep x → K x) : Body b sp0 fp reent keep v d :=
  Frame.returned h r al sub (by
    intro n hn
    simp only [bodyPins, keysG, List.mem_cons, List.not_mem_nil, or_false] at hn
    unfold CalleeKept; omega) fun n hn => Or.inr (Or.inr (Or.inr ⟨by omega, hn.2⟩))

/-- A direct call whose callee returns to the link in the body's state. -/
theorem callThen {c : Config} {call : CallInstr} (h : Body b sp0 fp reent keep v c) (shape : CallShape call)
    (decode : CallDecode call) (pins : CallPins call c) (al : call.link.toNat % 4 = 0)
    (callee : ∀ d, Body b sp0 fp reent keep v d → gprGet d.σ 1 = some call.link →
      FnSummary call.target (fun e => e = d) (fun e => Body b sp0 fp reent keep v e ∧ PCAt call.link e)) :
    FnSummary call.pc (fun e => e = c) (fun e => Body b sp0 fp reent keep v e ∧ PCAt call.link e) :=
  Frame.callThen h shape decode pins al (by decide) (by rw [bodyPins_keys]; decide) callee

end Body

/-- The `__retarget_lock_*_recursive` leaves (all `ret`) from the body. -/
theorem lockLeaf {b c : Config} {sp fp reent s2 r t : BitVec 64} {keep : Nat → Prop}
    (h : Body b sp fp reent keep s2 c) (raReg : gprGet c.σ 1 = some r)
    (leaf : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ [(1, R 1), (10, R 10)] →
      FnSummary t (fun d => d = c) (WriteRegistersPost [] [] c (R 1) (R 10) [(1, R 1), (10, R 10)])) :
    FnSummary t (fun d => d = c) (fun d => Body b sp fp reent keep s2 d ∧ PCAt r d) :=
  StdioFrame.lockLeaf h raReg (by rw [bodyPins_keys]; decide) leaf

/-- `__sfp_lock_acquire`/`__sfp_lock_release` from the body. -/
theorem sfpTail {b c : Config} {sp fp reent s2 r e t v : BitVec 64} {keep : Nat → Prop} {regs : GRegs}
    (h : Body b sp fp reent keep s2 c) (raReg : gprGet c.σ 1 = some r)
    (enter : FnSummary e (fun d => d = c) (WriteRegistersPost [10] [] c t v regs)) (cover : 10 ∈ keysG regs)
    (leaf : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ [(1, R 1), (10, R 10)] →
      FnSummary t (fun d => d = c) (WriteRegistersPost [] [] c (R 1) (R 10) [(1, R 1), (10, R 10)])) :
    FnSummary e (fun d => d = c) (fun d => Body b sp fp reent keep s2 d ∧ PCAt r d) :=
  StdioFrame.sfpTail h raReg (by rw [bodyPins_keys]; decide) (by decide) enter cover leaf

/-- `_fclose_r`'s saves: `ra` and `s0`–`s2` in its 32-byte frame. -/
def saveLog (sp ra s0 s1 s2 : BitVec 64) : List WEntry :=
  [((sp - 32#64 + 24#64).toNat, 8, ra), ((sp - 32#64).toNat, 8, s2),
    ((sp + 18446744073709551584#64 + 16#64).toNat, 8, s0), ((sp + 18446744073709551584#64 + 8#64).toNat, 8, s1)]

/-- Memory outside `_fclose_r`'s own frame. -/
def Out32 (sp : BitVec 64) (a : Nat) : Prop := a < sp.toNat - 32 ∨ sp.toNat ≤ a

/-- After the prologue (at `0x8004ce8c`): the body's state relative to here,
the frame holding `ra` and `s0`–`s2`, everything else as at the call. -/
structure Saved (c : Config) (sp ra s0 s1 s2 fp reent : BitVec 64) (d : Config) : Prop where
  body : Body d sp fp reent (fun _ => True) s2 d
  a0 : gprGet d.σ 10 = some reent
  ctx : KeepCtx (Out32 sp) c d
  memory : d.σ.mem = writeLog c.σ.mem (saveLog sp ra s0 s1 s2)
  high : ∀ k, 19 ≤ k → k ≤ 27 → gprGet d.σ k = gprGet c.σ k
  gprs : GprsKept c d

theorem sp32 (sp : BitVec 64) : sp + 18446744073709551584#64 = sp - 32#64 := by
  rw [BitVec.sub_eq_add_neg]; rfl

/-- **`_fclose_r`'s prologue**: the saves; `s0 = fp`, `s1 = reent`. -/
theorem fclose_save {ra sp s0 s1 s2 fp reent : BitVec 64} {c : Config} (h : LeafInput ra c) (ok : ExitOk c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s1r : gprGet c.σ 9 = some s1)
    (s2r : gprGet c.σ 18 = some s2) (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some fp)
    (frame : NativeFrame sp 32) (reentNz : reent ≠ 0#64) (fpNz : fp ≠ 0#64) :
    FnSummary 0x8004ce68#64 (fun d => d = c)
      (fun d => PCAt 0x8004ce8c#64 d ∧ Saved c sp ra s0 s1 s2 fp reent d) := by
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have r8 := regsAt_of s0r
  have r9 := regsAt_of s1r
  have r10 := regsAt_of a0
  have r11 := regsAt_of a1
  have r18 := regsAt_of s2r
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have e0 : sp - 32#64 = sp - BitVec.ofNat 64 32 + BitVec.ofNat 64 0 := by simp
  have n24 := frame_nat (k := 32) (off := 24) frame (by decide) (by decide)
  have n16 := frame_nat (k := 32) (off := 16) frame (by decide) (by decide)
  have n8 := frame_nat (k := 32) (off := 8) frame (by decide) (by decide)
  have n0 : (sp - 32#64).toNat = sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  have f24 := frame_outside (k := 32) (off := 24) (w := 8) (v := ra) frame (by decide) (by decide)
  have f0 := frame_outside (k := 32) (off := 0) (w := 8) (v := s2) frame (by decide) (by decide)
  have f16 := frame_outside (k := 32) (off := 16) (w := 8) (v := s0) frame (by decide) (by decide)
  have f8 := frame_outside (k := 32) (off := 8) (w := 8) (v := s1) frame (by decide) (by decide)
  rw [← e0] at f0
  apply summary_bind (Fclose.pro_fast c (regsAt c) (by rw [r1]; exact h)
    (by simp only [Fclose.pro_input, GHolds]
        exact ⟨gpr_some (gpr_some_of h.raReg), gpr_some (gpr_some_of sp0), gpr_some (gpr_some_of a0),
          gpr_some (gpr_some_of a1), gpr_some (gpr_some_of s2r), trivial⟩)
    (by rw [r2, sp32]; exact frame_word (k := 32) (off := 24) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [r2, sp32, e0]; exact frame_word (k := 32) (off := 0) frame (by decide) (by decide) (by decide) (by decide))
    (by simp only [Fclose.proLog, r1, r2, r18]; exact ⟨⟨f24.1.1, f0.1.1, trivial⟩, ⟨f24.2.1, f0.2.1, trivial⟩⟩)
    (by rw [r11]; simpa [guardB] using fpNz)) (fun _ p => p.pc)
  intro c1 p1
  have o1 := p1.regs
  simp only [Fclose.pro_regs, r1, r2, r10, r11, r18, GHolds] at o1
  obtain ⟨g2, g1, g10, g11, -, -⟩ := o1
  have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [2]) : gprGet c1.σ n = gprGet c.σ n :=
    p1.gpr_frame (by decide) n lo hi out
  have g8 := (k1 8 (by decide) (by decide) (by decide)).trans s0r
  have g9 := (k1 9 (by decide) (by decide) (by decide)).trans s1r
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of g1]; exact ⟨p1.good, p1.image, p1.minstret, g1, h.aligned, p1.tick⟩
  apply (Fclose.reent_fast c1 (regsAt c1) l1
    (by simp only [Fclose.reent_input, GHolds]
        exact ⟨gpr_some (gpr_some_of g2), gpr_some (gpr_some_of g8), gpr_some (gpr_some_of g9),
          gpr_some (gpr_some_of g10), gpr_some (gpr_some_of g11), trivial⟩)
    (by rw [regsAt_of g2, sp32]; exact frame_word (k := 32) (off := 16) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [regsAt_of g2, sp32]; exact frame_word (k := 32) (off := 8) frame (by decide) (by decide) (by decide) (by decide))
    (by simp only [Fclose.reentLog, regsAt_of g2, regsAt_of g8, regsAt_of g9, sp32]
        exact ⟨⟨f16.1.1, f8.1.1, trivial⟩, ⟨f16.2.1, f8.2.1, trivial⟩⟩)
    (by rw [regsAt_of g10]; simpa [guardB] using reentNz)).weaken (fun _ e => e)
  intro c2 p2
  have o2 := p2.regs
  simp only [Fclose.reent_regs, regsAt_of g2, regsAt_of g10, regsAt_of g11, GHolds] at o2
  obtain ⟨h9, h8, h2, h10, -, -⟩ := o2
  have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [8, 9]) : gprGet c2.σ n = gprGet c1.σ n :=
    p2.gpr_frame (by decide) n lo hi out
  have h1 := (k2 1 (by decide) (by decide) (by decide)).trans g1
  have log1 : Fclose.proLog (regsAt c) (Fclose.pro_loads c.σ.mem (regsAt c)) =
      [((sp - 32#64 + 24#64).toNat, 8, ra), ((sp - 32#64).toNat, 8, s2)] := by
    simp only [Fclose.proLog, r1, r2, r18]
  have log2 : Fclose.reentLog (regsAt c1) (Fclose.reent_loads c1.σ.mem (regsAt c1)) =
      [((sp + 18446744073709551584#64 + 16#64).toNat, 8, s0), ((sp + 18446744073709551584#64 + 8#64).toNat, 8, s1)] := by
    simp only [Fclose.reentLog, regsAt_of g2, regsAt_of g8, regsAt_of g9]
  have ctx : KeepCtx (Out32 sp) c c2 :=
    ((KeepCtx.refl ok h.image h.minstret).step p1 (fun x hx => by
      rw [log1]; simp only [OutL, n24, n0, and_true]; unfold Out32 at hx; omega) (by decide) (by simp [Fclose.pro_regs, keysG])).step p2
      (fun x hx => by rw [log2]; simp only [OutL, sp32, n16, n8, and_true]; unfold Out32 at hx; omega) (by decide)
      (by simp [Fclose.reent_regs, keysG])
  have high (k : Nat) (lo : 19 ≤ k) (hi : k ≤ 27) : gprGet c2.σ k = gprGet c.σ k :=
    (k2 k (by omega) (by omega) (by simp; omega)).trans (k1 k (by omega) (by omega) (by simp; omega))
  have h18 := (k2 18 (by decide) (by decide) (by decide)).trans ((k1 18 (by decide) (by decide) (by decide)).trans s2r)
  refine ⟨p2.pc, ⟨Frame.start ctx.ok p2.image p2.minstret ⟨ra, h1, h.aligned⟩ ⟨h2, h8, h9, h18, trivial⟩, h10, ctx, ?_,
    high, p1.kept.trans p2.kept⟩⟩
  rw [p2.memory, log2, p1.memory, log1, saveLog]
  exact (writeLog_append _ _ _).symm

/-- `__sclose`, the standard streams' close function. -/
def scloseFn : BitVec 64 := 0x80040184#64

/-- **What `_fclose_r` reads of a standard stream** (and of `reent`): a live,
unlocked, non-string stream without buffers, closed by `__sclose` on its own
cookie, with a live console descriptor. -/
structure Closable (m : Std.ExtHashMap Nat (BitVec 8)) (reent fp : BitVec 64) : Prop where
  cleanupR : ReadWindow (reent + 72#64) 8
  cleanup : bytesVal .ld (read8 m (reent + 72#64).toNat) ≠ 0#64
  flags2R : ReadWindow (fp + 176#64) 4
  flags2 : bytesVal .lw (read8 m (fp + 176#64).toNat) &&& 1#64 = 0#64
  flagsR : ReadWindow (fp + 16#64) 2
  flagsW : WriteWindow (fp + 16#64) 2
  flagsOut : ImageOutside [((fp + 16#64).toNat, 2, 0#64)]
  live : bytesVal .lh (read8 m (fp + 16#64).toNat) ≠ 0#64
  notStr : bytesVal .lh (read8 m (fp + 16#64).toNat) &&& 512#64 = 0#64
  lockR : ReadWindow (fp + 160#64) 8
  closeR : ReadWindow (fp + 80#64) 8
  close : bytesVal .ld (read8 m (fp + 80#64).toNat) = scloseFn
  cookieR : ReadWindow (fp + 48#64) 8
  cookie : bytesVal .ld (read8 m (fp + 48#64).toNat) = fp
  fileR : ReadWindow (fp + 18#64) 2
  fd : FdLive m (bytesVal .lh (read8 m (fp + 18#64).toNat))
  ubR : ReadWindow (fp + 88#64) 8
  ub : bytesVal .ld (read8 m (fp + 88#64).toNat) = 0#64
  lbR : ReadWindow (fp + 120#64) 8
  lb : bytesVal .ld (read8 m (fp + 120#64).toNat) = 0#64

/-- Where the stream and `reent` lie: globals below the heap's end, the
stream above the descriptor table and `errno`. -/
structure Placed (reent fp : BitVec 64) : Prop where
  fileEnd : fp.toNat + 184 ≤ Vsa.Sim.DlHeap.heapEnd
  aboveFds : 0x80065098 ≤ fp.toNat
  reentEnd : reent.toNat + 80 ≤ Vsa.Sim.DlHeap.heapEnd
  reentNz : reent ≠ 0#64

theorem Placed.fpNz {reent fp : BitVec 64} (h : Placed reent fp) : fp ≠ 0#64 := by
  intro e; have := h.aboveFds; rw [e] at this; simp at this

theorem Placed.fpN {reent fp : BitVec 64} (h : Placed reent fp) (k : Nat) (hk : k ≤ 184) :
    (fp + BitVec.ofNat 64 k).toNat = fp.toNat + k := by
  have := h.fileEnd; simp only [Vsa.Sim.DlHeap.heapEnd] at this
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- Bytes `_fclose_r` on `fp` (descriptor `fd`) leaves alone: outside its and
its callees' 80 bytes of stack, the stream's first 18 bytes, `errno`, and the
descriptor's slot. -/
def FcloseKeep (sp fp fd : BitVec 64) (a : Nat) : Prop :=
  (a < sp.toNat - 80 ∨ sp.toNat ≤ a) ∧ (a < fp.toNat ∨ fp.toNat + 18 ≤ a) ∧
    (a < 0x80064d48 ∨ 0x80064d48 + 4 ≤ a) ∧ (a < (fdSlot fd).toNat ∨ (fdSlot fd).toNat + 4 ≤ a)

/-- After the flush: kept outside the flush's frame and the stream's first 18 bytes. -/
def FlushPhase (sp fp : BitVec 64) (a : Nat) : Prop :=
  (a < sp.toNat - 80 ∨ sp.toNat - 32 ≤ a) ∧ (a < fp.toNat ∨ fp.toNat + 18 ≤ a)

/-- After the close: also outside `errno` and the descriptor's slot. -/
def ClosePhase (sp fp fd : BitVec 64) (a : Nat) : Prop :=
  FlushPhase sp fp a ∧ (a < 0x80064d48 ∨ 0x80064d48 + 4 ≤ a) ∧
    (a < (fdSlot fd).toNat ∨ (fdSlot fd).toNat + 4 ≤ a)

/-- **The stream's flush at `_fclose_r`'s call site**: from the call (`a0 =
reent`, `a1 = fp`, memory outside `_fclose_r`'s frame as at `c`), back at
`0x8004ceb8` with `0`, the bytes of `FlushKeep` kept, and the flags it leaves
without `__SMBF`. Supplied per stream from `StdioReturned`. -/
def FlushCall (c : Config) (sp fp reent : BitVec 64) : Prop :=
  ∀ c1 : Config, LeafInput 0x8004ceb8#64 c1 → ExitOk c1 →
    gprGet c1.σ 2 = some (sp + 18446744073709551584#64) → gprGet c1.σ 8 = some fp → gprGet c1.σ 9 = some reent →
    gprGet c1.σ 10 = some reent → gprGet c1.σ 11 = some fp → KeepCtx (Out32 sp) c c1 →
    FnSummary 0x8003e4f4#64 (fun d => d = c1) (Flushed 0x8004ceb8#64 (sp + 18446744073709551584#64) fp c1)

/-- **`_fclose_r` up to the flush**: `reent->__cleanup` set, the stream
unlocked-by-flag, not a string, live; the lock taken; `a0 = reent`, `a1 = fp`
at the `jal __sflush_r`. -/
theorem fclose_open {ra sp s0 s1 s2 fp reent : BitVec 64} {c c2 : Config}
    (S : Saved c sp ra s0 s1 s2 fp reent c2) (file : Closable c.σ.mem reent fp) (pl : Placed reent fp)
    (frame : NativeFrame sp 80) :
    FnSummary 0x8004ce8c#64 (fun d => d = c2)
      (fun d => PCAt Fclose.flush_call.pc d ∧ Body c2 sp fp reent (fun _ => True) s2 d ∧
        gprGet d.σ 10 = some reent ∧ gprGet d.σ 11 = some fp) := by
  have lo := frame.lower
  have fl := pl.fileEnd
  have rl := pl.reentEnd
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo fl rl
  have rd {d : Config} (bd : Body c2 sp fp reent (fun _ => True) s2 d) (a : Nat) (ha : a + 8 ≤ sp.toNat - 32) :
      read8 d.σ.mem a = read8 c.σ.mem a :=
    (bd.ctx.read fun _ _ => trivial).trans (S.ctx.read fun i _ => Or.inl (by omega))
  have rdF {d : Config} (bd : Body c2 sp fp reent (fun _ => True) s2 d) (k : Nat) (hk : k + 8 ≤ 184) :
      read8 d.σ.mem (fp + BitVec.ofNat 64 k).toNat = read8 c.σ.mem (fp + BitVec.ofNat 64 k).toNat :=
    rd bd _ (by rw [pl.fpN k (by omega)]; omega)
  have b2 := S.body
  -- `reent->__cleanup` is set
  apply summary_bind (Fclose.cleanup_fast c2 (regsAt c2) b2.leaf
    (by simp only [Fclose.cleanup_input, GHolds]; exact ⟨b2.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of S.a0]; exact file.cleanupR)
    (by
      simp only [Fclose.cleanup_loads, List.getD_cons_zero, regsAt_of S.a0]
      rw [rd b2 _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
      simpa [guardB] using file.cleanup)) (fun _ p => p.pc)
  intro c3 p3
  have b3 := b2.step p3 (fun _ _ => trivial) (by decide) (by simp [Fclose.cleanup_regs, keysG]) (by decide)
  -- `_flags2 & __SNLK` clear; the flags in `a4`
  apply summary_bind (Fclose.flags2_fast c3 (regsAt c3) b3.leaf
    (by simp only [Fclose.flags2_input, GHolds]; exact ⟨b3.reg 8 (by decide), b3.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b3.s0]; exact file.flags2R) (by rw [regsAt_of b3.s0]; exact file.flagsR)
    (by
      simp only [Fclose.flags2_loads, List.getD_cons_zero, regsAt_of b3.s0]
      rw [rdF b3 176 (by decide)]
      simpa [guardB] using file.flags2)) (fun _ p => p.pc)
  intro c4 p4
  have b4 := b3.step p4 (fun _ _ => trivial) (by decide) (by simp [Fclose.flags2_regs, keysG]) (by decide)
  have g14 : gprGet c4.σ 14 = some (bytesVal .lh (read8 c.σ.mem (fp + 16#64).toNat)) := by
    have := gholds_lookup (n := 14) _ p4.regs rfl
    simp only [Fclose.flags2_loads, List.getD_cons_zero, List.getD_cons_succ, regsAt_of b3.s0] at this
    rw [this, rdF b3 16 (by decide)]
  -- not a string stream
  apply summary_bind (Fclose.sstr_fast c4 (regsAt c4) b4.leaf
    (by simp only [Fclose.sstr_input, GHolds]; exact ⟨b4.reg 10 (by decide), gpr_some (gpr_some_of g14), trivial⟩)
    (by rw [regsAt_of g14]; simpa [guardB] using file.notStr)) (fun _ p => p.pc)
  intro c5 p5
  have b5 := b4.step p5 (fun _ _ => trivial) (by decide) (by simp [Fclose.sstr_regs, keysG]) (by decide)
  -- `__lock_acquire_recursive(fp->_lock)`
  apply summary_bind (Fclose.lock_fast c5 (regsAt c5) b5.leaf
    (by simp only [Fclose.lock_input, GHolds]
        exact ⟨b5.reg 1 (by decide), b5.reg 8 (by decide), b5.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b5.s0]; exact file.lockR)) (fun _ p => p.pc)
  intro c6 p6
  have b6 := b5.step p6 (fun _ _ => trivial) (by decide) (by simp [Fclose.lock_regs, keysG]) (by decide)
  apply summary_bind (pc := 0x8004cfa0#64) (b6.callThen Fclose.lock_call_shape Fclose.lock_call_decode
    (Fclose.lock_call_pins b6.ctx.image) (by decide) fun d bd raR => by
      rw [Fclose.lock_call_target]; exact lockLeaf bd raR ExitPath.RetargetLockAcquireRecursive.leaf_fast)
    (fun _ p => by have := p.2; rwa [show Fclose.lock_call.link = 0x8004cfa0#64 by decide] at this)
  intro c8 h8
  have b8 := h8.1
  -- the stream is live
  apply summary_bind (Fclose.live_fast c8 (regsAt c8) b8.leaf
    (by simp only [Fclose.live_input, GHolds]; exact ⟨b8.reg 8 (by decide), b8.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b8.s0]; exact file.flagsR)
    (by
      simp only [Fclose.live_loads, List.getD_cons_zero, regsAt_of b8.s0]
      rw [rdF b8 16 (by decide)]
      simpa [guardB] using file.live)) (fun _ p => p.pc)
  intro c9 p9
  have b9 := b8.step p9 (fun _ _ => trivial) (by decide) (by simp [Fclose.live_regs, keysG]) (by decide)
  -- the flush's arguments
  apply (Fclose.flush_fast c9 (regsAt c9) b9.leaf
    (by simp only [Fclose.flush_input, GHolds]
        exact ⟨b9.reg 1 (by decide), b9.reg 8 (by decide), b9.reg 9 (by decide), b9.reg 10 (by decide), trivial⟩)).weaken
    (fun _ e => e)
  intro c10 p10
  have o := p10.regs
  simp only [Fclose.flush_regs, regsAt_of b9.s0, regsAt_of b9.s1, GHolds] at o
  exact ⟨p10.pc, b9.step p10 (fun _ _ => trivial) (by decide) (by simp [Fclose.flush_regs, keysG]) (by decide),
    o.1, o.2.1⟩

/-- A returned call left a kept word as it was. -/
theorem returned_read {ra : BitVec 64} {K : Nat → Prop} {c d : Config} (r : Returned ra K c d) {a : Nat}
    (kept : ∀ i, i < 8 → K (a + i)) : read8 d.σ.mem a = read8 c.σ.mem a :=
  ConsoleWrite.read8_same fun i hi => r.kept _ (kept i hi)

/-- `FdLive` from equal reads of `fs_ready` and the slot. -/
theorem fdLive_of_read {m m' : Std.ExtHashMap Nat (BitVec 8)} {fd : BitVec 64} (h : FdLive m fd)
    (ready : read8 m' (0x80064918#64).toNat = read8 m (0x80064918#64).toNat)
    (slot : read8 m' (fdSlot fd).toNat = read8 m (fdSlot fd).toNat) : FdLive m' fd :=
  ⟨h.small, by rw [ready]; exact h.ready, by rw [slot]; exact h.live, by rw [slot]; exact h.notFile⟩

theorem spN {sp : BitVec 64} (frame : NativeFrame sp 80) :
    (sp + 18446744073709551584#64).toNat = sp.toNat - 32 := by
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  rw [sp32, BitVec.toNat_sub]; simp; omega

/-- **`_fclose_r`'s flush and close**: `__sflush_r(reent, fp)` returns 0
(`s2`); the close function is `__sclose`, called on the stream's cookie,
returns 0 too. -/
theorem fclose_flush {ra sp s0 s1 s2 fp reent : BitVec 64} {c c2 c10 : Config}
    (S : Saved c sp ra s0 s1 s2 fp reent c2) (file : Closable c.σ.mem reent fp) (pl : Placed reent fp)
    (frame : NativeFrame sp 80) (flush : FlushCall c sp fp reent)
    (b10 : Body c2 sp fp reent (fun _ => True) s2 c10) (a0r : gprGet c10.σ 10 = some reent)
    (a1r : gprGet c10.σ 11 = some fp) :
    FnSummary Fclose.flush_call.pc (fun d => d = c10)
      (fun d => PCAt 0x8004ced0#64 d ∧
        Body c2 sp fp reent (ClosePhase sp fp (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) 0#64 d ∧
        gprGet d.σ 10 = some 0#64 ∧ bytesVal .lhu (read8 d.σ.mem (fp + 16#64).toNat) &&& 128#64 = 0#64) := by
  have lo := frame.lower
  have fl := pl.fileEnd
  have ab := pl.aboveFds
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo fl
  have sN := spN frame
  generalize hfd : bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat) = fd
  have fdOk : FdLive c.σ.mem fd := hfd ▸ file.fd
  have sm := fdOk.small
  have slotN := fdSlot_toNat sm
  -- reads of the stream's fields (offset 18 on) and of the low globals survive the flush
  have rdF {d : Config} {v : BitVec 64} (bd : Body c2 sp fp reent (FlushPhase sp fp) v d) (k : Nat) (hk : 18 ≤ k) (hk' : k + 8 ≤ 184) :
      read8 d.σ.mem (fp + BitVec.ofNat 64 k).toNat = read8 c.σ.mem (fp + BitVec.ofNat 64 k).toNat := by
    rw [pl.fpN k (by omega)]
    exact (bd.ctx.read fun i _ => ⟨Or.inl (by omega), Or.inr (by omega)⟩).trans
      (S.ctx.read fun i _ => Or.inl (by omega))
  have rdLow {d : Config} {v : BitVec 64} (bd : Body c2 sp fp reent (FlushPhase sp fp) v d) (a : Nat) (ha : a + 8 ≤ fp.toNat) :
      read8 d.σ.mem a = read8 c.σ.mem a :=
    (bd.ctx.read fun i _ => ⟨Or.inl (by omega), Or.inl (by omega)⟩).trans (S.ctx.read fun i _ => Or.inl (by omega))
  -- `jal __sflush_r`
  apply summary_bind (call_registers_summary Fclose.flush_call_shape Fclose.flush_call_decode c10
    (Fclose.flush_call_pins b10.ctx.image) b10.ctx.ok.good b10.ctx.image b10.ctx.ok.tick b10.ctx.minstret
    [(10, reent), (11, fp)] ⟨a0r, a1r, trivial⟩ (by change KeysOK [10, 11]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl) (fun _ q => q.pc)
  intro c11 q11
  have b11 := b10.call q11 (by decide)
  have link11 : gprGet c11.σ 1 = some 0x8004ceb8#64 := gholds_lookup (n := 1) _ q11.regs rfl
  rw [Fclose.flush_call_target]
  apply summary_bind (flush c11 (b11.ctx.leaf link11 (by decide)) b11.ctx.ok b11.sp b11.s0 b11.s1
    (gholds_lookup (n := 10) _ q11.regs rfl) (gholds_lookup (n := 11) _ q11.regs rfl)
    (S.ctx.trans (b11.ctx.mono fun _ _ => trivial))) (fun _ p => p.1.pc)
  intro c12 h12
  obtain ⟨r12, smbf12⟩ := h12
  have b12 := (b11.mono (keep' := FlushPhase sp fp) fun _ _ => trivial).returned r12 (by decide) fun x hx => by
    unfold FlushPhase at hx; unfold FlushKeep; rw [sN]; omega
  -- `s2 = 0`; the close function is `__sclose`
  have closeAt := rdF b12 80 (by decide) (by decide)
  apply summary_bind (Fclose.closeFn_fast c12 (regsAt c12) b12.leaf
    (by simp only [Fclose.closeFn_input, GHolds]; exact ⟨b12.reg 8 (by decide), b12.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b12.s0]; exact file.closeR)
    (by simp only [Fclose.closeFn_loads, List.getD_cons_zero, regsAt_of b12.s0]
        rw [closeAt, file.close]; decide)) (fun _ p => p.pc)
  intro c13 p13
  have b13 := b12.stepS2 p13 (fun _ _ => trivial) (by decide) (by simp [Fclose.closeFn_regs, keysG]) (by decide)
    (by have := gholds_lookup (n := 18) _ p13.regs rfl; rwa [regsAt_of r12.result] at this)
  have g15 : gprGet c13.σ 15 = some scloseFn := by
    have := gholds_lookup (n := 15) _ p13.regs rfl
    simp only [Fclose.closeFn_loads, List.getD_cons_zero, regsAt_of b12.s0] at this
    rw [this, closeAt, file.close]
  -- `a0 = reent`, `a1 = fp->_cookie`
  have cookieAt := rdF b13 48 (by decide) (by decide)
  apply summary_bind (Fclose.close_fast c13 (regsAt c13) b13.leaf
    (by simp only [Fclose.close_input, GHolds]
        exact ⟨b13.reg 1 (by decide), b13.reg 8 (by decide), b13.reg 9 (by decide), b13.reg 10 (by decide),
          gpr_some (gpr_some_of g15), trivial⟩)
    (by rw [regsAt_of b13.s0]; exact file.cookieR)) (fun _ p => p.pc)
  intro c14 p14
  have b14 := b13.step p14 (fun _ _ => trivial) (by decide) (by simp [Fclose.close_regs, keysG]) (by decide)
  have o14 := p14.regs
  simp only [Fclose.close_regs, Fclose.close_loads, List.getD_cons_zero, regsAt_of b13.s0, regsAt_of b13.s1,
    regsAt_of g15, cookieAt, file.cookie, GHolds] at o14
  obtain ⟨h10, h11, -, -, -, h15, -⟩ := o14
  -- `jalr a5`
  apply summary_bind (indirect_registers_summary Fclose.close_call_shape Fclose.close_call_decode c14
    (Fclose.close_call_pins b14.ctx.image) b14.ctx.ok.good b14.ctx.image b14.ctx.ok.tick b14.ctx.minstret
    [(15, scloseFn), (10, reent), (11, fp)] ⟨h15, h10, h11, trivial⟩ (by change KeysOK [15, 10, 11]; decide)
    (by simp [KeysAvoidRa, keysG]) scloseFn rfl (by decide) rfl) (fun _ q => q.pc)
  intro c15 q15
  have b15 := b14.call q15 (by decide)
  have link15 : gprGet c15.σ 1 = some 0x8004ced0#64 := gholds_lookup (n := 1) _ q15.regs rfl
  rw [show Fclose.close_call.target scloseFn = 0x80040184#64 by decide]
  -- `__sclose(reent, fp)`
  have fdAt : read8 c15.σ.mem (fp + 18#64).toNat = read8 c.σ.mem (fp + 18#64).toNat :=
    rdF b15 18 (by decide) (by decide)
  have fd15 : bytesVal .lh (read8 c15.σ.mem (fp + 18#64).toNat) = fd := by rw [fdAt, hfd]
  have S16 := sclose_returned (b15.ctx.leaf link15 (by decide)) b15.sp b15.s0
    (gholds_lookup (n := 10) _ q15.regs rfl) (gholds_lookup (n := 11) _ q15.regs rfl)
    (frame_callee (front := 32) (size := 48) frame (by decide) _ (by decide)) file.fileR
    (by
      rw [fd15]
      exact fdLive_of_read fdOk (rdLow b15 _ (by simp only [BitVec.toNat_ofNat]; omega))
        (rdLow b15 _ (by rw [slotN]; omega)))
  rw [fd15] at S16
  apply S16.weaken (fun _ e => e)
  intro c16 r16
  have b16 := (b15.mono (keep' := ClosePhase sp fp fd) fun x hx => hx.1).returned r16 (by decide) fun x hx => by
    obtain ⟨⟨h1, -⟩, h2, h3⟩ := hx
    exact ⟨by rw [sN]; omega, h2, h3⟩
  refine ⟨r16.pc, b16, r16.result, ?_⟩
  -- the flags the flush left survive the close
  have m13 : c13.σ.mem = c12.σ.mem := by rw [p13.memory, Named.NamedValue.wl_nil]
  have m14 : c14.σ.mem = c13.σ.mem := by rw [p14.memory, Named.NamedValue.wl_nil]
  have m15 : c15.σ.mem = c14.σ.mem := q15.memory
  rw [returned_read r16 (a := (fp + 16#64).toNat) fun i _ => by
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pl.fpN 16 (by decide)]
      exact ⟨Or.inl (by rw [sN]; omega), Or.inr (by omega), Or.inr (by rw [slotN]; omega)⟩,
    m15, m14, m13]
  exact smbf12

/-- **`_fclose_r` after the close**: no `__SMBF`, no `ub`/`lb` buffers;
`_flags = 0` under the `__sfp` lock; the stream's lock released and closed;
the epilogue returns `s2 = 0`. -/
theorem fclose_finish {ra sp s0 s1 s2 fp reent : BitVec 64} {c c2 c16 : Config} (ok : ExitOk c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s1r : gprGet c.σ 9 = some s1) (s2r : gprGet c.σ 18 = some s2)
    (raAl : ra.toNat % 4 = 0) (S : Saved c sp ra s0 s1 s2 fp reent c2) (file : Closable c.σ.mem reent fp)
    (pl : Placed reent fp) (frame : NativeFrame sp 80)
    (b16 : Body c2 sp fp reent (ClosePhase sp fp (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) 0#64 c16)
    (a0r : gprGet c16.σ 10 = some 0#64) (smbf : bytesVal .lhu (read8 c16.σ.mem (fp + 16#64).toNat) &&& 128#64 = 0#64) :
    FnSummary 0x8004ced0#64 (fun d => d = c16)
      (Returned ra (FcloseKeep sp fp (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) c) := by
  have lo := frame.lower
  have fl := pl.fileEnd
  have ab := pl.aboveFds
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo fl
  have sN := spN frame
  generalize hfd : bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat) = fd at b16 ⊢
  have sm : fd.toNat < 32 := hfd ▸ file.fd.small
  have slotN := fdSlot_toNat sm
  have rdF {d : Config} (bd : Body c2 sp fp reent (ClosePhase sp fp fd) 0#64 d) (k : Nat) (hk : 18 ≤ k)
      (hk' : k + 8 ≤ 184) :
      read8 d.σ.mem (fp + BitVec.ofNat 64 k).toNat = read8 c.σ.mem (fp + BitVec.ofNat 64 k).toNat := by
    rw [pl.fpN k (by omega)]
    exact (bd.ctx.read fun i _ => ⟨⟨Or.inl (by omega), Or.inr (by omega)⟩, Or.inr (by omega),
      Or.inr (by rw [slotN]; omega)⟩).trans (S.ctx.read fun i _ => Or.inl (by omega))
  -- `_close` returned 0, not -1
  apply summary_bind (Fclose.closed_fast c16 (regsAt c16) b16.leaf
    (by simp only [Fclose.closed_input, GHolds]; exact ⟨b16.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of a0r]; decide)) (fun _ p => p.pc)
  intro c17 p17
  have b17 := b16.step p17 (fun _ _ => trivial) (by decide) (by simp) (by decide)
  -- no `__SMBF`, no `ub`, no `lb`
  apply summary_bind (Fclose.smbf_fast c17 (regsAt c17) b17.leaf
    (by simp only [Fclose.smbf_input, GHolds]; exact ⟨b17.reg 8 (by decide), b17.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b17.s0]; exact file.flagsR)
    (by simp only [Fclose.smbf_loads, List.getD_cons_zero, regsAt_of b17.s0]
        rw [p17.memory, Named.NamedValue.wl_nil]; simpa [guardB] using smbf)) (fun _ p => p.pc)
  intro c18 p18
  have b18 := b17.step p18 (fun _ _ => trivial) (by decide) (by simp [Fclose.smbf_regs, keysG]) (by decide)
  apply summary_bind (Fclose.ub_fast c18 (regsAt c18) b18.leaf
    (by simp only [Fclose.ub_input, GHolds]; exact ⟨b18.reg 8 (by decide), b18.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b18.s0]; exact file.ubR)
    (by simp only [Fclose.ub_loads, List.getD_cons_zero, regsAt_of b18.s0]
        rw [rdF b18 88 (by decide) (by decide)]; simpa [guardB] using file.ub)) (fun _ p => p.pc)
  intro c19 p19
  have b19 := b18.step p19 (fun _ _ => trivial) (by decide) (by simp [Fclose.ub_regs, keysG]) (by decide)
  apply summary_bind (Fclose.lb_fast c19 (regsAt c19) b19.leaf
    (by simp only [Fclose.lb_input, GHolds]; exact ⟨b19.reg 8 (by decide), b19.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b19.s0]; exact file.lbR)
    (by simp only [Fclose.lb_loads, List.getD_cons_zero, regsAt_of b19.s0]
        rw [rdF b19 120 (by decide) (by decide)]; simpa [guardB] using file.lb)) (fun _ p => p.pc)
  intro c20 p20
  have b20 := b19.step p20 (fun _ _ => trivial) (by decide) (by simp [Fclose.lb_regs, keysG]) (by decide)
  -- `__sfp_lock_acquire()`
  apply summary_bind (Fclose.sfpLock_fast c20 (regsAt c20) b20.leaf
    (by simp only [Fclose.sfpLock_input, GHolds]; exact ⟨b20.reg 1 (by decide), b20.reg 10 (by decide), trivial⟩))
    (fun _ p => p.pc)
  intro c21 p21
  have b21 := b20.step p21 (fun _ _ => trivial) (by decide) (by simp) (by decide)
  apply summary_bind (pc := 0x8004cf14#64) (b21.callThen Fclose.sfpLock_call_shape Fclose.sfpLock_call_decode
    (Fclose.sfpLock_call_pins b21.ctx.image) (by decide) fun d bd raR => by
      rw [Fclose.sfpLock_call_target]
      exact sfpTail bd raR (SfpLockAcquire.enter_fast d (regsAt d) bd.leaf
        ⟨bd.reg 1 (by decide), bd.reg 10 (by decide), trivial⟩) (by simp [SfpLockAcquire.enter_regs, keysG])
        ExitPath.RetargetLockAcquireRecursive.leaf_fast)
    (fun _ p => by have := p.2; rwa [show Fclose.sfpLock_call.link = 0x8004cf14#64 by decide] at this)
  intro c24 h24
  have b24 := h24.1
  -- `_flags = 0` (`_flags2 & __SNLK` still clear)
  apply summary_bind (Fclose.clear_fast c24 (regsAt c24) b24.leaf
    (by simp only [Fclose.clear_input, GHolds]; exact ⟨b24.reg 8 (by decide), b24.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b24.s0]; exact file.flags2R) (by rw [regsAt_of b24.s0]; exact file.flagsW)
    (by simp only [Fclose.clearLog, regsAt_of b24.s0]; exact file.flagsOut)
    (by simp only [Fclose.clear_loads, List.getD_cons_zero, regsAt_of b24.s0]
        rw [rdF b24 176 (by decide) (by decide)]; simpa [guardB] using file.flags2)) (fun _ p => p.pc)
  intro c25 p25
  have b25 := b24.step p25 (fun x hx => by
      simp only [Fclose.clearLog, regsAt_of b24.s0, OutL, pl.fpN 16 (by decide), and_true]
      have := hx.1.2; omega)
    (by decide) (by simp [Fclose.clear_regs, keysG]) (by decide)
  -- `__lock_release_recursive(fp->_lock)`
  apply summary_bind (Fclose.unlock_fast c25 (regsAt c25) b25.leaf
    (by simp only [Fclose.unlock_input, GHolds]
        exact ⟨b25.reg 1 (by decide), b25.reg 8 (by decide), b25.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b25.s0]; exact file.lockR)) (fun _ p => p.pc)
  intro c26 p26
  have b26 := b25.step p26 (fun _ _ => trivial) (by decide) (by simp [Fclose.unlock_regs, keysG]) (by decide)
  apply summary_bind (pc := 0x8004cfd0#64) (b26.callThen Fclose.unlock_call_shape Fclose.unlock_call_decode
    (Fclose.unlock_call_pins b26.ctx.image) (by decide) fun d bd raR => by
      rw [Fclose.unlock_call_target]; exact lockLeaf bd raR ExitPath.RetargetLockReleaseRecursive.leaf_fast)
    (fun _ p => by have := p.2; rwa [show Fclose.unlock_call.link = 0x8004cfd0#64 by decide] at this)
  intro c28 h28
  have b28 := h28.1
  apply summary_bind (Fclose.toClose_fast c28 (regsAt c28) b28.leaf
    (by simp only [Fclose.toClose_input, GHolds]; exact ⟨b28.reg 10 (by decide), trivial⟩)) (fun _ p => p.pc)
  intro c29 p29
  have b29 := b28.step p29 (fun _ _ => trivial) (by decide) (by simp) (by decide)
  -- `__lock_close_recursive(fp->_lock)`
  apply summary_bind (Fclose.closeLock_fast c29 (regsAt c29) b29.leaf
    (by simp only [Fclose.closeLock_input, GHolds]
        exact ⟨b29.reg 1 (by decide), b29.reg 8 (by decide), b29.reg 10 (by decide), trivial⟩)
    (by rw [regsAt_of b29.s0]; exact file.lockR)) (fun _ p => p.pc)
  intro c30 p30
  have b30 := b29.step p30 (fun _ _ => trivial) (by decide) (by simp [Fclose.closeLock_regs, keysG]) (by decide)
  apply summary_bind (pc := 0x8004cf2c#64) (b30.callThen Fclose.closeLock_call_shape Fclose.closeLock_call_decode
    (Fclose.closeLock_call_pins b30.ctx.image) (by decide) fun d bd raR => by
      rw [Fclose.closeLock_call_target]; exact lockLeaf bd raR RetargetLockClose.leaf_fast)
    (fun _ p => by have := p.2; rwa [show Fclose.closeLock_call.link = 0x8004cf2c#64 by decide] at this)
  intro c32 h32
  have b32 := h32.1
  -- `__sfp_lock_release()`
  apply summary_bind (Fclose.sfpUnlock_fast c32 (regsAt c32) b32.leaf
    (by simp only [Fclose.sfpUnlock_input, GHolds]; exact ⟨b32.reg 1 (by decide), b32.reg 10 (by decide), trivial⟩))
    (fun _ p => p.pc)
  intro c33 p33
  have b33 := b32.step p33 (fun _ _ => trivial) (by decide) (by simp) (by decide)
  apply summary_bind (pc := 0x8004cf30#64) (b33.callThen Fclose.sfpUnlock_call_shape Fclose.sfpUnlock_call_decode
    (Fclose.sfpUnlock_call_pins b33.ctx.image) (by decide) fun d bd raR => by
      rw [Fclose.sfpUnlock_call_target]
      exact sfpTail bd raR (SfpLockRelease.enter_fast d (regsAt d) bd.leaf
        ⟨bd.reg 1 (by decide), bd.reg 10 (by decide), trivial⟩) (by simp [SfpLockRelease.enter_regs, keysG])
        ExitPath.RetargetLockReleaseRecursive.leaf_fast)
    (fun _ p => by have := p.2; rwa [show Fclose.sfpUnlock_call.link = 0x8004cf30#64 by decide] at this)
  intro c36 h36
  have b36 := h36.1
  -- the epilogue: `ra`, `s0`–`s2` from the frame, `a0 = s2 = 0`
  have n (off : Nat) (ho : off ≤ 32) := frame_nat (k := 32) (off := off) frame (by decide) ho
  have n0 : (sp - 32#64).toNat = sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  have slotAt (i a : Nat) (w : BitVec 64) (sel : (saveLog sp ra s0 s1 s2)[i]? = some (a, 8, w))
      (ha : sp.toNat - 32 ≤ a) (ha' : a + 8 ≤ sp.toNat) (out : OutLRange ((saveLog sp ra s0 s1 s2).drop (i + 1)) a 8) :
      bytesVal .ld (read8 c36.σ.mem a) = w := by
    rw [b36.ctx.read fun j _ => ⟨⟨Or.inr (by omega), Or.inr (by omega)⟩, Or.inr (by omega),
      Or.inr (by rw [slotN]; omega)⟩, read8_value, S.memory]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ i _ _ sel out
  have e24 : (sp + 18446744073709551584#64 + 24#64).toNat = sp.toNat - 32 + 24 := by rw [sp32]; exact n 24 (by decide)
  have e16 : (sp + 18446744073709551584#64 + 16#64).toNat = sp.toNat - 32 + 16 := by rw [sp32]; exact n 16 (by decide)
  have e8 : (sp + 18446744073709551584#64 + 8#64).toNat = sp.toNat - 32 + 8 := by rw [sp32]; exact n 8 (by decide)
  have e0 : (sp + 18446744073709551584#64).toNat = sp.toNat - 32 := by rw [sp32]; exact n0
  have raS : bytesVal .ld (read8 c36.σ.mem (sp + 18446744073709551584#64 + 24#64).toNat) = ra := by
    rw [e24]
    exact slotAt 0 _ ra (by rw [saveLog, n 24 (by decide)]; rfl) (by omega) (by omega) (by
      simp only [saveLog, List.drop, OutLRange, n0, e16, e8]
      exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩)
  have s0S : bytesVal .ld (read8 c36.σ.mem (sp + 18446744073709551584#64 + 16#64).toNat) = s0 := by
    rw [e16]
    exact slotAt 2 _ s0 (by rw [saveLog, e16]; rfl) (by omega) (by omega) (by
      simp only [saveLog, List.drop, OutLRange, e8]
      exact ⟨Or.inr (by omega), trivial⟩)
  have s1S : bytesVal .ld (read8 c36.σ.mem (sp + 18446744073709551584#64 + 8#64).toNat) = s1 := by
    rw [e8]
    exact slotAt 3 _ s1 (by rw [saveLog, e8]; rfl) (by omega) (by omega) (by
      simp only [saveLog, List.drop, OutLRange])
  have s2S : bytesVal .ld (read8 c36.σ.mem (sp + 18446744073709551584#64).toNat) = s2 := by
    rw [e0]
    exact slotAt 1 _ s2 (by rw [saveLog, n0]; rfl) (by omega) (by omega) (by
      simp only [saveLog, List.drop, OutLRange, e16, e8]
      exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩)
  have w (off : Nat) (ho : off + 8 ≤ 32) (ao : off % 8 = 0) :
      ReadWindow (sp + 18446744073709551584#64 + BitVec.ofNat 64 off) 8 := by
    rw [sp32]; exact (frame_word (k := 32) (off := off) frame (by decide) ho (by decide) ao).read
  have w0 := w 0 (by decide) (by decide)
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at w0
  apply (Fclose.leave_fast c36 ra (regsAt c36) b36.leaf
    (by simp only [Fclose.leave_input, GHolds]
        exact ⟨b36.reg 2 (by decide), b36.reg 10 (by decide), b36.reg 18 (by decide), trivial⟩)
    (by rw [regsAt_of b36.sp]; exact w 24 (by decide) (by decide))
    (by rw [regsAt_of b36.sp]; exact w 16 (by decide) (by decide))
    (by rw [regsAt_of b36.sp]; exact w 8 (by decide) (by decide))
    (by rw [regsAt_of b36.sp]; exact w0)
    (by rw [regsAt_of b36.sp]; exact raS) raAl).weaken (fun _ e => e)
  intro d p
  have o := p.regs
  simp only [Fclose.leave_regs, Fclose.leave_loads, regsAt_of b36.sp, regsAt_of b36.s2, List.getD_cons_zero,
    List.getD_cons_succ, GHolds] at o
  obtain ⟨d2, d18, -, d9, d8, d1, -⟩ := o
  have kd (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1, 2, 8, 9, 10, 18]) : gprGet d.σ k = gprGet c36.σ k :=
    p.gpr_frame (by decide) k lo hi out
  exact
    { good := p.good
      image := p.image
      minstret := p.minstret
      tick := p.tick
      pc := p.pc
      result := by have := p.result; rwa [regsAt_of b36.s2] at this
      saved := fun k hk => by
        rcases hk with rfl | rfl | rfl | ⟨lo, hi⟩
        · rw [d2, sp0, BitVec.add_assoc]; simp
        · rw [d8, s0S, s0r]
        · rw [d9, s1S, s1r]
        · by_cases e18 : k = 18
          · subst e18; rw [d18, s2S, s2r]
          · rw [kd k (by omega) (by omega) (by simp; omega), b36.high k (by omega) hi, S.high k (by omega) hi]
      output := by
        unfold Vsa.Machine.output; rw [p.output]; exact b36.ctx.output.trans S.ctx.output
      htif := (p.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
        (b36.ctx.ok.htifIdle.trans ok.htifIdle.symm)
      gprs := S.gprs.trans (b36.gprs.trans p.kept)
      raReg := by rw [d1, raS]
      kept := fun a ha => by
        obtain ⟨h1, h2, h3, h4⟩ := ha
        rw [p.memory, Named.NamedValue.wl_nil, b36.ctx.frame a ⟨⟨by omega, h2⟩, h3, h4⟩, S.ctx.frame a (by unfold Out32; omega)] }

/-- **`_fclose_r(reent, fp)` on a standard stream** returns 0 to `ra`,
keeping `sp`, the callee-saved registers, the console, and every byte
outside its 80 bytes of stack, the stream's first 18 bytes, `errno` and the
descriptor's slot; given the stream's flush at its call site. -/
theorem fclose_returned {ra sp fp reent : BitVec 64} {c : Config} (h : LeafInput ra c) (ok : ExitOk c)
    (sp0 : gprGet c.σ 2 = some sp) (a0 : gprGet c.σ 10 = some reent) (a1 : gprGet c.σ 11 = some fp)
    (frame : NativeFrame sp 80) (file : Closable c.σ.mem reent fp) (pl : Placed reent fp)
    (flush : FlushCall c sp fp reent) :
    FnSummary 0x8004ce68#64 (fun d => d = c)
      (Returned ra (FcloseKeep sp fp (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) c) := by
  have s0r := gpr_some (ok.present 8 (by decide))
  have s1r := gpr_some (ok.present 9 (by decide))
  have s2r := gpr_some (ok.present 18 (by decide))
  apply summary_bind (fclose_save h ok sp0 s0r s1r s2r a0 a1 (frame.resize (by decide) (by decide)) pl.reentNz
    pl.fpNz) (fun _ p => p.1)
  intro c2 h2
  have S := h2.2
  apply summary_bind (fclose_open S file pl frame) (fun _ p => p.1)
  intro c10 h10
  obtain ⟨-, b10, a0r, a1r⟩ := h10
  apply summary_bind (fclose_flush S file pl frame flush b10 a0r a1r) (fun _ p => p.1)
  intro c16 h16
  obtain ⟨-, b16, a0z, smbf⟩ := h16
  exact fclose_finish ok sp0 s0r s1r s2r h.aligned S file pl frame b16 a0z smbf

theorem stdioRead {c c1 : Config} {sp : BitVec 64} (frame : NativeFrame sp 80) (ctx : KeepCtx (Out32 sp) c c1)
    (a : Nat) (ha : a + 8 ≤ Vsa.Sim.DlHeap.heapEnd) : read8 c1.σ.mem a = read8 c.σ.mem a := by
  have lo := frame.lower
  exact ctx.read fun i _ => Or.inl (by omega)

/-- stdin's flush at `_fclose_r` (never read: `_r = _ur = 0`). -/
theorem flushCall_stdin {c : Config} {sp reent : BitVec 64} (frame : NativeFrame sp 80)
    (flags : bytesVal .lh (read8 c.σ.mem (stdinFile + 16#64).toNat) = 4#64)
    (r : bytesVal .lw (read8 c.σ.mem (stdinFile + 8#64).toNat) = 0#64)
    (ur : bytesVal .lw (read8 c.σ.mem (stdinFile + 112#64).toNat) = 0#64) : FlushCall c sp stdinFile reent := by
  intro c1 l ok sp1 s0 _ a0 a1 ctx
  exact flush_stdin_returned l sp1 s0 (gpr_some (ok.present 19 (by decide))) a0 a1
    (frame_callee (front := 32) (size := 48) frame (by decide) _ (by decide))
    (by rw [stdioRead frame ctx _ (by decide)]; exact flags) (by rw [stdioRead frame ctx _ (by decide)]; exact r)
    (by rw [stdioRead frame ctx _ (by decide)]; exact ur)

/-- stdout's flush at `_fclose_r` (no buffer). -/
theorem flushCall_stdout {c : Config} {sp reent : BitVec 64} (frame : NativeFrame sp 80)
    (flags : bytesVal .lh (read8 c.σ.mem (stdoutFile + 16#64).toNat) = 9#64)
    (base : bytesVal .ld (read8 c.σ.mem (stdoutFile + 24#64).toNat) = 0#64) : FlushCall c sp stdoutFile reent := by
  intro c1 l ok sp1 s0 _ a0 a1 ctx
  exact flush_stdout_returned l sp1 s0 (gpr_some (ok.present 18 (by decide))) (gpr_some (ok.present 19 (by decide)))
    a0 a1 (frame_callee (front := 32) (size := 48) frame (by decide) _ (by decide))
    (by rw [stdioRead frame ctx _ (by decide)]; exact flags) (by rw [stdioRead frame ctx _ (by decide)]; exact base)

/-- stderr's flush at `_fclose_r` (unbuffered, nothing pending). -/
theorem flushCall_stderr {c : Config} {sp reent nb : BitVec 64} (frame : NativeFrame sp 80)
    (flags : bytesVal .lh (read8 c.σ.mem (stderrFile + 16#64).toNat) = 0x201a#64)
    (base : bytesVal .ld (read8 c.σ.mem (stderrFile + 24#64).toNat) = nb) (nz : nb ≠ 0#64)
    (pos : bytesVal .ld (read8 c.σ.mem stderrFile.toNat) = nb) : FlushCall c sp stderrFile reent := by
  intro c1 l ok sp1 s0 s1 a0 a1 ctx
  exact flush_stderr_returned l sp1 s0 s1 (gpr_some (ok.present 18 (by decide)))
    (gpr_some (ok.present 19 (by decide))) a0 a1 (frame_callee (front := 32) (size := 48) frame (by decide) _ (by decide))
    (by rw [stdioRead frame ctx _ (by decide)]; exact flags) (by rw [stdioRead frame ctx _ (by decide)]; exact base) nz
    (by rw [stdioRead frame ctx _ (by decide)]; exact pos)

end OCaml.Vm.Primitives.Uncaught.StdioFclose
