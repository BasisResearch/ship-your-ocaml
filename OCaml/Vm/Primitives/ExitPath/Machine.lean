import OCaml.Vm.Primitives.ExitPath.Context
import OCaml.Vm.Primitives.ExitPath.Halt

/-! The default process-exit run, from `caml_sys_exit` to the HTIF halt. -/
namespace OCaml.Vm.Primitives.ExitPath
open Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

/-- The native stack below `sp` used by the exit path: 16 + 96 + 16 + 96 bytes. -/
def exitDepth : Nat := 224

theorem LogWithin.outLRange {log : List WEntry} {lo hi a n : Nat} (h : LogWithin log lo hi)
    (apart : a + n ≤ lo ∨ hi ≤ a) : OutLRange log a n := by
  induction log with
  | nil => trivial
  | cons e rest ih =>
    have he := h e (by simp)
    exact ⟨by omega, ih (fun e' he' => h e' (by simp [he']))⟩

/-- Static obligations of the default exit path. The runtime supplies the
four flag/list globals at their defaults (zero: no GC verbosity, no cleanup at
exit, no atexit registrations, stdio never initialized) and a native stack
window disjoint from them and from the image. -/
structure ExitLayout (sp : BitVec 64) : Prop where
  low : 0x80000000 + exitDepth ≤ sp.toNat
  high : sp.toNat ≤ 0x100000000
  htif : Layout.sym_tohost + 16 + exitDepth ≤ sp.toNat
  aligned : sp.toNat % 16 = 0
  text : Image.textBase + Image.textSize ≤ sp.toNat - exitDepth ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - exitDepth ∨ sp.toNat ≤ Image.rodataBase
  globals : ∀ g ∈ [verbGc, cleanupOnExit, atexitList, atexitMutex, stdioExitHandler],
    g.toNat + 8 ≤ sp.toNat - exitDepth ∨ sp.toNat ≤ g.toNat

structure ExitGlobals (c : Config) : Prop where
  quiet : bytesVal .ld (read8 c.σ.mem verbGc.toNat) &&& 1024#64 = 0#64
  noCleanup : bytesVal .lw (read8 c.σ.mem cleanupOnExit.toNat) = 0#64
  noAtexit : bytesVal .ld (read8 c.σ.mem atexitList.toNat) = 0#64
  noHandler : bytesVal .ld (read8 c.σ.mem stdioExitHandler.toNat) = 0#64

structure ExitInput (live : Nat → Prop) (ra sp v : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  ok : VsaOk live c
  stack : gpr c 2 = some sp
  arg : gpr c 10 = some v
  layout : ExitLayout sp
  globals : ExitGlobals c

theorem sub_toNat {x : BitVec 64} {k : Nat} (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem add_toNat {x : BitVec 64} {j : Nat} (h : x.toNat + j < 2 ^ 64) :
    (x + BitVec.ofNat 64 j).toNat = x.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Stack-address arithmetic: unfold `toNat` of the frame offsets, then `omega`. -/
macro "frame_arith" : tactic =>
  `(tactic| (simp only [BitVec.toNat_sub, BitVec.toNat_add] at *; simp at *; omega))

/-- The runtime globals are fixed RAM words away from the HTIF registers. -/
theorem global_window (g : BitVec 64) (hg : g ∈ [verbGc, cleanupOnExit, atexitList, atexitMutex, stdioExitHandler]) :
    ReadWindow g 8 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, Or.inr (by decide)⟩

theorem ExitLayout.image {sp : BitVec 64} (h : ExitLayout sp) {log : List WEntry}
    (within : LogWithin log (sp.toNat - exitDepth) sp.toNat) : ImageOutside log :=
  ⟨within.outLRange h.text, within.outLRange h.rodata⟩

/-- A slot of the exit stack window, stated by its bounds; the caller's
frame arithmetic discharges them. -/
theorem ExitLayout.write {sp x : BitVec 64} (h : ExitLayout sp)
    (slot : sp.toNat - exitDepth ≤ x.toNat ∧ x.toNat + 8 ≤ sp.toNat ∧ x.toNat % 8 = 0) :
    WriteWindow x 8 := by
  have l := h.low; have u := h.high; have t := h.htif
  unfold exitDepth at *
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem ExitLayout.read {sp x : BitVec 64} (h : ExitLayout sp)
    (slot : sp.toNat - exitDepth ≤ x.toNat ∧ x.toNat + 8 ≤ sp.toNat ∧ x.toNat % 8 = 0) :
    ReadWindow x 8 := (h.write slot).read

/-- Parked at `_exit`'s HTIF store with its address and data registers. -/
structure Parked (live : Nat → Prop) (sp code : BitVec 64) (c d : Config) : Prop where
  ctx : ExitCtx live (sp.toNat - exitDepth) sp.toNat c d
  pc : pcOf d = some 0x800008b0#64
  base : gpr d 14 = some 0x800618ac#64
  data : gpr d 15 = some ((code <<< 32) >>> 31 ||| 1#64)

theorem exit_run {live ra sp v c} (h : ExitInput live ra sp v c) :
    FnSummary 0x8001c7ac#64 (fun d => d = c) (Parked live sp (exitCode v) c) := by
  have L := h.layout
  have ctx0 : ExitCtx live (sp.toNat - exitDepth) sp.toNat c c :=
    ⟨h.ok, h.image, h.minstret, rfl, fun _ _ => rfl⟩
  -- caml_sys_exit: untag, save ra, call caml_do_exit
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else v
  have e0 := SysExit.entry_fast c R0 h.toLeafInput ⟨h.raReg, h.stack, h.arg, True.intro⟩
    (L.write (by
      have := L.low; have := L.aligned; unfold exitDepth at *
      simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (L.image (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [SysExit.entryLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      subst he
      simp only [R0, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_sub, BitVec.toNat_add]; simp
      omega))
  apply summary_bind e0 (fun _ p => p.pc)
  intro d0 p0
  have ctx1 := ctx0.step p0 (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [SysExit.entryLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      subst he
      simp only [R0, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_sub, BitVec.toNat_add]; simp
      omega) (by decide) (by simp [SysExit.entry_regs, keysG])
  let a0 : GRegs := [(2, sp - 16#64), (10, exitCode v)]
  have a0h : GHolds d0.σ a0 := holds_project p0.regs (by simp [a0, SysExit.entry_regs, R0, lookupG, exitCode])
  have J0 := call_registers_summary SysExit.entry_call_shape SysExit.entry_call_decode d0
    (SysExit.entry_call_pins p0.image) p0.good p0.image p0.tick p0.minstret a0 a0h
    (by change KeysOK [2, 10]; decide) (by simp [KeysAvoidRa, a0, keysG]) rfl
  apply summary_bind J0 (fun _ q => q.pc)
  intro d1 q1
  have ctx2 := ctx1.call q1 (by simp [keysG])
  -- caml_do_exit: save the callee-saved registers, test GC verbosity
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then SysExit.entry_call.link else
    if n = 2 then sp - 16#64 else if n = 10 then exitCode v else (gpr d1 n).getD 0
  have pr := fun n lo hi => ctx2.present n lo hi
  have e1 := DoExit.save_fast d1 R1 (ctx2.leaf (gholds_lookup _ q1.regs rfl) (by simp only [R1, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q1.regs rfl, gholds_lookup _ q1.regs rfl, pr 8 (by decide) (by decide),
      pr 9 (by decide) (by decide), gholds_lookup _ q1.regs rfl, pr 18 (by decide) (by decide),
      pr 19 (by decide) (by decide), pr 20 (by decide) (by decide), pr 21 (by decide) (by decide),
      pr 22 (by decide) (by decide), pr 23 (by decide) (by decide), pr 24 (by decide) (by decide),
      pr 25 (by decide) (by decide), pr 26 (by decide) (by decide), True.intro⟩
    (global_window _ (by simp))
    (by
      intro k hk
      have := L.low; have := L.aligned; unfold exitDepth at *
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact L.write (by unfold exitDepth; simp only [R1, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (L.image (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [DoExit.saveLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [R1, ↓reduceIte, Nat.reduceEqDiff]; frame_arith)))
    (by rw [ctx2.read (L.globals _ (by simp))]; exact h.globals.quiet)
  apply summary_bind e1 (fun _ p => p.pc)
  intro d2 p1
  have ctx3 := ctx2.step p1 (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [DoExit.saveLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [R1, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (by decide) (by simp [DoExit.save_regs, keysG])
  have sp2 : gpr d2 2 = some (sp - 16#64 - 96#64) := gholds_lookup _ p1.regs rfl
  have code2 : gpr d2 9 = some (exitCode v) := gholds_lookup _ p1.regs rfl
  -- caml_debugger(PROGRAM_EXIT, Val_unit): a `ret` leaf
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then SysExit.entry_call.link else exitCode v
  have e2 := DoExit.debug_fast d2 R2 (ctx3.leaf (gholds_lookup _ p1.regs rfl) (by simp only [R2, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p1.regs rfl, code2, True.intro⟩
  apply summary_bind e2 (fun _ p => p.pc)
  intro d3 p2
  have ctx4 := ctx3.step p2 LogWithin.nil (by decide) (by simp [DoExit.debug_regs, keysG])
  have fr2 : gpr d3 2 = some (sp - 16#64 - 96#64) :=
    (p2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans sp2
  let a2 : GRegs := [(2, sp - 16#64 - 96#64), (9, exitCode v), (10, 3#64)]
  have J2 := call_registers_summary DoExit.debug_call_shape DoExit.debug_call_decode d3
    (DoExit.debug_call_pins p2.image) p2.good p2.image p2.tick p2.minstret a2
    ⟨fr2, gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, True.intro⟩
    (by change KeysOK [2, 9, 10]; decide) (by simp [KeysAvoidRa, a2, keysG]) rfl
  apply summary_bind J2 (fun _ q => q.pc)
  intro d4 q2
  have ctx5 := ctx4.call q2 (by simp [keysG])
  let R3 : Nat → BitVec 64 := fun n => if n = 1 then DoExit.debug_call.link else 3#64
  have l3 := CamlDebugger.leaf_fast d4 R3 (ctx5.leaf (gholds_lookup _ q2.regs rfl) (by simp only [R3, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q2.regs rfl, gholds_lookup _ q2.regs rfl, True.intro⟩
  apply summary_bind l3 (fun _ p => p.pc)
  intro d5 p3
  have ctx6 := ctx5.step p3 LogWithin.nil (by decide) (by simp)
  have sp5 : gpr d5 2 = some (sp - 16#64 - 96#64) :=
    (p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ q2.regs rfl)
  have code5 : gpr d5 9 = some (exitCode v) :=
    (p3.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by simp)).trans (gholds_lookup _ q2.regs rfl)
  -- if (caml_cleanup_on_exit) caml_shutdown(): the flag is clear
  let R4 : Nat → BitVec 64 := fun n => if n = 1 then DoExit.debug_call.link else if n = 9 then exitCode v else 3#64
  have e4 := DoExit.cleanup_fast d5 R4 (ctx6.leaf (gholds_lookup _ p3.regs rfl) (by simp only [R4, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p3.regs rfl, code5, gholds_lookup _ p3.regs rfl, True.intro⟩
    ⟨by decide, by decide, Or.inr (by decide)⟩
    (by rw [ctx6.read (L.globals _ (by simp))]; exact h.globals.noCleanup)
  apply summary_bind e4 (fun _ p => p.pc)
  intro d6 p4
  have ctx7 := ctx6.step p4 LogWithin.nil (by decide) (by simp [DoExit.cleanup_regs, keysG])
  have e5 := DoExit.signals_fast d6 R4 (ctx7.leaf (gholds_lookup _ p4.regs rfl) (by simp only [R4, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p4.regs rfl, gholds_lookup _ p4.regs rfl, gholds_lookup _ p4.regs rfl, True.intro⟩
  apply summary_bind e5 (fun _ p => p.pc)
  intro d7 p5
  have ctx8 := ctx7.step p5 LogWithin.nil (by decide) (by simp [DoExit.signals_regs, keysG])
  have sp7 : gpr d7 2 = some (sp - 16#64 - 96#64) :=
    (p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans
      ((p4.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans sp5)
  -- caml_terminate_signals(): a `ret` leaf
  let a5 : GRegs := [(2, sp - 16#64 - 96#64), (9, exitCode v), (10, 3#64)]
  have J5 := call_registers_summary DoExit.signals_call_shape DoExit.signals_call_decode d7
    (DoExit.signals_call_pins p5.image) p5.good p5.image p5.tick p5.minstret a5
    ⟨sp7, gholds_lookup _ p5.regs rfl, gholds_lookup _ p5.regs rfl, True.intro⟩
    (by change KeysOK [2, 9, 10]; decide) (by simp [KeysAvoidRa, a5, keysG]) rfl
  apply summary_bind J5 (fun _ q => q.pc)
  intro d8 q5
  have ctx9 := ctx8.call q5 (by simp [keysG])
  let R5 : Nat → BitVec 64 := fun n => if n = 1 then DoExit.signals_call.link else 3#64
  have l5 := CamlTerminateSignals.leaf_fast d8 R5 (ctx9.leaf (gholds_lookup _ q5.regs rfl) (by simp only [R5, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q5.regs rfl, gholds_lookup _ q5.regs rfl, True.intro⟩
  apply summary_bind l5 (fun _ p => p.pc)
  intro d9 p6
  have ctx10 := ctx9.step p6 LogWithin.nil (by decide) (by simp)
  have sp9 : gpr d9 2 = some (sp - 16#64 - 96#64) :=
    (p6.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ q5.regs rfl)
  have code9 : gpr d9 9 = some (exitCode v) :=
    (p6.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by simp)).trans (gholds_lookup _ q5.regs rfl)
  -- exit(retcode)
  let R6 : Nat → BitVec 64 := fun n => if n = 1 then DoExit.signals_call.link else exitCode v
  have e6 := DoExit.leave_fast d9 R6 (ctx10.leaf (gholds_lookup _ p6.regs rfl) (by simp only [R6, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p6.regs rfl, code9, True.intro⟩
  apply summary_bind e6 (fun _ p => p.pc)
  intro d10 p7
  have ctx11 := ctx10.step p7 LogWithin.nil (by decide) (by simp [DoExit.leave_regs, keysG])
  have sp10 : gpr d10 2 = some (sp - 16#64 - 96#64) :=
    (p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans sp9
  have s0 := ctx11.present 8 (by decide) (by decide)
  let a7 : GRegs := [(2, sp - 16#64 - 96#64), (8, (gpr d10 8).getD 0), (10, exitCode v)]
  have J7 := call_registers_summary DoExit.leave_call_shape DoExit.leave_call_decode d10
    (DoExit.leave_call_pins p7.image) p7.good p7.image p7.tick p7.minstret a7
    ⟨sp10, s0, gholds_lookup _ p7.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10]; decide) (by simp [KeysAvoidRa, a7, keysG]) rfl
  apply summary_bind J7 (fun _ q => q.pc)
  intro d11 q7
  have ctx12 := ctx11.call q7 (by simp [keysG])
  -- exit: save s0/ra, keep the code in s0, call __call_exitprocs(code, NULL)
  let R7 : Nat → BitVec 64 := fun n => if n = 1 then DoExit.leave_call.link else
    if n = 2 then sp - 16#64 - 96#64 else if n = 8 then (gpr d10 8).getD 0 else exitCode v
  have e8 := LibcExit.enter_fast d11 R7 (ctx12.leaf (gholds_lookup _ q7.regs rfl) (by simp only [R7, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q7.regs rfl, gholds_lookup _ q7.regs rfl, gholds_lookup _ q7.regs rfl,
      gholds_lookup _ q7.regs rfl, True.intro⟩
    (L.write (by have := L.low; have := L.aligned; unfold exitDepth at *; simp only [R7, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (L.write (by have := L.low; have := L.aligned; unfold exitDepth at *; simp only [R7, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (L.image (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [LibcExit.enterLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl <;> (simp only [R7, ↓reduceIte, Nat.reduceEqDiff]; frame_arith)))
  apply summary_bind e8 (fun _ p => p.pc)
  intro d12 p8
  have ctx13 := ctx12.step p8 (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [LibcExit.enterLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl <;> (simp only [R7, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (by decide) (by simp [LibcExit.enter_regs, keysG])
  let a8 : GRegs := [(2, sp - 16#64 - 96#64 - 16#64), (8, exitCode v), (10, exitCode v), (11, 0#64)]
  have J8 := call_registers_summary LibcExit.enter_call_shape LibcExit.enter_call_decode d12
    (LibcExit.enter_call_pins p8.image) p8.good p8.image p8.tick p8.minstret a8
    ⟨gholds_lookup _ p8.regs rfl, gholds_lookup _ p8.regs rfl, gholds_lookup _ p8.regs rfl,
      gholds_lookup _ p8.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10, 11]; decide) (by simp [KeysAvoidRa, a8, keysG]) rfl
  apply summary_bind J8 (fun _ q => q.pc)
  intro d13 q8
  have ctx14 := ctx13.call q8 (by simp [keysG])
  -- __call_exitprocs: save, take the lock, find the atexit list empty, restore and release
  let R8 : Nat → BitVec 64 := fun n => if n = 1 then LibcExit.enter_call.link else
    if n = 2 then sp - 16#64 - 96#64 - 16#64 else if n = 10 then exitCode v else if n = 11 then 0#64 else
    (gpr d13 n).getD 0
  have pr := fun n lo hi => ctx14.present n lo hi
  have e9 := ExitProcs.enter_fast d13 R8 (ctx14.leaf (gholds_lookup _ q8.regs rfl) (by simp only [R8, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q8.regs rfl, gholds_lookup _ q8.regs rfl, gholds_lookup _ q8.regs rfl,
      gholds_lookup _ q8.regs rfl, pr 18 (by decide) (by decide), pr 20 (by decide) (by decide),
      pr 22 (by decide) (by decide), pr 23 (by decide) (by decide), pr 24 (by decide) (by decide), True.intro⟩
    (global_window _ (by simp))
    (by
      intro k hk
      have := L.low; have := L.aligned; unfold exitDepth at *
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact L.write (by unfold exitDepth; simp only [R8, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (L.image (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [ExitProcs.enterLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [R8, ↓reduceIte, Nat.reduceEqDiff]; frame_arith)))
  apply summary_bind e9 (fun _ p => p.pc)
  intro d14 p9
  have ctx15 := ctx14.step p9 (by
      have := L.low; unfold exitDepth at *
      intro e he
      simp only [ExitProcs.enterLog, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [R8, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (by decide) (by simp [ExitProcs.enter_regs, keysG])
  let sp224 : BitVec 64 := sp - 16#64 - 96#64 - 16#64 - 96#64
  let mutexv : BitVec 64 := bytesVal .ld (read8 (writeLog d13.σ.mem (ExitProcs.enterLog R8 |>.take 2)) atexitMutex.toNat)
  let a9 : GRegs := [(2, sp224), (10, mutexv), (20, 0x80064d90#64), (23, 0x80064900#64)]
  have J9 := call_registers_summary ExitProcs.enter_call_shape ExitProcs.enter_call_decode d14
    (ExitProcs.enter_call_pins p9.image) p9.good p9.image p9.tick p9.minstret a9
    ⟨gholds_lookup _ p9.regs rfl, gholds_lookup _ p9.regs rfl, gholds_lookup _ p9.regs rfl,
      gholds_lookup _ p9.regs rfl, True.intro⟩
    (by change KeysOK [2, 10, 20, 23]; decide) (by simp [KeysAvoidRa, a9, keysG]) rfl
  apply summary_bind J9 (fun _ q => q.pc)
  intro d15 q9
  have ctx16 := ctx15.call q9 (by simp [keysG])
  let R9 : Nat → BitVec 64 := fun n => if n = 1 then ExitProcs.enter_call.link else mutexv
  have l9 := RetargetLockAcquireRecursive.leaf_fast d15 R9
    (ctx16.leaf (gholds_lookup _ q9.regs rfl) (by simp only [R9, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q9.regs rfl, gholds_lookup _ q9.regs rfl, True.intro⟩
  apply summary_bind l9 (fun _ p => p.pc)
  intro d16 p10
  have ctx17 := ctx16.step p10 LogWithin.nil (by decide) (by simp)
  have keep := fun n (hn : 1 < n ∧ n ≤ 31) => p10.toEffectPost.gpr_frame (by decide) n (by omega) hn.2 (by simp)
  let R10 : Nat → BitVec 64 := fun n => if n = 1 then ExitProcs.enter_call.link else if n = 2 then sp224 else
    if n = 10 then mutexv else if n = 20 then 0x80064d90#64 else 0x80064900#64
  have e11 := ExitProcs.empty_fast d16 R10 (ctx17.leaf (gholds_lookup _ p10.regs rfl) (by simp only [R10, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p10.regs rfl, (keep 2 (by decide)).trans (gholds_lookup _ q9.regs rfl),
      gholds_lookup _ p10.regs rfl, (keep 20 (by decide)).trans (gholds_lookup _ q9.regs rfl),
      (keep 23 (by decide)).trans (gholds_lookup _ q9.regs rfl), True.intro⟩
    (by simp only [R10, ↓reduceIte, Nat.reduceEqDiff]; decide) (global_window _ (by simp))
    (by rw [ctx17.read (L.globals _ (by simp))]; exact h.globals.noAtexit)
  apply summary_bind e11 (fun _ p => p.pc)
  intro d17 p11
  have ctx18 := ctx17.step p11 LogWithin.nil (by decide) (by simp [ExitProcs.empty_regs, keysG])
  have keep11 := fun n (hn : n ≠ 18 ∧ 1 ≤ n ∧ n ≤ 31) =>
    p11.toEffectPost.gpr_frame (by decide) n hn.2.1 hn.2.2 (by simp; omega)
  -- the epilogue reloads exit's return address from its save slot
  have memory17 : d17.σ.mem = writeLog d13.σ.mem (ExitProcs.enterLog R8) := by
    have nil : ∀ m : Std.ExtHashMap Nat (BitVec 8), writeLog m [] = m := fun _ => rfl
    rw [p11.memory, nil, p10.memory, nil, q9.memory, p9.memory]
  let R11 : Nat → BitVec 64 := fun n => if n = 1 then ExitProcs.enter_call.link else if n = 2 then sp224 else
    0x80064900#64
  have e12 := ExitProcs.leave_fast d17 R11 (ctx18.leaf (gholds_lookup _ p11.regs rfl) (by simp only [R11, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p11.regs rfl, gholds_lookup _ p11.regs rfl, gholds_lookup _ p11.regs rfl, True.intro⟩
    (global_window _ (by simp [R11, atexitMutex, Layout.sym_atexit_recursive_mutex]))
    (by
      intro k hk
      have := L.low; have := L.aligned; unfold exitDepth at *
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact L.read (by unfold exitDepth; simp only [R11, sp224, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
  apply summary_bind e12 (fun _ p => p.pc)
  intro d18 p12
  have ctx19 := ctx18.step p12 LogWithin.nil (by decide) (by simp [ExitProcs.leave_regs, keysG])
  have raBack : bytesVal .ld (read8 d17.σ.mem (R11 2 + 88#64).toNat) = LibcExit.enter_call.link := by
    rw [read8_value, memory17]
    exact Gc.word_writeLog_at _ _ 5 _ _ rfl True.intro
  have ra18 : gpr d18 1 = some LibcExit.enter_call.link := by
    rw [← raBack]; exact gholds_lookup _ p12.regs rfl
  have a18 := ctx19.present 10 (by decide) (by decide)
  let R12 : Nat → BitVec 64 := fun n => if n = 1 then LibcExit.enter_call.link else (gpr d18 10).getD 0
  have l12 := RetargetLockReleaseRecursive.leaf_fast d18 R12 (ctx19.leaf ra18 (by simp only [R12, ↓reduceIte]; decide)) ⟨ra18, a18, True.intro⟩
  apply summary_bind l12 (fun _ p => p.pc)
  intro d19 p13
  have ctx20 := ctx19.step p13 LogWithin.nil (by decide) (by simp)
  have code19 : gpr d19 8 = some (exitCode v) := by
    rw [p13.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp),
      p12.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp),
      p11.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp),
      p10.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp),
      q9.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp),
      p9.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp)]
    exact gholds_lookup _ q8.regs rfl
  -- back in exit: the stdio exit handler is null; _exit(code)
  have a19 := ctx20.present 10 (by decide) (by decide)
  let R13 : Nat → BitVec 64 := fun n => if n = 1 then LibcExit.enter_call.link else
    if n = 8 then exitCode v else (gpr d19 10).getD 0
  have e14 := LibcExit.handler_fast d19 R13 (ctx20.leaf (gholds_lookup _ p13.regs rfl) (by simp only [R13, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p13.regs rfl, code19, a19, True.intro⟩ (global_window _ (by simp))
    (by rw [ctx20.read (L.globals _ (by simp))]; exact h.globals.noHandler)
  apply summary_bind e14 (fun _ p => p.pc)
  intro d20 p14
  have ctx21 := ctx20.step p14 LogWithin.nil (by decide) (by simp [LibcExit.handler_regs, keysG])
  have e15 := LibcExit.tail_fast d20 R13 (ctx21.leaf (gholds_lookup _ p14.regs rfl) (by simp only [R13, ↓reduceIte]; decide))
    ⟨gholds_lookup _ p14.regs rfl, gholds_lookup _ p14.regs rfl, True.intro⟩
  apply summary_bind e15 (fun _ p => p.pc)
  intro d21 p15
  have ctx22 := ctx21.step p15 LogWithin.nil (by decide) (by simp [LibcExit.tail_regs, keysG])
  let a15 : GRegs := [(10, exitCode v)]
  have J15 := call_registers_summary LibcExit.tail_call_shape LibcExit.tail_call_decode d21
    (LibcExit.tail_call_pins p15.image) p15.good p15.image p15.tick p15.minstret a15
    ⟨gholds_lookup _ p15.regs rfl, True.intro⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, a15, keysG]) rfl
  apply summary_bind J15 (fun _ q => q.pc)
  intro d22 q15
  have ctx23 := ctx22.call q15 (by simp [keysG])
  let R14 : Nat → BitVec 64 := fun n => if n = 1 then LibcExit.tail_call.link else exitCode v
  have e16 := HtifExit.store_fast d22 R14 (ctx23.leaf (gholds_lookup _ q15.regs rfl) (by simp only [R14, ↓reduceIte]; decide))
    ⟨gholds_lookup _ q15.regs rfl, gholds_lookup _ q15.regs rfl, True.intro⟩
  apply e16.weaken (fun _ eq => eq)
  intro d23 p16
  exact ⟨ctx23.step p16 LogWithin.nil (by decide) (by simp [HtifExit.store_regs, keysG]), p16.pc,
    gholds_lookup _ p16.regs rfl, gholds_lookup _ p16.regs rfl⟩


/-- `_exit` keeps the low 32 bits of its `int` status. -/
def exitStatus (code : BitVec 64) : BitVec 64 := (code <<< 32) >>> 32

theorem exitStatus_word (code : BitVec 64) :
    (code <<< 32) >>> 31 ||| 1#64 = (exitStatus code <<< 1) ||| 1#64 := by
  unfold exitStatus
  congr 1
  bv_omega

theorem exitStatus_small (code : BitVec 64) : (exitStatus code).toNat < 2 ^ 47 := by
  unfold exitStatus
  rw [BitVec.toNat_ushiftRight]
  have := (code <<< 32).isLt
  omega

/-- From `caml_sys_exit`'s entry, the default exit path halts the machine with
the low 32 bits of the untagged status and the console output so far. -/
theorem exit_halts {live ra sp v c} (h : ExitInput live ra sp v c)
    (entry : pcOf c = some 0x8001c7ac#64) :
    Halts c (Vsa.Machine.output c.σ) (exitStatus (exitCode v)).toNat := by
  obtain ⟨d, steps, parked⟩ := (exit_run h).run c ⟨entry, rfl⟩
  have halt := HtifExit.store_halts (exitStatus_small (exitCode v)) parked.ctx.ok.good parked.ctx.image
    parked.pc parked.base (by rw [parked.data, exitStatus_word]) parked.ctx.ok.htifIdle
  rw [parked.ctx.output] at halt
  obtain ⟨d', σf, run, halted, out⟩ := halt
  exact ⟨d', σf, steps.trans run, halted, out⟩

end OCaml.Vm.Primitives.ExitPath
