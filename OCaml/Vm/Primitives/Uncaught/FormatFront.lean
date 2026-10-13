import OCaml.Vm.Primitives.Uncaught.FormatException
import OCaml.Vm.Primitives.Named.NamedFront
import OCaml.Vm.Primitives.Memmove
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Sim.LogWindow

/-!
# `caml_format_exception` on a constant exception: the prologue

The 432-byte frame (`NativeFrame sp 432`), its six saves, the buffer's
`ptr`/`end` (`data = sp - 336`, `end = sp - 81`), the tag (nonzero: a
constant exception) and the name pointer `Field(exn, 0)`. The exception
block and its name lie in the arena, below every native frame.
-/

namespace OCaml.Vm.Primitives.Uncaught.FormatException
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gpr_some gpr_some_of NameAt)

/-- The frame's slots as `sp - 432 + off`, the form the blocks compute. -/
theorem frame_slot {sp : BitVec 64} (frame : NativeFrame sp 432) (off : Nat) (bound : off ≤ 432) :
    sp + 18446744073709551184#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (nativeFrameBase sp 432 + off) := by
  rw [show (18446744073709551184#64 : BitVec 64) = -BitVec.ofNat 64 432 from by decide]
  exact frame.address off bound

/-- **A call of `caml_format_exception(exn)`** on a constant exception named `name`. -/
structure FormatInput (ra sp exn np s0 s1 s2 s4 s5 : BitVec 64) (name : List (BitVec 8)) (c : Config) : Prop where
  leaf : LeafInput ra c
  ready : LibraryReady c
  pc : PCAt 0x8000dbec#64 c
  frame : NativeFrame sp 432
  stack : gprGet c.σ 2 = some sp
  arg : gprGet c.σ 10 = some exn
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  saved2 : gprGet c.σ 18 = some s2
  saved4 : gprGet c.σ 20 = some s4
  saved5 : gprGet c.σ 21 = some s5
  /-- a constant exception: the block's tag is not 0 -/
  constant : (c.σ.mem[(exn + 18446744073709551608#64).toNat]?).getD 0 ≠ 0#8
  namePtr : bytesVal .ld (read8 c.σ.mem exn.toNat) = np
  /-- the block and its name lie in the arena, below the native frames -/
  exnLow : Layout.sym_tohost + 16 ≤ exn.toNat
  exnHigh : exn.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  named : NameAt c.σ.mem np name
  nameLow : Layout.sym_bss_end ≤ np.toNat
  nameHigh : np.toNat + name.length + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  nonempty : 0 < name.length
  fits : name.length ≤ 255

/-- The prologue's eight stores into the frame. -/
def frameLog (sp ra s0 s1 s2 s4 s5 : BitVec 64) : List WEntry :=
  [((sp - 432#64 + 400#64).toNat, 8, s2), ((sp - 432#64 + 384#64).toNat, 8, s4),
   ((sp - 432#64 + 424#64).toNat, 8, ra), ((sp - 432#64 + 416#64).toNat, 8, s0),
   ((sp - 432#64 + 408#64).toNat, 8, s1), ((sp - 432#64 + 376#64).toNat, 8, s5),
   ((sp - 432#64 + 80#64).toNat, 8, sp - 432#64 + 96#64), ((sp - 432#64 + 88#64).toNat, 8, sp - 432#64 + 351#64)]

theorem frame_sub {sp : BitVec 64} (frame : NativeFrame sp 432) (off : Nat) (bound : off ≤ 432) :
    (sp - 432#64 + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 432 + off := by
  rw [BitVec.sub_eq_add_neg, show (-432#64 : BitVec 64) = 18446744073709551184#64 from by decide,
    frame_slot frame off bound]
  exact frame.slot_nat bound

theorem frameLog_inside {sp ra s0 s1 s2 s4 s5 : BitVec 64} (frame : NativeFrame sp 432) :
    LogInW [⟨nativeFrameBase sp 432, sp.toNat⟩] (frameLog sp ra s0 s1 s2 s4 s5) := by
  have top : nativeFrameBase sp 432 + 432 = sp.toNat := by
    have := frame.lower; unfold nativeFrameBase; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  simp only [frameLog, LogInW, InsideW]
  rw [frame_sub frame 400 (by decide), frame_sub frame 384 (by decide), frame_sub frame 424 (by decide),
    frame_sub frame 416 (by decide), frame_sub frame 408 (by decide), frame_sub frame 376 (by decide),
    frame_sub frame 80 (by decide), frame_sub frame 88 (by decide)]
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩,
    Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

/-- A word in the arena (below the native frames, above the HTIF words) reads. -/
theorem arena_read {a : BitVec 64} {n : Nat} (low : Layout.sym_tohost + 8 ≤ a.toNat)
    (high : a.toNat + n ≤ Vsa.Sim.DlHeap.heapEnd) : ReadWindow a n :=
  ⟨by simp only [Layout.sym_tohost] at low; omega, by simp only [Vsa.Sim.DlHeap.heapEnd] at high ⊢; omega,
   Or.inr low⟩

/-- An arena range misses the frame's stores. -/
theorem arena_out {sp ra s0 s1 s2 s4 s5 : BitVec 64} (frame : NativeFrame sp 432) {a n : Nat}
    (high : a + n ≤ Vsa.Sim.DlHeap.heapEnd) : OutLRange (frameLog sp ra s0 s1 s2 s4 s5) a n := by
  apply OCaml.Vm.Sim.outLRange_of_windows (frameLog_inside frame)
  have lower := frame.lower
  refine ⟨Or.inl ?_, trivial⟩
  unfold nativeFrameBase
  simp only [Vsa.Sim.DlHeap.heapEnd] at *
  omega

theorem outLRange_take {log : List WEntry} {a n : Nat} (k : Nat) (h : OutLRange log a n) :
    OutLRange (log.take k) a n :=
  OCaml.Vm.Sim.outLRange_sublist (List.take_sublist _ _) h

/-- A nonzero byte loaded by `lbu` passes `bnez`. -/
theorem lbu_bne_zero {b : BitVec 8} (h : b ≠ 0#8) : guardB .BNE (bytesVal .lbu [b]) 0#64 = true := by
  simp only [guardB, bytesVal, List.getD_cons_zero]
  simp only [bne_iff_ne, ne_eq]
  intro e; apply h; apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat e
  have lt := b.isLt
  simp [zero_extend, Sail.BitVec.zeroExtend] at this ⊢; omega

/-- After the prologue: at the name's `strlen`. -/
structure ProDone (before : Config) (ra sp exn np s0 s1 s2 s4 s5 : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x8000dd94#64 c
  name : gprGet c.σ 21 = some np
  bufEnd : gprGet c.σ 18 = some (sp + 18446744073709551535#64)
  bufData : gprGet c.σ 20 = some (sp + 18446744073709551280#64)
  stack : gprGet c.σ 2 = some (sp + 18446744073709551184#64)
  saved0 : gprGet c.σ 8 = some s0
  arg : gprGet c.σ 10 = some exn
  memory : c.σ.mem = writeLog before.σ.mem (frameLog sp ra s0 s1 s2 s4 s5)
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [2, 15, 18, 20, 21] → gprGet c.σ n = gprGet before.σ n
  kept : GprsKept before c
  htif : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- **The prologue** of `caml_format_exception` on a constant exception. -/
theorem format_pro {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c) :
    ∃ d, Steps c d ∧ ProDone c ra sp exn np s0 s1 s2 s4 s5 d := by
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  have r8 := regsAt_of h.saved0
  have r9 := regsAt_of h.saved1
  have r10 := regsAt_of h.arg
  have r18 := regsAt_of h.saved2
  have r20 := regsAt_of h.saved4
  have r21 := regsAt_of h.saved5
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have logEq : proLog (regsAt c) (pro_loads c.σ.mem (regsAt c)) = frameLog sp ra s0 s1 s2 s4 s5 := by
    simp only [proLog, frameLog, r1, r2, r8, r9, r18, r20, r21]
  have slot : ∀ k, k + 8 ≤ 432 → k % 8 = 0 → WriteWindow (regsAt c 2 + 18446744073709551184#64 + BitVec.ofNat 64 k) 8 :=
    fun k hk al => by rw [r2, frame_slot h.frame k (by omega)]; exact h.frame.word hk al
  have exnOut : ∀ a n, a + n ≤ Vsa.Sim.DlHeap.heapEnd → OutLRange (frameLog sp ra s0 s1 s2 s4 s5) a n :=
    fun a n hi => arena_out h.frame hi
  have tagAddr : (exn + 18446744073709551608#64).toNat = exn.toNat - 8 := by
    have := h.exnLow; simp only [Layout.sym_tohost] at this
    rw [BitVec.toNat_add]; simp; omega
  obtain ⟨c1, run1, p1⟩ := (pro_fast c (regsAt c) l0 (by
      simp only [pro_input, GHolds, r1, r2, r8, r9, r10, r18, r20, r21]
      exact ⟨h.leaf.raReg, h.stack, h.saved0, h.saved1, h.arg, h.saved2, h.saved4, h.saved5, trivial⟩)
    (slot 400 (by decide) (by decide)) (slot 384 (by decide) (by decide)) (slot 424 (by decide) (by decide))
    (slot 416 (by decide) (by decide)) (slot 408 (by decide) (by decide)) (slot 376 (by decide) (by decide))
    (by rw [r10]; apply arena_read <;> (try rw [tagAddr]) <;> (have := h.exnLow; have := h.exnHigh; omega))
    (by rw [logEq, r10, tagAddr]; exact outLRange_take 6 (exnOut _ _ (by have := h.exnHigh; omega)))
    (slot 80 (by decide) (by decide)) (slot 88 (by decide) (by decide))
    (by rw [r10]; exact arena_read (by have := h.exnLow; omega) h.exnHigh)
    (by rw [logEq, r10]; exact outLRange_take 8 (exnOut _ _ h.exnHigh))
    (by rw [logEq]; exact h.frame.image_outside (frameLog_inside h.frame))
    (by simp only [pro_loads, List.getD_cons_zero, r10]; exact lbu_bne_zero h.constant)).run c ⟨h.pc, rfl⟩
  have o1 := p1.regs
  simp only [pro_regs, pro_loads, List.getD_cons_zero, List.getD_cons_succ, r1, r2, r8, r9, r10, GHolds] at o1
  obtain ⟨g21, g18, g20, -, g2, g1, g8, -, g10, -⟩ := o1
  refine ⟨c1, run1, ?_⟩
  exact
    { leaf := ⟨p1.good, p1.image, p1.minstret, g1, h.leaf.aligned, p1.tick⟩
      pc := p1.pc
      name := by rw [read8_value] at g21; rw [g21, ← read8_value, h.namePtr]
      bufEnd := g18, bufData := g20, stack := g2, saved0 := g8, arg := g10
      memory := by rw [p1.memory, logEq]
      output := p1.output
      frame := fun n lo hi out => p1.gpr_frame (by decide) n lo hi out
      kept := p1.kept
      htif := p1.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide) }

end OCaml.Vm.Primitives.Uncaught.FormatException
