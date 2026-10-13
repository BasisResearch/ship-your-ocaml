import OCaml.Vm.Boot.Startup.ProgOpenReset
import OCaml.Vm.Boot.Startup.AttemptOk
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- A word of `openProgLog`, read back. -/
theorem openProgLog_read4 (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry) (A : Nat) (v : BitVec 64)
    (split : openProgLog m = log1 ++ (A, 4, v) :: log2) (out : OutLRange log2 A 4) :
    read4 (writeLog m (openProgLog m)) A = [(swData v).extractLsb' 0 8, (swData v).extractLsb' 8 8,
      (swData v).extractLsb' 16 8, (swData v).extractLsb' 24 8] := by
  obtain ⟨b0, b1, b2, b3⟩ := pin4_of_writeLog m log1 log2 A v out
  unfold read4
  rw [split]
  simp only [b0, b1, b2, b3, Option.getD_some]

theorem vsaReg_of_gpr {c : Config} {n : Nat} {v : BitVec 64} (h : gprGet c.σ n = some v) (hn : n < 32) :
    vsaReg c n = v := by
  unfold vsaReg
  simp only [VsaIris.PC, show n ≠ 32 by omega, ↓reduceIte, h, Option.getD_some]

/-- caml_attempt_open's frame lies above `open`'s stack and apart from htif's
globals. -/
theorem attempt_frame_apart {x : Nat} (lo : 0x87ffff40 ≤ x) (hi : x < 0x87ffff80) :
    (x < attemptStack.toNat - openProgDepth ∨ attemptStack.toNat ≤ x) ∧ OutW errnoWindows x ∧
      (x < Layout.sym_files + 104 ∨ Layout.sym_files + 108 ≤ x) ∧ (x < Layout.sym_fds + 72 ∨ Layout.sym_fds + 96 ≤ x) := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  simp only [sp, openProgDepth, OutW, errnoWindows, and_true, Layout.sym_files, Layout.sym_fds]
  omega

theorem attempt_slot_bounds {off i : Nat} (h : off + 8 ≤ 64) (hi : i < 8) :
    0x87ffff40 ≤ 0x87ffff40 + off + i ∧ 0x87ffff40 + off + i < 0x87ffff80 := by omega

/-- Away from `open`'s stack, errno and its descriptor log. -/
def OpenApart (a : Nat) : Prop :=
  (a < attemptStack.toNat - openProgDepth ∨ attemptStack.toNat ≤ a) ∧ OutW errnoWindows a ∧
    (a < Layout.sym_files + 104 ∨ Layout.sym_files + 108 ≤ a) ∧ (a < Layout.sym_fds + 72 ∨ Layout.sym_fds + 96 ≤ a)

theorem OpenApart.below {a : Nat} (lo : 0x80064d4c ≤ a) (hi : a < embedLimit)
    (f1 : a < Layout.sym_files + 104 ∨ Layout.sym_files + 108 ≤ a) (f2 : a < Layout.sym_fds + 72 ∨ Layout.sym_fds + 96 ≤ a) :
    OpenApart a := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  refine ⟨Or.inl ?_, ?_, f1, f2⟩
  · rw [sp]; unfold openProgDepth embedLimit Layout.sym_stack_top Layout.sym_stack_size at *; omega
  · simp only [OutW, errnoWindows, and_true]; omega

theorem OpenApart.embed {a : Nat} (h : EmbedByte a) : OpenApart a := by
  obtain ⟨lo, hi⟩ := h
  exact OpenApart.below (by unfold heapEnd at lo; omega) hi (Or.inr (by unfold heapEnd Layout.sym_files at *; omega))
    (Or.inr (by unfold heapEnd Layout.sym_fds at *; omega))

theorem OpenApart.late_low {a : Nat} (ha : EnvironByte a ∨ VerbGcByte a ∨
    (allocatorImpureAddr ≤ a ∧ a < allocatorImpureAddr + 8) ∨
    (Layout.sym_print_config ≤ a ∧ a < Layout.sym_print_config + 8)) : OpenApart a := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  refine ⟨Or.inl ?_, ?_, ?_, ?_⟩ <;>
    rcases ha with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [sp, openProgDepth, OutW, errnoWindows, and_true, Layout.sym_environ, Layout.sym_caml_verb_gc, allocatorImpureAddr,
      Layout.sym_print_config, Layout.sym_files, Layout.sym_fds] at * <;> omega

theorem OpenApart.fsWord {a : Nat} (h : FsWordByte a) : OpenApart a := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  refine ⟨Or.inl ?_, ?_, ?_, ?_⟩ <;> rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [sp, openProgDepth, OutW, errnoWindows, and_true, Layout.sym_fs_ready, Layout.sym_files, Layout.sym_fds] at * <;> omega

theorem OpenApart.slot {a : Nat} (lo : slotOne ≤ a) (hi : a < slotOne + 56) (opens : a < slotOne + 48 ∨ slotOne + 52 ≤ a) :
    OpenApart a := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  refine ⟨Or.inl ?_, ?_, ?_, ?_⟩ <;>
    simp only [sp, openProgDepth, OutW, errnoWindows, and_true, slotOne, Layout.sym_files, Layout.sym_fds] at * <;> omega

theorem OpenApart.heap {a : Nat} (lo : heapStart ≤ a) (hi : a < heapEnd) : OpenApart a := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  refine ⟨Or.inl ?_, ?_, ?_, ?_⟩ <;>
    simp only [sp, openProgDepth, OutW, errnoWindows, and_true, heapStart, heapEnd, Layout.sym_files, Layout.sym_fds] at * <;> omega

theorem fds_open_apart {x : Nat} (lo : Layout.sym_fds ≤ x) (hi : x < Layout.sym_fds + 96) :
    (x < attemptStack.toNat - openProgDepth ∨ attemptStack.toNat ≤ x) ∧ OutW errnoWindows x := by
  have sp : attemptStack.toNat = 0x87ffff40 := by decide
  simp only [sp, openProgDepth, OutW, errnoWindows, and_true, Layout.sym_fds] at *
  omega

/-- Actual reset execution up to caml_attempt_open's return of descriptor 3
for "/prog", with the trailer read and the name recorded. -/
structure ResetAttemptOk (initial after : Config) where
  atOpen : Config
  opened : ResetProgOpened initial atOpen
  /-- caml_attempt_open's state at `open`'s return. -/
  attempt : AttemptOpened ((opened.call.call.copy.toNat, 5 + 1) :: (opened.call.retry.failed.opened.opened.node.toNat, 5) ::
      opened.call.retry.failed.opened.call.search.path.table.H) (startupAllocatorCredits - 592) opened.call.call.copy
    opened.call.retry.failed.opened.opened.node jal_8000512c_call.link (vsaReg opened.call.atRetry 8) argvPtr
    (vsaReg opened.call.atRetry 18) (vsaReg opened.call.atRetry 19) (vsaReg opened.call.atRetry 20) atOpen
  ok : AttemptOk ((opened.call.call.copy.toNat, 5 + 1) :: (opened.call.retry.failed.opened.opened.node.toNat, 5) ::
      opened.call.retry.failed.opened.call.search.path.table.H) (startupAllocatorCredits - 592)
    opened.call.call.copy jal_8000512c_call.link (vsaReg opened.call.atRetry 8) argvPtr
    (vsaReg opened.call.atRetry 18) (vsaReg opened.call.atRetry 19) (vsaReg opened.call.atRetry 20) atOpen after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_attempt_ok_exists : ∃ initial after, Nonempty (ResetAttemptOk initial after) := by
  obtain ⟨initial, d, ⟨w⟩⟩ := reset_prog_opened_exists
  have O := w.opened
  have C := w.call.call
  have fs := w.call.fs
  have depth : heapEnd + openProgDepth ≤ attemptStack.toNat := by decide
  -- memory at `open`'s return, away from the stack it used and errno: the log over the call's
  have glob (x : Nat) (hx : x < heapEnd) (errno : OutW errnoWindows x)
      (out : OutL (openProgLog w.atCall.σ.mem) x) :
      (d.σ.mem[x]?).getD 0 = (w.atCall.σ.mem[x]?).getD 0 := by
    rw [O.mem x (Or.inl (by omega)) errno, writeLog_out _ _ _ out]
  have outLog (x : Nat) (h : x < Layout.sym_files + 104 ∨ Layout.sym_files + 108 ≤ x)
      (h2 : x < Layout.sym_fds + 72 ∨ Layout.sym_fds + 96 ≤ x) : OutL (openProgLog w.atCall.σ.mem) x := by
    simp only [openProgLog, htifOpenTakeLog, OutL, and_true]; omega
  have regs := (gholds_append _ _).1 O.regs
  have logA (x : Nat) (lo : Layout.sym_fds ≤ x) (hi : x < Layout.sym_fds + 96) :
      (d.σ.mem[x]?).getD 0 = ((writeLog w.atCall.σ.mem (openProgLog w.atCall.σ.mem))[x]?).getD 0 :=
    O.mem x (fds_open_apart lo hi).1 (fds_open_apart lo hi).2
  have backA (x : Nat) (h : OpenApart x) : (d.σ.mem[x]?).getD 0 = (w.atCall.σ.mem[x]?).getD 0 := by
    rw [O.mem x h.1 h.2.1, writeLog_out _ _ _ (outLog x h.2.2.1 h.2.2.2)]
  have A : AttemptOpened ((w.call.call.copy.toNat, 5 + 1) :: (w.call.retry.failed.opened.opened.node.toNat, 5) ::
      w.call.retry.failed.opened.call.search.path.table.H) (startupAllocatorCredits - 592) w.call.call.copy
      w.call.retry.failed.opened.opened.node jal_8000512c_call.link (vsaReg w.call.atRetry 8) argvPtr
      (vsaReg w.call.atRetry 18) (vsaReg w.call.atRetry 19) (vsaReg w.call.atRetry 20) d := {
    slots := fun off value member => by
      have range : 16 ≤ off ∧ off + 8 ≤ 64 := by
        simp only [attemptOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      have base : nativeFrameBase parameterStack 64 = 0x87ffff40 := by decide
      have sp : attemptStack.toNat = 0x87ffff40 := by decide
      have back (x : Nat) (lo : 0x87ffff40 ≤ x) (hi : x < 0x87ffff80) :
          (d.σ.mem[x]?).getD 0 = (w.atCall.σ.mem[x]?).getD 0 := by
        obtain ⟨st, er, f1, f2⟩ := attempt_frame_apart lo hi
        rw [O.mem x st er, writeLog_out _ _ _ (outLog x f1 f2)]
      rw [word_observed (m := w.atCall.σ.mem) (nativeFrameBase parameterStack 64 + off)
        (fun i hi => by
          rw [base]; exact back _ (attempt_slot_bounds range.2 hi).1 (attempt_slot_bounds range.2 hi).2)]
      exact C.slots off value member
    raAligned := by decide
    pc := O.pc
    regs := ⟨gholds_lookup (n := 2) _ regs.1 rfl, gholds_lookup (n := 10) _ regs.1 rfl,
      by rw [gholds_lookup (n := 8) _ regs.2 rfl, vsaReg_of_gpr C.trail (by decide)],
      gholds_lookup (n := 18) _ regs.2 rfl,
      by rw [gholds_lookup (n := 19) _ regs.2 rfl, vsaReg_of_gpr C.slot (by decide)],
      by rw [gholds_lookup (n := 20) _ regs.2 rfl, vsaReg_of_gpr C.flagReg (by decide)], trivial⟩
    ready := O.ready
    late := C.late.transport ⟨fun a ea => (backA a (OpenApart.embed ea)).trans (C.late.embed.byte a ea)⟩
      (fun a ha => backA a (OpenApart.late_low ha))
    words := fs.words.transport fun x hx => backA x (OpenApart.fsWord hx)
    slot := fs.slot.transport_opens (fun x lo hi op => backA x (OpenApart.slot lo hi op))
      (fun j hj => by
        have b := O.ready.block_bounds (q := w.call.retry.failed.opened.opened.node.toNat) (n := 5)
          (List.mem_cons_of_mem _ List.mem_cons_self)
        exact backA _ (OpenApart.heap (Nat.le_trans b.1 (Nat.le_add_right _ _)) (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (Nat.lt_succ_of_le hj) _) b.2)))
    nodeHeap := O.ready.block_bounds (q := w.call.retry.failed.opened.opened.node.toNat) (n := 5)
      (List.mem_cons_of_mem _ List.mem_cons_self)
    kind := by
      rw [read4_observed (m := writeLog w.atCall.σ.mem (openProgLog w.atCall.σ.mem)) (Layout.sym_fds + 72)
        (fun k hk => logA _ (Nat.le_add_right_of_le (Nat.le_add_right _ _)) (by unfold Layout.sym_fds; omega)),
        show Layout.sym_fds + 72 = Layout.sym_fds + 72 from rfl,
        openProgLog_read4 _ [(Layout.sym_files + 56 + 48, 4, _), (Layout.sym_fds + 72 + 4, 4, 1#64), (Layout.sym_fds + 72 + 8, 8, 0#64), (Layout.sym_fds + 72 + 16, 4, 0#64)] [] (Layout.sym_fds + 72) 4#64 rfl (by simp only [OutLRange, and_true] <;> (simp only [Layout.sym_fds]; omega))]
      decide
    nodeWord := by
      rw [read4_observed (m := writeLog w.atCall.σ.mem (openProgLog w.atCall.σ.mem)) (Layout.sym_fds + 76)
        (fun k hk => logA _ (Nat.le_add_right_of_le (Nat.le_add_right _ _)) (by unfold Layout.sym_fds; omega)),
        show Layout.sym_fds + 76 = Layout.sym_fds + 72 + 4 from rfl,
        openProgLog_read4 _ [(Layout.sym_files + 56 + 48, 4, _)] [(Layout.sym_fds + 72 + 8, 8, 0#64), (Layout.sym_fds + 72 + 16, 4, 0#64), (Layout.sym_fds + 72, 4, 4#64)] (Layout.sym_fds + 72 + 4) 1#64 rfl (by simp only [OutLRange, and_true] <;> (simp only [Layout.sym_fds]; omega))]
      decide
    flags := by
      rw [read4_observed (m := writeLog w.atCall.σ.mem (openProgLog w.atCall.σ.mem)) (Layout.sym_fds + 88)
        (fun k hk => logA _ (Nat.le_add_right_of_le (Nat.le_add_right _ _)) (by unfold Layout.sym_fds; omega)),
        show Layout.sym_fds + 88 = Layout.sym_fds + 72 + 16 from rfl,
        openProgLog_read4 _ [(Layout.sym_files + 56 + 48, 4, _), (Layout.sym_fds + 72 + 4, 4, 1#64), (Layout.sym_fds + 72 + 8, 8, 0#64)] [(Layout.sym_fds + 72, 4, 4#64)] (Layout.sym_fds + 72 + 16) 0#64 rfl (by simp only [OutLRange, and_true] <;> (simp only [Layout.sym_fds]; omega))]
      decide }
  obtain ⟨after, run, ok⟩ := attempt_ok d _ _ _ _ _ _ _ _ _ _ A
  exact ⟨initial, after, ⟨⟨d, w, A, ok, w.run.trans run⟩⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
