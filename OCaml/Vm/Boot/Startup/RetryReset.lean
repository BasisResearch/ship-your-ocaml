import OCaml.Vm.Boot.Startup.AttemptFailReset
import OCaml.Vm.Boot.Startup.CamlRetrySteps
import OCaml.Vm.Sim.LogRead
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- Actual reset execution from the failed first attempt to the call
`caml_attempt_open(&exe_name, &trail, 1)` with `exe_name = argv[1]` ("/prog"). -/
structure ResetRetryCall (initial after : Config) where
  atFailed : Config
  failed : ResetAttemptFailed initial atFailed
  pc : PCAt jal_8000512c_call.target after
  regs : GHolds after.σ ((1, jal_8000512c_call.link) :: [(11, parameterStack + 40#64), (12, 1#64),
    (10, parameterStack + 32#64), (2, parameterStack), (14, argv1Ptr), (15, argvPtr + 8#64)])
  argv : gprGet after.σ 9 = some argvPtr
  ready : RuntimeReady ((failed.opened.opened.node.toNat, 5) :: failed.opened.call.search.path.table.H)
    (startupAllocatorCredits - 496) parameterStack jal_8000512c_call.link after
  late : LateImage after
  exeName : bytesT after.σ.mem (parameterStack + 32#64).toNat 8 = argv1Ptr
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_retry_call_exists : ∃ initial after, Nonempty (ResetRetryCall initial after) := by
  obtain ⟨initial, c0, ⟨w⟩⟩ := reset_attempt_failed_exists
  have frame : NativeFrame (parameterStack + 48#64) 32 := by constructor <;> decide
  -- fd < 0
  obtain ⟨c1, run1, p1⟩ := (caml_retry_test c0 _ w.fd w.ready.toLeafInput ⟨w.result, trivial⟩ w.negative).run c0
    ⟨w.pc, rfl⟩
  have ready1 := w.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p1.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans w.stack)
    ((p1.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans w.ready.raReg) (by decide)
    frame (by simp only [LogInW])
  -- caml_executable_name()
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary jal_80005024_call_shape jal_80005024_call_decode c1
    (jal_80005024_call_pins ready1.image) p1.good ready1.image p1.tick p1.minstret [(2, parameterStack), (10, w.fd)]
    ⟨ready1.stack, gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run c1 ⟨p1.pc, rfl⟩
  have p2' : WriteRegistersPost [1] [] c1 jal_80005024_call.target w.fd
      ((1, jal_80005024_call.link) :: [(2, parameterStack), (10, w.fd)]) c2 := p2
  have ready2 := ready1.stack_log p2' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2'.regs rfl) (gholds_lookup (n := 1) _ p2'.regs rfl) (by decide) frame
    (by simp only [LogInW])
  obtain ⟨c3, run3, p3⟩ := (caml_executable_name_null c2 _ ready2.toLeafInput
    ⟨gholds_lookup (n := 1) _ p2'.regs rfl, trivial⟩).run c2 ⟨p2'.pc, rfl⟩
  have ready3 := ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready2.stack)
    (gholds_lookup (n := 1) _ p3.regs rfl) (by decide) frame (by simp only [LogInW])
  -- no name: argv[1]
  obtain ⟨c4, run4, p4⟩ := (caml_retry_noname c3 _ ready3.toLeafInput
    ⟨gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩).run c3 ⟨p3.pc, rfl⟩
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p4.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready3.stack)
    ((p4.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready3.raReg) (by decide)
    frame (by simp only [LogInW])
  have argv4 : gprGet c4.σ 9 = some argvPtr :=
    (p4.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
      ((p3.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        ((p2'.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
          ((p1.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans w.argv)))
  have late4 : LateImage c4 :=
    w.late.frame ((EmbedFrame.of_memory p1.memory).trans ((EmbedFrame.of_memory p2'.memory).trans
      ((EmbedFrame.of_memory p3.memory).trans (EmbedFrame.of_memory p4.memory))))
  obtain ⟨c5, run5, p5⟩ := (caml_retry_argv1 c4 _ ready4.toLeafInput late4.embed
    ⟨argv4, gholds_lookup (n := 10) _ p4.regs rfl, trivial⟩).run c4 ⟨p4.pc, rfl⟩
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready4.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready4.raReg) (by decide)
    frame (by simp only [LogInW])
  have late5 : LateImage c5 := late4.frame (EmbedFrame.of_memory p5.memory)
  obtain ⟨c6, run6, p6⟩ := (caml_retry_dash c5 _ ready5.toLeafInput late5.embed
    ⟨gholds_lookup (n := 8) _ p5.regs rfl, gholds_lookup (n := 10) _ p5.regs rfl, trivial⟩).run c5 ⟨p5.pc, rfl⟩
  have ready6 := ready5.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p6.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready5.stack)
    ((p6.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready5.raReg) (by decide)
    frame (by simp only [LogInW])
  have late6 : LateImage c6 := late5.frame (EmbedFrame.of_memory p6.memory)
  -- print_config
  have flags : read4 c6.σ.mem Layout.sym_print_config = [0#8, 0#8, 0#8, 0#8] := by
    simp only [read4]
    rw [show (c6.σ.mem[Layout.sym_print_config]?).getD 0 = 0#8 from by simpa using late6.printFlags 0 (by decide),
      late6.printFlags 1 (by decide), late6.printFlags 2 (by decide), late6.printFlags 3 (by decide)]
  obtain ⟨c7, run7, p7⟩ := (caml_retry_config c6 _ ready6.toLeafInput flags
    ⟨gholds_lookup (n := 10) _ p6.regs rfl, trivial⟩).run c6 ⟨p6.pc, rfl⟩
  have ready7 := ready6.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack)
    ((p7.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready6.raReg) (by decide)
    frame (by simp only [LogInW])
  have late7 : LateImage c7 := late6.frame (EmbedFrame.of_memory p7.memory)
  have argv7 : gprGet c7.σ 9 = some argvPtr :=
    (p7.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
      ((p6.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 9) _ p5.regs rfl))
  have s4At7 : gprGet c7.σ 20 = some 1#64 :=
    (p7.toEffectPost.gpr_frame (by decide) 20 (by decide) (by decide) (by decide)).trans
      ((p6.toEffectPost.gpr_frame (by decide) 20 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 20) _ p5.regs rfl))
  obtain ⟨c8, run8, p8⟩ := (caml_retry_prog_test c7 _ ready7.toLeafInput late7.embed
    ⟨s4At7, argv7, gholds_lookup (n := 10) _ p7.regs rfl, trivial⟩).run c7 ⟨p7.pc, rfl⟩
  have ready8 := ready7.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p8.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack)
    ((p8.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready7.raReg) (by decide)
    frame (by simp only [LogInW])
  -- caml_attempt_open(&exe_name, &trail, 1)
  obtain ⟨c9, run9, p9⟩ := (caml_retry_prog_call c8 _ parameterStack ready8.toLeafInput
    ⟨ready8.stack, gholds_lookup (n := 14) _ p8.regs rfl, gholds_lookup (n := 15) _ p8.regs rfl, trivial⟩
    (by constructor <;> decide) (by constructor <;> decide)
    (by constructor <;> simp only [camlRetryLog, OutLRange] <;> decide)).run c8 ⟨p8.pc, rfl⟩
  have ready9 := ready8.stack_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p9.regs rfl) (gholds_lookup (n := 1) _ p9.regs rfl) (by decide) frame
    (by simp only [camlRetryLog, LogInW, InsideW]; decide)
  have late9 : LateImage c9 :=
    (late7.frame (EmbedFrame.of_memory p8.memory)).frame (EmbedFrame.stack p9.memory
      (by simp only [camlRetryLog, LogInW, InsideW]; decide : LogInW [⟨nativeFrameBase (parameterStack + 48#64) 32,
        (parameterStack + 48#64).toNat⟩] (camlRetryLog parameterStack)) (by decide))
  refine ⟨initial, c9, ⟨c0, w, p9.pc, p9.regs,
    (p9.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
      ((p8.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans argv7),
    ready9, late9, ?_,
    w.run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (run8.trans run9))))))))⟩⟩
  rw [p9.memory]
  exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl (by simp only [camlRetryLog, OutLRange, List.drop]; decide)
end OCaml.Vm.Boot.WhileMinElfParse
