import OCaml.Vm.Boot.Startup.OpenOcamlrunReset
import OCaml.Vm.Boot.Startup.AttemptFailSteps
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- caml_attempt_open's six saves, read back from any state whose frame is
kept since the saves. -/
theorem ResetSearchTableReturned.attempt_slot {initial after c : Config} (w : ResetSearchTableReturned initial after)
    (caller : CallerFrame attemptStack w.atSaved c) {off : Nat} {value : BitVec 64}
    (member : (off, value) ∈ attemptOpenSlots jal_80004df8_call.link (vsaReg w.source 8)
      (BitVec.ofNat 64 WhileMinImage.argvArray) (vsaReg w.source 18) (vsaReg w.source 19) (vsaReg w.source 20)) :
    bytesT c.σ.mem (nativeFrameBase parameterStack 64 + off) 8 = value := by
  have frame : NativeFrame parameterStack 64 := by constructor <;> decide
  have base : nativeFrameBase parameterStack 64 = attemptStack.toNat := by decide
  rw [word_observed (m := w.atSaved.σ.mem) _ (fun i _ => caller.byte _ (by rw [base] at *; omega)), w.save.memory]
  apply frame.word_log_read
  · intro k v hk
    simp only [attemptOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
    omega
  · simp [attemptOpenSlots]
  · exact member

/-- Actual reset execution through caml_attempt_open's failure on "ocamlrun":
back in caml_main with a negative descriptor. -/
structure ResetAttemptFailed (initial after : Config) where
  atOpened : Config
  opened : ResetOcamlrunOpened initial atOpened
  fd : BitVec 64
  negative : fd = -1#64 ∨ fd = -4#64
  pc : PCAt jal_80004df8_call.link after
  result : gprGet after.σ 10 = some fd
  stack : gprGet after.σ 2 = some parameterStack
  argv : gprGet after.σ 9 = some (BitVec.ofNat 64 WhileMinImage.argvArray)
  ready : RuntimeReady ((opened.opened.node.toNat, 5) :: opened.call.search.path.table.H)
    (startupAllocatorCredits - 496) parameterStack jal_80004df8_call.link after
  late : LateImage after
  caller : CallerFrame parameterStack opened.call.search.path.table.atSaved after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_attempt_failed_exists : ∃ initial after, Nonempty (ResetAttemptFailed initial after) := by
  obtain ⟨initial, c0, ⟨w⟩⟩ := reset_ocamlrun_opened_exists

  have entry := (gholds_append _ _).1 w.opened.regs
  have frameS : NativeFrame attemptStack (48 + allocHeadroom) := by constructor <;> decide
  have frameA : NativeFrame attemptStack allocHeadroom := frameS.resize (by decide) (by decide)
  have frameGc : NativeFrame attemptStack 80 := by constructor <;> decide
  have frame64 : NativeFrame parameterStack 64 := by constructor <;> decide
  -- fd == -1
  obtain ⟨c1, run1, p1⟩ := (attempt_fail_test c0 _ w.opened.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ entry.1 rfl, trivial⟩).run c0 ⟨w.opened.pc, rfl⟩
  have ready1 := w.opened.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p1.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 2) _ entry.1 rfl))
    ((p1.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 1) _ entry.1 rfl)) (by decide) frameS (by simp only [LogInW])
  -- caml_stat_free(truename)
  obtain ⟨c2, run2, p2⟩ := (attempt_fail_free c1 _ attemptStack w.call.search.copy ready1.toLeafInput
    ⟨(p1.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 18) _ entry.2 rfl), ready1.stack, trivial⟩).run c1 ⟨p1.pc, rfl⟩
  have ready2 := ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2.regs rfl) (gholds_lookup (n := 1) _ p2.regs rfl) (by decide) frameS
    (by simp only [LogInW])
  obtain ⟨c3, run3, ⟨freed⟩⟩ := (stat_free_block c2 _ w.call.search.copy 9 _ attemptStack jal_80004aac_call.link
    (ready2.perm (List.Perm.swap _ _ _)) (gholds_lookup (n := 10) _ p2.regs rfl) frameA
    w.call.search.fresh.1 w.call.search.fresh.2).run c2 ⟨p2.pc, rfl⟩
  -- caml_gc_message(0x100, "Cannot open file\n")
  obtain ⟨c4, run4, p4⟩ := (attempt_fail_message c3 _ attemptStack freed.ready.toLeafInput
    ⟨freed.ready.stack, trivial⟩).run c3 ⟨library_pc freed.free.good freed.free.result.frame.pc, rfl⟩
  have ready4 := freed.ready.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p4.regs rfl) (gholds_lookup (n := 1) _ p4.regs rfl) (by decide) frameS
    (by simp only [LogInW])
  have embed3 : EmbedFrame c0 c3 :=
    (EmbedFrame.of_memory p1.memory).trans ((EmbedFrame.of_memory p2.memory).trans
      (freed.embed_frame frameA (by decide) w.call.search.fresh.1 w.call.search.fresh.2))
  have late4 : LateImage c4 := (w.opened.late.frame embed3).frame (EmbedFrame.of_memory p4.memory)
  obtain ⟨c5, run5, gc⟩ := (gc_message_quiet c4 attemptStack _ (vsaReg c4 12) (vsaReg c4 13) (vsaReg c4 14)
    (vsaReg c4 15) (vsaReg c4 16) (vsaReg c4 17) 0x100#64 ready4.toLeafInput frameGc
    ⟨gholds_lookup (n := 2) _ p4.regs rfl, gholds_lookup (n := 1) _ p4.regs rfl,
      gpr_of_ready ready4 12 (by decide) (by decide), gpr_of_ready ready4 13 (by decide) (by decide),
      gpr_of_ready ready4 14 (by decide) (by decide), gpr_of_ready ready4 15 (by decide) (by decide),
      gpr_of_ready ready4 16 (by decide) (by decide), gpr_of_ready ready4 17 (by decide) (by decide),
      gholds_lookup (n := 10) _ p4.regs rfl, trivial⟩ late4.verbGc).run c4 ⟨p4.pc, rfl⟩
  have ready5 := ready4.stack_log gc (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ gc.regs rfl) (gholds_lookup (n := 1) _ gc.regs rfl) (by decide) frameGc
    (gcMessageLog_inside frameGc)
  have late5 : LateImage c5 := late4.frame (EmbedFrame.stack gc.memory (gcMessageLog_inside frameGc) (by decide))
  -- __errno()
  obtain ⟨c6, run6, p6⟩ := (call_registers_summary jal_80004ac0_call_shape jal_80004ac0_call_decode c5
    (jal_80004ac0_call_pins ready5.image) gc.good ready5.image gc.tick gc.minstret [(2, attemptStack), (10, 0#64)]
    ⟨gholds_lookup (n := 2) _ gc.regs rfl, gholds_lookup (n := 10) _ gc.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run c5 ⟨gc.pc, rfl⟩
  have p6' : WriteRegistersPost [1] [] c5 jal_80004ac0_call.target 0#64
      ((1, jal_80004ac0_call.link) :: [(2, attemptStack), (10, 0#64)]) c6 := p6
  have ready6 := ready5.stack_log p6' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p6'.regs rfl) (gholds_lookup (n := 1) _ p6'.regs rfl) (by decide) frameS
    (by simp only [LogInW])
  have late6 : LateImage c6 := late5.frame (EmbedFrame.of_memory p6'.memory)
  obtain ⟨c7, run7, p7⟩ := (errno_return c6 jal_80004ac0_call.link ready6.toLeafInput
    ⟨gholds_lookup (n := 1) _ p6'.regs rfl, trivial⟩).run c6 ⟨p6'.pc, rfl⟩
  have ready7 := ready6.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack)
    (gholds_lookup (n := 1) _ p7.regs rfl) (by decide) frameS (by simp only [LogInW])
  have reent7 : gprGet c7.σ 10 = some 0x80064668#64 := by
    rw [gholds_lookup (n := 10) _ p7.regs rfl]
    exact congrArg some late6.reent
  -- s1 = -1 through the calls
  have s1At7 : gprGet c7.σ 9 = some (-1#64) :=
    (p7.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
      ((p6'.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        ((gc.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
          ((p4.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
            ((freed.saved_gpr (k := 9) (by decide)).trans
              ((p2.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
                (gholds_lookup (n := 9) _ p1.regs rfl))))))
  have window : ReadWindow 0x80064668#64 4 := by constructor <;> decide
  -- errno == EMFILE ? -4 : -1
  obtain ⟨cR, runR, v, neg, pcR, s1R, spR, readyR, memR⟩ : ∃ cR, Steps c7 cR ∧ ∃ v : BitVec 64,
      (v = -1#64 ∨ v = -4#64) ∧ PCAt 0x80004a1c#64 cR ∧ gprGet cR.σ 9 = some v ∧
      gprGet cR.σ 2 = some attemptStack ∧
      RuntimeReady ((w.opened.node.toNat, 5) :: w.call.search.path.table.H) (startupAllocatorCredits - 496) attemptStack
        jal_80004ac0_call.link cR ∧ cR.σ.mem = c7.σ.mem := by
    by_cases emfile : bytesVal .lw (read4 c7.σ.mem (0x80064668#64).toNat) = 24#64
    · obtain ⟨cR, run, p⟩ := (attempt_fail_code_emfile c7 _ _ _ ready7.toLeafInput ⟨reent7, trivial⟩ window rfl
        emfile).run c7 ⟨p7.pc, rfl⟩
      exact ⟨cR, run, -4#64, Or.inr rfl, p.pc, gholds_lookup (n := 9) _ p.regs rfl,
        (p.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack,
        ready7.stack_log p (by decide) (by simp only [keysG]; decide) (by decide)
          ((p.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack)
          ((p.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready7.raReg) (by decide)
          frameS (by simp only [LogInW]), p.memory⟩
    · obtain ⟨cR, run, p⟩ := (attempt_fail_code_other c7 _ _ _ ready7.toLeafInput ⟨reent7, trivial⟩ window rfl
        emfile).run c7 ⟨p7.pc, rfl⟩
      exact ⟨cR, run, -1#64, Or.inl rfl, p.pc,
        (p.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans s1At7,
        (p.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack,
        ready7.stack_log p (by decide) (by simp only [keysG]; decide) (by decide)
          ((p.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack)
          ((p.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready7.raReg) (by decide)
          frameS (by simp only [LogInW]), p.memory⟩
  -- caml_attempt_open's frame since its saves
  have tail : CallerFrame attemptStack c0 cR :=
    (CallerFrame.of_memory p1.memory).trans ((CallerFrame.of_memory p2.memory).trans
      ((⟨fun a bound => freed.byte frameA (by decide) w.call.search.fresh.1 w.call.search.fresh.2 (Or.inl bound)⟩ :
        CallerFrame attemptStack c2 c3).trans ((CallerFrame.of_memory p4.memory).trans
      ((CallerFrame.of_log gc.memory (gcMessageLog_inside frameGc)).trans ((CallerFrame.of_memory p6'.memory).trans
        ((CallerFrame.of_memory p7.memory).trans (CallerFrame.of_memory memR)))))))
  have callerR : CallerFrame attemptStack w.call.search.path.table.atSaved cR :=
    w.call.caller.trans (w.opened.caller.trans tail)
  -- restore and return
  obtain ⟨c8, run8, p8⟩ := (attempt_open_return cR parameterStack jal_80004df8_call.link _ _ _ _ _ v _
    readyR.toLeafInput frame64 ⟨spR, s1R, trivial⟩
    (fun off value member => w.call.search.path.table.attempt_slot callerR member) (by decide)).run cR ⟨pcR, rfl⟩
  have ready8 := readyR.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p8.regs rfl) (gholds_lookup (n := 1) _ p8.regs rfl) (by decide) frame64
    (by simp only [LogInW])
  have late8 : LateImage c8 :=
    (late6.frame (EmbedFrame.of_memory p7.memory)).frame ((EmbedFrame.of_memory memR).trans
      (EmbedFrame.of_memory p8.memory))
  refine ⟨initial, c8, ⟨c0, w, v, neg, p8.pc, gholds_lookup (n := 10) _ p8.regs rfl,
    gholds_lookup (n := 2) _ p8.regs rfl, gholds_lookup (n := 9) _ p8.regs rfl, ready8, late8,
    (callerR.mono (by decide)).trans (CallerFrame.of_memory p8.memory),
    w.run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (runR.trans run8))))))))⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
