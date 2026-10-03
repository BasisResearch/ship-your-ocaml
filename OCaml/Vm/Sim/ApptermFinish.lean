import OCaml.Vm.Sim.ApptermInput
import OCaml.Vm.Sim.ApptermSuffixSegment
import OCaml.Vm.Sim.ApptermSuffixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The generated generic-tail-call suffix enters the closure after the proved
backward copy, restoring represented data and platform from its exact log. -/
theorem appterm_finish {L : OCaml.Layout} {P : Prog} {s : St} {c middle d : Config}
    {pl : Place} {cp : ChanPlace} {sp high count slots l a k dest : Nat}
    (stable : WindowStable L.runtimeOk [⟨tailcallStart sp count slots, sp + 8 * slots⟩])
    (h : ArmInput L P s .APPTERM c pl cp sp high) (positive : 0 < count)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8) (ready : EnterReady c (tailcallStart sp count slots))
    (space : ApptermWriteOk P s c pl cp sp high count slots)
    (front : ApptermCopyStart c sp count slots middle)
    (copied : BackwardCopyAt sp (tailcallStart sp count slots) (stackWords c sp count) middle 0 d) :
    ∃ nb after, StepsN nb d after ∧ Running L P (tailcallState s count slots dest) after := by
  have written : d.σ.mem = writeLog c.σ.mem
      (reverseCopyLog (tailcallStart sp count slots) (stackWords c sp count) 0) := by
    rw [copied.memory, front.memory]
  have accu : gpr d Layout.reg_accu = some (BitVec.ofNat 64 (a + 8 * k)) :=
    (copied.frame.frame Register.x21 (by decide)).trans
      ((front.frame.frame Register.x21 (by decide)).trans (represented_register h.accu field.sourceWord))
  have extra : gpr d Layout.reg_extra = some (BitVec.ofNat 64 s.extra) :=
    (copied.frame.frame Register.x18 (by decide)).trans ((front.frame.frame Register.x18 (by decide)).trans h.extra)
  have countReg : gpr d 10 = some (BitVec.ofNat 64 (count - 1)) :=
    (copied.frame.frame Register.x10 (by decide)).trans front.extraCount
  have baseReg : gpr d 11 = some (BitVec.ofNat 64 (tailcallStart sp count slots)) :=
    (copied.frame.frame Register.x11 (by decide)).trans front.base
  have loop : LoopRegisters d := loopRegisters_frame (fun r hr =>
    (copied.frame.frame r (by revert r; decide)).trans (front.frame.frame r (by revert r; decide))) h.dispatch.loop
  have fieldWord : word c (a + 8 * k) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) :=
    (Option.some.inj (field.read h.toVmReprAt (by simp [roots])).word).symm
  have closureRead := (space.payload.accu_field_load (payload_of_repr h.toVmReprAt) field written).trans fieldWord
  have domainRead := word_read_writeLog_out space.enter.domain written
  have thresholdRead := word_read_writeLog_out space.enter.threshold written
  have pendingRead := ready.toSignalCheckReady.read_log space.enter.pending written
  have targetNat : (BitVec.ofNat 64 (tailcallStart sp count slots)).toNat = tailcallStart sp count slots :=
    Nat.mod_eq_of_lt (by have upper := space.copy.targetUpper; omega)
  have thresholdAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x098#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl
  have domainWindow : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have pendingWindow : RamReadAt Layout.sym_caml_something_to_do 4 := ⟨by decide, by decide, by decide⟩
  have capacity : zopz0zI_u (BitVec.ofNat 64 (tailcallStart sp count slots))
      (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)) = false := by
    apply bltu_false_of_ge
    rw [targetNat]
    exact ready.capacity
  have bp : SegSt (0x80002ad0#64)
      [⟨Register.x21, BitVec.ofNat 64 (a + 8 * k)⟩, ⟨Register.x18, BitVec.ofNat 64 s.extra⟩,
       ⟨Register.x10, BitVec.ofNat 64 (count - 1)⟩, ⟨Register.x11, BitVec.ofNat 64 (tailcallStart sp count slots)⟩,
       ⟨Register.x19, BitVec.ofNat 64 Layout.sym_Caml_state⟩,
       ⟨Register.x20, BitVec.ofNat 64 Layout.sym_caml_something_to_do⟩]
      (fun σ => Vsa.Sim.Code.CamlApptermSuffixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨copied.good, copied.pc, ⟨accu, extra, countReg, baseReg, loop.domain, loop.pending, trivial⟩,
      copied.good.minstret, copied.tick, appterm_suffix_loaded copied.image, rfl, rfl⟩
  have run := tr_appterm_suffix (BitVec.ofNat 64 (a + 8 * k)) (BitVec.ofNat 64 s.extra)
    (BitVec.ofNat 64 (count - 1)) (BitVec.ofNat 64 (tailcallStart sp count slots))
    (BitVec.ofNat 64 Layout.sym_Caml_state) (BitVec.ofNat 64 Layout.sym_caml_something_to_do) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, geometry.toNat, domainWindow.toNat, pendingWindow.toNat] at run
  have first := run geometry.lower geometry.upper geometry.htif
    (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) closureRead.symm
    domainWindow.lower domainWindow.upper domainWindow.htif (word c Layout.sym_Caml_state) domainRead.symm
  simp only [thresholdAddress, ready.threshold.toNat] at first
  obtain ⟨nb, after, _, steps, post⟩ := first ready.threshold.lower ready.threshold.upper ready.threshold.htif
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)) thresholdRead.symm capacity
    pendingWindow.lower pendingWindow.upper pendingWindow.htif 0#64 pendingRead.symm (by decide) d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have observations : TailcallPostWith
      (reverseCopyLog (tailcallStart sp count slots) (stackWords c sp count) 0) c s pl sp slots dest count after := by
    refine ⟨⟨post.pcAt, PinsHold.get post.pins ⟨5, by simp⟩, PinsHold.get post.pins ⟨3, by simp⟩,
      ⟨_, PinsHold.get post.pins ⟨6, by simp⟩, field.sourceWord⟩,
      ⟨_, PinsHold.get post.pins ⟨2, by simp⟩, field.sourceWord⟩, ?_⟩,
      post.good, memory.trans written, frame.out.trans (copied.frame.out.trans front.frame.out), ?_⟩
    · have counter : gpr after Layout.reg_extra = some (BitVec.ofNat 64 s.extra + BitVec.ofNat 64 (count - 1)) :=
        PinsHold.get post.pins ⟨4, by simp⟩
      simpa only [tailcallState, tailcall_extra s.extra count positive] using counter
    · exact loopRegisters_frame (fun r hr => frame.frame r (by revert r; decide)) loop
  have arguments := stack_value_words h.stack (Nat.le_trans space.fits space.bound)
  exact ⟨nb, after, steps, tailcall_restore_of_log stable h.toVmReprAt h.running.platform space.toTailcallMemoryOk
    (reverse_copy_log_words arguments observations.memory) observations⟩

end OCaml.Vm.Sim
