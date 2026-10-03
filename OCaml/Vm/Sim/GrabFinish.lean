import OCaml.Vm.Sim.GrabAllocInput
import OCaml.Vm.Sim.GrabFinishArithmetic
import OCaml.Vm.Sim.GrabAllocSuffixSegment
import OCaml.Vm.Sim.GrabAllocSuffixPins
import OCaml.Vm.Sim.SwitchArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The generated GRAB suffix installs closure metadata and returns through
the saved caller frame after the proved argument copy. -/
theorem grab_finish {L : OCaml.Layout} {P : Prog} {s : St} {c middle d : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit dest : Nat} {env : BitVec 64}
    {savedEnv : Val} {savedExtra : BitVec 63} {rest : List Val}
    (runtime : AllocationRuntime L.runtimeOk c (grabAllocationLog c pl s sp a domain env))
    (h : ArmInput L P s .GRAB c pl cp sp high) (environment : valWord pl s.env = some env)
    (stack : s.stack.drop (1 + s.extra) = .code dest :: savedEnv :: .int savedExtra :: rest)
    (savedNonnegative : 0 ≤ savedExtra.toInt)
    (space : GrabAllocInput P s c pl cp sp high a domain limit env)
    (front : GrabCopyStart c sp s.extra a domain env middle)
    (copied : CursorCopyAt sp (a + 24) (stackWords c sp (1 + s.extra)) middle
      (stackWords c sp (1 + s.extra)).length d) :
    ∃ nb after, StepsN nb d after ∧ Running L P (grabState s dest savedEnv savedExtra rest) after := by
  have written : d.σ.mem = writeLog c.σ.mem
      (grabSetupLog domain a s.extra env ++ valueLog (a + 24) (stackWords c sp (1 + s.extra))) := by
    rw [copied.memory, forward_copy_log_complete, front.memory, writeLog_append]
  have pcReg : gpr d 8 = some (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) :=
    (copied.frame.frame Register.x8 (by decide)).trans ((front.frame.frame Register.x8 (by decide)).trans h.pc)
  have spReg : gpr d 9 = some (BitVec.ofNat 64 sp) :=
    (copied.frame.frame Register.x9 (by decide)).trans ((front.frame.frame Register.x9 (by decide)).trans h.spReg)
  have headerReg : gpr d 11 = some (BitVec.ofNat 64 (a - 8)) :=
    (copied.frame.frame Register.x11 (by decide)).trans front.header
  have valueReg : gpr d 10 = some (BitVec.ofNat 64 a) :=
    (copied.frame.frame Register.x10 (by decide)).trans front.value
  have bytesReg : gpr d 16 = some (BitVec.ofNat 64 (8 * (s.extra + 4))) :=
    (copied.frame.frame Register.x16 (by decide)).trans front.bytes
  have loop : LoopRegisters d := loopRegisters_frame (fun r hr =>
    (copied.frame.frame r (by revert r; decide)).trans (front.frame.frame r (by revert r; decide))) h.dispatch.loop
  have valueAddress : BitVec.ofNat 64 (a - 8) + sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 a := by
    change BitVec.ofNat 64 (a - 8) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]; congr 1; have room := space.nursery.room; omega
  have arityAddress : BitVec.ofNat 64 a + sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 (a + 8) := by
    rw [BitVec.ofNat_add]; rfl
  have newSp : BitVec.ofNat 64 sp + BitVec.ofNat 64 (8 * (s.extra + 4)) =
      BitVec.ofNat 64 (sp + 8 * (s.extra + 4)) := (BitVec.ofNat_add _ _).symm
  have codeAddress : BitVec.ofNat 64 (sp + 8 * (s.extra + 4)) + sign_extend (m := 64) (0xfe8#12) =
      BitVec.ofNat 64 (sp + 8 * (1 + s.extra)) := by
    rw [show sign_extend (m := 64) (0xfe8#12) = -(24#64) from by decide, ← BitVec.sub_eq_add_neg]
    exact grab_saved_address sp s.extra 0 (by decide)
  have envAddress : BitVec.ofNat 64 (sp + 8 * (s.extra + 4)) + sign_extend (m := 64) (0xff0#12) =
      BitVec.ofNat 64 (sp + 8 * (1 + s.extra) + 8) := by
    rw [show sign_extend (m := 64) (0xff0#12) = -(16#64) from by decide, ← BitVec.sub_eq_add_neg]
    exact grab_saved_address sp s.extra 1 (by decide)
  have extraAddress : BitVec.ofNat 64 (sp + 8 * (s.extra + 4)) + sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 (sp + 8 * (1 + s.extra) + 16) := by
    rw [show sign_extend (m := 64) (0xff8#12) = -(8#64) from by decide, ← BitVec.sub_eq_add_neg]
    exact grab_saved_address sp s.extra 2 (by decide)
  obtain ⟨codeMemory, codeWritten⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem a (sdData_val (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc - 1)))) := ⟨_, rfl⟩
  obtain ⟨nextMemory, arityWritten⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 codeMemory (a + 8) (sdData_val (5#64)) := ⟨_, rfl⟩
  have suffixMemory : nextMemory = writeLog d.σ.mem (grabSuffixLog a (pl.codeBase + 4 * (s.pc - 1))) := by
    rw [arityWritten, codeWritten]; rfl
  have fullMemory : nextMemory = writeLog c.σ.mem (grabAllocationLog c pl s sp a domain env) := by
    rw [suffixMemory, written, ← writeLog_append, grab_allocation_log_parts]
  have selected (i : Nat) (v : Val) (slot : (.code dest :: savedEnv :: .int savedExtra :: rest)[i]? = some v) :
      s.stack[(1 + s.extra) + i]? = some v := by
    rw [← List.getElem?_drop, stack]; exact slot
  have saved := return_frame_values (payload_of_repr h.toVmReprAt) stack
  have codeLoad : sign_extend (m := 64) (bytesT8 nextMemory (sp + 8 * (1 + s.extra))) =
      BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    have unchanged := word_read_writeLog_out (space.allocation.payload.stack _ _ (selected 0 (.code dest) rfl)) fullMemory
    simpa only [Nat.add_zero] using unchanged.trans saved.code
  have envLoad : sign_extend (m := 64) (bytesT8 nextMemory (sp + 8 * (1 + s.extra) + 8)) =
      word c (sp + 8 * (1 + s.extra) + 8) := by
    have unchanged := word_read_writeLog_out (space.allocation.payload.stack _ _ (selected 1 savedEnv rfl)) fullMemory
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using unchanged
  have extraLoad : sign_extend (m := 64) (bytesT8 nextMemory (sp + 8 * (1 + s.extra) + 16)) = tag64 savedExtra := by
    have unchanged := word_read_writeLog_out (space.allocation.payload.stack _ _ (selected 2 (.int savedExtra) rfl)) fullMemory
    have atSlot : sign_extend (m := 64) (bytesT8 nextMemory (sp + 8 * (1 + s.extra) + 16)) =
        word c (sp + 8 * (1 + s.extra) + 16) := by
      simpa only [Nat.mul_add, Nat.add_assoc] using unchanged
    exact atSlot.trans saved.extraArgs
  have suffixImage : ImageOutside (grabSuffixLog a (pl.codeBase + 4 * (s.pc - 1))) := by
    apply imageOutside_sublist (large := grabAllocationLog c pl s sp a domain env) _ space.allocation.image
    rw [← grab_allocation_log_parts]
    exact List.sublist_append_right _ _
  have bp : SegSt (0x80003714#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x11, BitVec.ofNat 64 (a - 8)⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩, ⟨Register.x16, BitVec.ofNat 64 (8 * (s.extra + 4))⟩,
       ⟨Register.x10, BitVec.ofNat 64 a⟩]
      (fun σ => Vsa.Sim.Code.CamlGrabAllocSuffixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨copied.good, by change pcOf d = some (0x80003714#64); simpa only [Nat.lt_irrefl, ite_false] using copied.pc,
      ⟨pcReg, headerReg, spReg, bytesReg, valueReg, trivial⟩,
      copied.good.minstret, copied.tick, grab_alloc_suffix_loaded copied.image, rfl, rfl⟩
  have run := tr_grab_alloc_suffix (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 (a - 8))
    (BitVec.ofNat 64 sp) (BitVec.ofNat 64 (8 * (s.extra + 4))) (BitVec.ofNat 64 a) d.σ.mem d.σ
  simp only [valueAddress, arityAddress, space.codeWrite.read.toNat, space.arityWrite.read.toNat,
    grab_restart_pc _ _ space.pcPositive, newSp, codeAddress, envAddress, extraAddress,
    space.frameReads.code.toNat, space.frameReads.environment.toNat, space.frameReads.extraArgs.toNat,
    show (0#64) + sign_extend (m := 64) (0x005#12) = 5#64 from by decide] at run
  obtain ⟨nb, after, _, steps, post⟩ := run space.codeWrite.lower space.codeWrite.upper space.codeWrite.htif space.codeWrite.aligned
    (image_entry_code suffixImage (List.mem_cons_self : (a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc - 1))) ∈
      grabSuffixLog a (pl.codeBase + 4 * (s.pc - 1))) (by decide) (by decide)) codeMemory codeWritten
    space.arityWrite.lower space.arityWrite.upper space.arityWrite.htif space.arityWrite.aligned
    (image_entry_code suffixImage (List.mem_cons_of_mem _ List.mem_cons_self : (a + 8, 8, 5#64) ∈
      grabSuffixLog a (pl.codeBase + 4 * (s.pc - 1))) (by decide) (by decide)) nextMemory arityWritten
    space.frameReads.extraArgs.lower space.frameReads.extraArgs.upper space.frameReads.extraArgs.htif (tag64 savedExtra) extraLoad.symm
    space.frameReads.code.lower space.frameReads.code.upper space.frameReads.code.htif
      (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) codeLoad.symm
    space.frameReads.environment.lower space.frameReads.environment.upper space.frameReads.environment.htif
      (word c (sp + 8 * (1 + s.extra) + 8)) envLoad.symm d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked (allowed := [Register.x8, Register.x9, Register.x14, Register.x15, Register.x18, Register.x25] ++ noiseRegs) (by decide)
  have observations : GrabPost c s pl sp dest savedEnv savedExtra rest (grabAllocationLog c pl s sp a domain env) after := by
    refine ⟨⟨post.pcAt, PinsHold.get post.pins ⟨3, by simp⟩, PinsHold.get post.pins ⟨1, by simp⟩,
      ⟨_, (frame.frame Register.x21 (by decide)).trans ((copied.frame.frame Register.x21 (by decide)).trans front.accu), ?_⟩,
      ⟨_, PinsHold.get post.pins ⟨2, by simp⟩, saved.environment⟩, ?_⟩,
      post.good, memory.trans fullMemory, frame.out.trans (copied.frame.out.trans front.frame.out), ?_⟩
    · simp only [grabState, valWord, space.allocation.placed, Option.map_some, Nat.mul_zero, Nat.add_zero]
    · have untagged : gpr after Layout.reg_extra = some (shift_bits_right_arith (tag64 savedExtra)
        (Sail.BitVec.extractLsb (0x01#6) 5 0)) := PinsHold.get post.pins ⟨0, by simp⟩
      simpa only [grabState, longVal_native, longVal_nonnegative savedExtra savedNonnegative] using untagged
    · exact loopRegisters_frame (fun r hr => frame.frame r (by revert r; decide)) loop
  exact ⟨nb, after, steps, grab_restore runtime h.toVmReprAt h.running.platform stack space.allocation
    (grab_allocation_layout h.toVmReprAt space environment stack observations.memory) observations⟩

end OCaml.Vm.Sim
