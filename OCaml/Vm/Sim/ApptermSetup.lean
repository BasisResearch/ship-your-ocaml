import OCaml.Vm.Sim.ApptermInput
import OCaml.Vm.Sim.ApptermPrefixSegment
import OCaml.Vm.Sim.ApptermPrefixPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Generic APPTERM prepares its exact high-to-low argument-copy state through
the generated two-operand prefix, with no machine execution premise. -/
theorem appterm_setup {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {count slots : BitVec 32}
    (h : ArmInput L P s .APPTERM c pl cp sp high)
    (countAt : OperandAt P pl (s.pc + 1) count) (slotsAt : OperandAt P pl (s.pc + 2) slots)
    (positive : 0 < count.toInt) (nonnegative : 0 ≤ slots.toInt)
    (space : ApptermWriteOk P s c pl cp sp high count.toInt.toNat slots.toInt.toNat)
    (dp : DispatchPost c .APPTERM (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ nb after, StepsN nb d after ∧ ApptermCopyStart c sp count.toInt.toNat slots.toInt.toNat after := by
  have countPositive : 0 < count.toInt.toNat := by omega
  have countSmall := word32_nat_small count
  have room := space.copy.room
  have targetRoom : 8 ≤ tailcallStart sp count.toInt.toNat slots.toInt.toNat :=
    Nat.le_trans room space.copy.direction
  have targetWord : BitVec.ofNat 64 sp + Sail.shift_bits_left
      (sign_extend (m := 64) slots - sign_extend (m := 64) count)
      (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (tailcallStart sp count.toInt.toNat slots.toInt.toNat) := by
    rw [nonnegative_word32 slots nonnegative, nonnegative_word32 count (by omega)]
    exact appterm_base_word sp slots.toInt.toNat count.toInt.toNat space.fits (by omega)
  have sourceWord := appterm_cursor_word sp count.toInt.toNat room countPositive
  have destinationWord := appterm_cursor_word (tailcallStart sp count.toInt.toNat slots.toInt.toNat)
    count.toInt.toNat targetRoom countPositive
  have bp : SegSt (0x80002a88#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x9, BitVec.ofNat 64 sp⟩]
      (fun σ => Vsa.Sim.Code.CamlApptermPrefixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x9 (by decide)).trans h.spReg, trivial⟩,
      dp.good.minstret, dp.tick, appterm_prefix_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_appterm_prefix (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 (4 * 2) from by decide,
    codePc_succ, codePc_add, countAt.geometry.toNat, slotsAt.geometry.toNat] at run
  have loaded := run countAt.geometry.lower countAt.geometry.upper countAt.geometry.htif
    (sign_extend (m := 64) count) (by rw [countAt.read32 h.code dp.memory])
    slotsAt.geometry.lower slotsAt.geometry.upper slotsAt.geometry.htif
    (sign_extend (m := 64) slots) (by rw [slotsAt.read32 h.code dp.memory])
  simp only [apply_count_word count positive, targetWord, sourceWord, destinationWord] at loaded
  obtain ⟨nb, after, _, steps, post⟩ := loaded (appterm_prefix_guard count.toInt.toNat countSmall) d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have fullMemory := memory.trans dp.memory
  have image : ExecutableImage after :=
    ⟨fun i hi => by rw [fullMemory]; exact h.dispatch.image.text i hi,
      fun i hi => by rw [fullMemory]; exact h.dispatch.image.rodata i hi⟩
  have frame := (dp.frame.trans rawFrame).widenChecked (allowed := apptermSetupWrites) (by decide)
  refine ⟨nb, after, steps, ?_⟩
  constructor
  · have length : (stackWords c sp count.toInt.toNat).length = count.toInt.toNat := by simp [stackWords]
    refine ⟨post.good, post.tick, image, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [length, countPositive, ite_true]
      exact post.pcAt
    · simp only [length]
      exact PinsHold.get post.pins ⟨3, by simp⟩
    · simp only [length]
      exact PinsHold.get post.pins ⟨1, by simp⟩
    · have counter : gpr after 14 = some
          (BitVec.ofNat 64 (count.toInt.toNat - 1) + sign_extend (m := 64) (0x000#12)) :=
        PinsHold.get post.pins ⟨2, by simp⟩
      simpa only [length, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
        BitVec.add_zero, appterm_counter_word _ countPositive] using counter
    · exact PinsHold.get post.pins ⟨0, by simp⟩
    · rw [reverse_copy_log_initial]; rfl
    · exact (StepFrameOut.refl after.σ).widenChecked (allowed := backwardWrites) (by decide)
  · exact PinsHold.get post.pins ⟨5, by simp⟩
  · exact PinsHold.get post.pins ⟨4, by simp⟩
  · exact fullMemory
  · exact frame

end OCaml.Vm.Sim
