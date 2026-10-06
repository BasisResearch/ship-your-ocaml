import OCaml.Vm.Sim.ClosureAllocInput
import OCaml.Vm.Sim.ClosureArithmetic
import OCaml.Vm.Sim.OperandFrame
import OCaml.Vm.Sim.ClosureSuffixSegment
import OCaml.Vm.Sim.ClosureSuffixPins
import OCaml.Vm.Sim.Immediate

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The actual CLOSURE suffix reads its preserved displacement, writes metadata,
and restores the represented newly allocated closure at the loop head. -/
theorem closure_finish {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high count dest a domain : Nat} {accu : BitVec 64} {ofs : BitVec 32}
    (runtime : AllocationRuntime L.runtimeOk c (closureAllocationLog c pl sp count dest a domain accu))
    (h : ArmInput L P s .CLOSURE c pl cp sp high) (value : valWord pl s.accu = some accu)
    (operand : OperandAt P pl (s.pc + 2) ofs) (jump : target s.pc 1 ofs.toInt = some dest)
    (space : ClosureWriteOk P s c pl cp sp high count dest a domain accu)
    (room : 0 < count → 8 ≤ sp) (metadata : ClosureMetadataWrites a)
    (front : ClosureReady c pl s.pc sp count a domain accu d) :
    ∃ nb after, StepsN nb d after ∧ Running L P (closureState s count dest) after := by
  have parts := closure_allocation_log_parts c pl sp count dest a domain accu
  have beforeSub : (closureReadyLog c sp count a domain accu).Sublist (closureAllocationLog c pl sp count dest a domain accu) := by
    rw [← parts]; exact List.sublist_append_left _ _
  have read := operand.read32_log h.code (outLRange_sublist beforeSub (space.payload.code _ _ operand.fetch)) front.memory
  have codeMember : (a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * dest)) ∈ closureAllocationLog c pl sp count dest a domain accu := by
    rw [← parts]; exact List.mem_append_right _ (by simp [closureSuffixLog])
  have arityMember : (a + 8, 8, 5#64) ∈ closureAllocationLog c pl sp count dest a domain accu := by
    rw [← parts]; exact List.mem_append_right _ (by simp [closureSuffixLog])
  have pc2 := codePc_add pl s.pc 2
  have pc3 := codePc_add pl s.pc 3
  have arityAddress : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
    rw [BitVec.ofNat_add]
  obtain ⟨m1, written1⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem a (sdData_val (BitVec.ofNat 64 (pl.codeBase + 4 * dest))) := ⟨_, rfl⟩
  obtain ⟨m2, written2⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m1 (a + 8) (sdData_val (5#64)) := ⟨_, rfl⟩
  have fullMemory : m2 = writeLog c.σ.mem (closureAllocationLog c pl sp count dest a domain accu) := by
    rw [written2, written1, front.memory, ← parts, writeLog_append]; rfl
  have bp : SegSt (0x80002a60#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x17, BitVec.ofNat 64 count⟩,
       ⟨Register.x23, BitVec.ofNat 64 (closureSource sp count)⟩,
       ⟨Register.x27, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2))⟩,
       ⟨Register.x10, BitVec.ofNat 64 a⟩, ⟨Register.x16, BitVec.ofNat 64 a⟩]
      (fun σ => Vsa.Sim.Code.CamlClosureSuffixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨front.good, front.pcAt, ⟨(front.frame.frame Register.x8 (by decide)).trans h.pc,
      front.fields.countReg, front.fields.sourceReg, front.fields.codeBase, front.value, front.targetReg, trivial⟩,
      front.good.minstret, front.tick, closure_suffix_loaded front.image, rfl, rfl⟩
  have run := tr_closure_suffix (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 count)
    (BitVec.ofNat 64 (closureSource sp count)) (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)))
    (BitVec.ofNat 64 a) (BitVec.ofNat 64 a) d.σ.mem d.σ
  simp only [arityAddress, show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) (0x00c#12) = 12#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    show sign_extend (m := 64) (0x005#12) = 5#64 from by decide,
    BitVec.add_zero, BitVec.zero_add, pc2, pc3, operand.geometry.toNat, metadata.code.read.toNat,
    metadata.arity.read.toNat, closure_capture_end sp count room] at run
  have first := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (sign_extend (m := 64) ofs) (by rw [read])
  simp only [closure_code_address pl jump] at first
  obtain ⟨nb, after, _, steps, post⟩ := first metadata.code.lower metadata.code.upper metadata.code.htif metadata.code.aligned
    (image_entry_code space.image codeMember (by decide) (by decide)) m1 written1
    metadata.arity.lower metadata.arity.upper metadata.arity.htif metadata.arity.aligned
    (image_entry_code space.image arityMember (by decide) (by decide)) m2 written2 d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := (front.frame.trans rawFrame).widenChecked (allowed := Register.x8 :: closureSetupWrites) (by decide)
  have observed : ClosurePost c s pl sp count dest a domain accu after := by
    refine ⟨⟨post.pcAt, PinsHold.get post.pins ⟨0, by simp⟩, PinsHold.get post.pins ⟨4, by simp⟩,
      ⟨BitVec.ofNat 64 a, ?_, ?_⟩, ?_, ?_⟩, post.good, memory.trans fullMemory, frame.out, ?_,
      frame.frame (gprReg 2) (by decide)⟩
    · exact (rawFrame.frame Register.x21 (by decide)).trans front.accu
    · simp only [closureState, valWord, space.placed, Option.map_some, Nat.mul_zero, Nat.add_zero]
    · obtain ⟨w, reg, value⟩ := h.env
      exact ⟨w, (frame.frame Register.x25 (by decide)).trans reg, value⟩
    · exact (frame.frame Register.x18 (by decide)).trans h.extra
    · exact loopRegisters_of (fun r hr => frame.frame r (by revert r; decide)) h.dispatch.loop
        (forall_saved (isSome_of_pin ((rawFrame.frame Register.x26 (by decide)).trans front.fields.fieldCount))
          (isSome_of_pin ((rawFrame.frame Register.x27 (by decide)).trans front.fields.codeBase)))
  exact ⟨nb, after, steps, closure_restore runtime h.toVmReprAt h.running.platform value space observed
    h.geometry h.native⟩

end OCaml.Vm.Sim
