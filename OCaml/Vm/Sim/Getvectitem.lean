import OCaml.Vm.Sim.StackConsume
import OCaml.Vm.Sim.FieldRead
import OCaml.Vm.Sim.ValueIndex
import OCaml.Vm.Sim.GetvectitemSegment
import OCaml.Vm.Sim.GetvectitemPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- GETVECTITEM consumes a represented integer index and retains the selected
field as its new live accumulator. Both load windows are explicit. -/
theorem getvectitem_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k : Nat} {n : BitVec 63}
    {v : Val} {rest : List Val}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .GETVECTITEM c pl cp sp high)
    (stack : s.stack = .int n :: rest)
    (selected : FieldSelection s.heap pl s.accu n.toNat v l a k)
    (stackRead : RamReadAt sp 8)
    (fieldRead : RamReadAt (a + 8 * (k + n.toNat)) 8) :
    ∃ c', Plus c c' ∧ Running L P
      {s with pc := s.pc + 1, accu := v, stack := rest} c' := by
  have value := FieldSelection.read h.toVmReprAt (by simp [roots]) selected
  have source := represented_register h.accu selected.sourceWord
  have slot := stack_integer_word h.toVmReprAt stack
  have bound : 1 ≤ s.stack.length := by simp [stack]
  have dropped : s.stack.drop 1 = rest := by simp [stack]
  rw [← dropped]
  apply consume_value_arm stable h value.word value.root bound
  intro d dp
  have loaded : sign_extend (m := 64) (bytesT8 d.σ.mem sp) = tag64 n := by
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend,
      Sail.BitVec.signExtend, BitVec.signExtend_eq] using slot
  have address : BitVec.ofNat 64 (8 * n.toNat) + BitVec.ofNat 64 (a + 8 * k) =
      BitVec.ofNat 64 (a + 8 * (k + n.toNat)) := by
    rw [BitVec.add_comm]
    simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]
  have bp : SegSt (0x8000226c#64)
      [⟨Register.x9, BitVec.ofNat 64 sp⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩,
       ⟨Register.x21, BitVec.ofNat 64 (a + 8 * k)⟩]
      (fun σ => Vsa.Sim.Code.CamlGetvectitemLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x9 (by decide)).trans h.spReg, dp.nextCode,
       (dp.frame.frame Register.x21 (by decide)).trans source, trivial⟩,
      dp.good.minstret, dp.tick, getvectitem_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_getvectitem (BitVec.ofNat 64 sp)
    (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64)
    (BitVec.ofNat 64 (a + 8 * k)) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    BitVec.add_zero, stackRead.toNat, loaded, value_index_word,
    address, fieldRead.toNat] at run
  obtain ⟨nb, after, _, hb, post⟩ := run stackRead.lower stackRead.upper stackRead.htif
    fieldRead.lower fieldRead.upper fieldRead.htif d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, ?_, hm, frame.out, ?_⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) :=
      PinsHold.get post.pins ⟨3, by simp⟩
    simpa only [codePc_succ] using hp
  · have hp : gpr after Layout.reg_sp = some (BitVec.ofNat 64 sp + 8#64) :=
      PinsHold.get post.pins ⟨2, by simp⟩
    simpa only [Nat.mul_one, BitVec.ofNat_add] using hp
  · have hp : gpr after Layout.reg_accu = some
        (sign_extend (m := 64) (bytesT8 d.σ.mem (a + 8 * (k + n.toNat)))) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend,
      Sail.BitVec.signExtend, BitVec.signExtend_eq] using hp
  · intro r hr
    exact frame.frame r (by revert r; decide)

end OCaml.Vm.Sim
