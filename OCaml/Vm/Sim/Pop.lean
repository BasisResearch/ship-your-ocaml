import OCaml.Vm.Sim.StackConsume
import OCaml.Vm.Sim.IndexWord
import OCaml.Vm.Sim.PopSegment
import OCaml.Vm.Sim.PopPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- POP consumes a bounded nonnegative prefix and preserves the accumulator.
The operand window/sign are explicit adapter obligations, as for indexed loads. -/
theorem pop_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .POP c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) w)
    (nonnegative : 0 ≤ w.toInt)
    (bound : w.toInt.toNat ≤ s.stack.length) :
    ∃ c', Plus c c' ∧ Running L P
      {s with pc := s.pc + 2, stack := s.stack.drop w.toInt.toNat} c' := by
  obtain ⟨a, ha, value⟩ := h.accu
  apply consume_value_arm stable h value (fun l hl => Live.root (by simp [roots]) hl) bound
  intro d dp
  have read : bytesT4 d.σ.mem (pl.codeBase + 4 * (s.pc + 1)) = w :=
    operand.read32 h.code dp.memory
  have bp : SegSt (0x800023f8#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩]
      (fun σ => Vsa.Sim.Code.CamlPopLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
       (dp.frame.frame Register.x9 (by decide)).trans h.spReg, trivial⟩,
      dp.good.minstret, dp.tick, pop_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_pop (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
    (BitVec.ofNat 64 sp) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    codePc_succ, operand.geometry.toNat, read, index_word w nonnegative] at run
  obtain ⟨nb, after, _, hb, post⟩ := run operand.geometry.lower operand.geometry.upper
    operand.geometry.htif d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, ?_, hm, frame.out, ?_⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) :=
      PinsHold.get post.pins ⟨2, by simp⟩
    simpa only [show BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)) from codePc_add pl s.pc 2] using hp
  · have hp : gpr after Layout.reg_sp = some
        (BitVec.ofNat 64 sp + BitVec.ofNat 64 (8 * w.toInt.toNat)) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [BitVec.ofNat_add] using hp
  · exact (frame.frame Register.x21 (by decide)).trans
      ((dp.frame.frame Register.x21 (by decide)).trans ha)
  · intro r hr
    exact frame.frame r (by revert r; decide)

/-- Adapter from the actual POP semantic result. -/
theorem pop_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .POP c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) w)
    (nonnegative : 0 ≤ w.toInt)
    (step : stepI P s ⟨.POP, [w.toInt]⟩ = .next s') :
    ∃ c', Plus c c' ∧ Running L P s' c' := by
  replace step := Res.unguard step
  change (if s.stack.length < w.toInt.toNat then Res.wrong else
    .next {s with pc := s.pc + 2, stack := s.stack.drop w.toInt.toNat}) = .next s' at step
  split at step
  · cases step
  · have state := Res.next.inj step
    rw [← state]
    exact pop_arm stable h operand nonnegative (by omega)

end OCaml.Vm.Sim
