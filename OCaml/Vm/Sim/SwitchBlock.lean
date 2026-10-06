import OCaml.Vm.Sim.SwitchSemantics
import OCaml.Vm.Sim.StackPush
import OCaml.Vm.Sim.SwitchBlockSegment
import OCaml.Vm.Sim.SwitchBlockPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The block SWITCH path selects the table entry after the integer cases.
Header/tag selection, code words and architectural read geometry are explicit
observations, discharged from representation and placement. -/
theorem switch_block_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a tag dest : Nat} {sizes w : BitVec 32}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .SWITCH c pl cp sp high)
    (selected : SwitchTag s pl c a tag) (room : 8 ≤ a)
    (headerRead : RamReadAt (a - 8) 1)
    (count : OperandAt P pl (s.pc + 1) sizes)
    (operand : OperandAt P pl (s.pc + 2 + (sizes.toNat % 65536 + tag)) w)
    (jump : target s.pc 1 w.toInt = some dest) :
    ∃ after, Plus c after ∧ Running L P {s with pc := dest} after := by
  have source := represented_register h.accu selected.word
  apply control_arm stable h
  intro d dp v haccu _
  have bp : SegSt (0x8000314c#64)
      [⟨Register.x21, BitVec.ofNat 64 a⟩, ⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩]
      (fun σ => Vsa.Sim.Code.CamlSwitchBlockLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x21 (by decide)).trans source,
       (dp.frame.frame Register.x8 (by decide)).trans h.pc, trivial⟩,
      dp.good.minstret, dp.tick, switch_block_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have read := operand.read32 h.code dp.memory
  have half := switch_count_read count h.code dp.memory
  have header := selected.read dp.memory
  have run := tr_switch_block (BitVec.ofNat 64 a) (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
    d.σ.mem d.σ (loaded_80003158 := BitVec.ofNat 64 (sizes.toNat % 65536))
    (loaded_8000315c := BitVec.ofNat 64 tag) (loaded_8000316c := BitVec.ofInt 64 w.toInt)
  simp only [show sign_extend (m := 64) (0x001#12) = 1#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, push_address room, switch_block_low_bit a selected.even,
    codePc_succ, count.geometry.toNat, headerRead.toNat,
    show BitVec.ofNat 64 (sizes.toNat % 65536) + BitVec.ofNat 64 tag =
      BitVec.ofNat 64 (sizes.toNat % 65536 + tag) from (BitVec.ofNat_add _ _).symm,
    switch_index_scale, switch_table_word, operand.geometry.toNat, read] at run
  obtain ⟨nb, after, _, steps, post⟩ := run (by decide)
    count.geometry.lower (by have := count.geometry.upper; omega)
    (by
      rcases count.geometry.htif with left | right
      · apply Or.inl
        change pl.codeBase + 4 * (s.pc + 1) + 2 ≤ Layout.sym_tohost
        omega
      · exact Or.inr right) half.symm
    headerRead.lower headerRead.upper headerRead.htif header.symm
    operand.geometry.lower operand.geometry.upper operand.geometry.htif rfl d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨nb, after, steps, post.good, post.pcAt, ?_,
    (frame.frame Register.x21 (by decide)).trans haccu, memory, frame.out,
    immediate_preserved frame (by decide)⟩
  have pc : gpr after Layout.reg_pc = some
      ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) +
        (BitVec.ofInt 64 w.toInt <<< (2 : Nat))) := PinsHold.get post.pins ⟨0, by simp⟩
  have address : (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) +
      (BitVec.ofInt 64 w.toInt <<< (2 : Nat)) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    rw [show (8#64) = BitVec.ofNat 64 (4 * 2) from rfl, codePc_add]
    simpa only [Nat.add_assoc] using relative_code_word pl jump
  simpa only [address] using pc

/-- Match the successful block SWITCH rule to its represented table entry. -/
theorem switch_block_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a tag : Nat} {sizes w : BitVec 32}
    {table : List Int}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .SWITCH c pl cp sp high)
    (selected : SwitchTag s pl c a tag) (room : 8 ≤ a)
    (headerRead : RamReadAt (a - 8) 1)
    (count : OperandAt P pl (s.pc + 1) sizes)
    (operand : OperandAt P pl (s.pc + 2 + (sizes.toNat % 65536 + tag)) w)
    (entry : table[sizes.toNat % 65536 + tag]? = some w.toInt)
    (step : stepI P s ⟨.SWITCH, sizes.toInt :: table⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have guarded := step
  rw [switch_tag_step sizes.toInt table selected.tagOf] at step
  replace step := Res.unguard step
  have bound : tag < sizes.toInt.toNat / 65536 := by
    by_cases good : tag < sizes.toInt.toNat / 65536
    · exact good
    · simp only [good, ite_false, opt] at step
      cases step
  have positive : 0 ≤ sizes.toInt := by omega
  simp only [bound, ite_true, opt] at step
  have taken : opt (target s.pc 1 w.toInt) (fun t => .next {s with pc := t}) = .next s' := by
    simpa only [opt, switch_sizes_nat sizes positive, entry] using step
  cases jump : target s.pc 1 w.toInt with
  | none => simp [jump, opt] at taken
  | some dest =>
    have state : {s with pc := dest} = s' := by simpa [jump, opt] using taken
    rw [← state]
    exact switch_block_arm stable h selected room headerRead count operand jump

end OCaml.Vm.Sim
