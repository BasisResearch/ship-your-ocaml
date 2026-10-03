import OCaml.Vm.Gc.ForwardedAdvance
import OCaml.Vm.Gc.FieldClassify

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Actual oldify arguments computed by the field load and destination sum. -/
def args (R : Nat → BitVec 64) (c : Config) (n : Nat) : BitVec 64 :=
  if n = 10 then word c (R 8).toNat else if n = 11 then R 18 + R 8 else R n

def carried (R : Nat → BitVec 64) : GRegs :=
  [(2,R 2),(8,R 8),(9,R 9),(1,R 1),(18,R 18),(19,R 19),(20,R 20),
   (21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

structure Input (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (OldifyEntry.regs R)
  source : ReadWindow (R 8) 8
  header : ReadWindow (R 19 - 8#64) 8
  domainReg : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  stackWindows : ∀ cell ∈ OldifyEntry.saves,
    WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  even : (word c (R 8).toNat).toNat % 2 = 0
  conditions : ForwardedCall.Conditions (args R c) domain c

theorem Input.read_input {R domain c} (input : Input R domain c) :
    FieldCopy.ReadInput (R 8) (R 18) (R 19) (R 9) c := by
  refine ⟨input.good,input.minstret,input.tick,input.code,?_,input.source⟩
  exact ⟨gholds_lookup _ input.registers rfl, gholds_lookup _ input.registers rfl,
    gholds_lookup _ input.registers rfl, gholds_lookup _ input.registers rfl, True.intro⟩

theorem Input.carried {R domain c} (input : Input R domain c) : GHolds c.σ (carried R) := by
  apply gholds_select input.registers
  intro n v member
  simp only [ForwardedField.carried, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem classifier_carried {R domain before after}
    (post : FieldCopy.ClassifiedPost (R 8) (R 18) (R 19) (R 9) domain before after)
    (holds : GHolds before.σ (carried R)) : GHolds after.σ (carried R) := by
  apply gholds_of_frame post.native _ (by change KeysOK [2,8,9,1,18,19,20,21,22,23,24,25]; decide)
    ?_ ?_ holds
  · change ∀ n ∈ [2,8,9,1,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · change ∀ n ∈ [2,8,9,1,18,19,20,21,22,23,24,25], ∀ m ∈ [10,11,14,15], (gprReg m == gprReg n) = false
    decide

theorem classifier_input {R domain before after} (input : Input R domain before)
    (post : FieldCopy.ClassifiedPost (R 8) (R 18) (R 19) (R 9) domain before after) :
    ForwardedCall.Input (args R before) domain after := by
  have keep := classifier_carried post input.carried
  have combined : GHolds after.σ
      ((10,word before (R 8).toNat) :: (11,R 18 + R 8) :: carried R) :=
    ⟨gholds_lookup _ post.registers rfl, gholds_lookup _ post.registers rfl, keep⟩
  refine {
    toConditions := input.conditions.memory_eq post.memory,
    entry := {
      good := post.good, minstret := post.minstret, tick := post.tick
      code := post.memory ▸ input.oldifyCode, registers := ?_
      windows := input.stackWindows, even := input.even } }
  apply gholds_select combined
  intro n v member
  simp only [OldifyEntry.regs, OldifyEntry.entryKeys, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem forwarded_field {R domain c} (input : Input R domain c) :
    FnSummary FieldCopy.pc (fun d => d = c)
      (fun after => MopupCall.AdvancedPost (args R c) c after [1,8,9,10,11,12,14,15]) := by
  constructor
  apply Vsa.Logic.Triple.seq (FieldCopy.classify_field input.read_input input.even
    input.domainReg input.conditions.root input.conditions.domainWindows).run
  intro middle classified
  have young : (Young.lowerWord domain c).toNat < (word c (R 8).toNat).toNat ∧
      (word c (R 8).toNat).toNat < (Young.upperWord domain c).toNat :=
    ⟨input.conditions.lower, input.conditions.upper⟩
  have pc : PCAt MopupCall.call.pc middle := by
    simpa only [if_pos young, Young.oldifyPc, MopupCall.call] using classified.pc
  obtain ⟨after, run, advanced⟩ := (MopupCall.forwarded_advance
    (classifier_input input classified) classified.code input.header).run middle ⟨pc,rfl⟩
  refine ⟨after, run, ⟨advanced.good, advanced.minstret, advanced.tick, advanced.code,
    ?_, ?_, ?_, advanced.registers, advanced.link, advanced.output.trans classified.output, ?_⟩⟩
  · simpa only [ForwardedCall.effect, word, classified.memory] using advanced.memory
  · simpa only [word, classified.memory] using advanced.destination
  · have same : MopupCall.againAfterCall (args R c) middle = MopupCall.againAfterCall (args R c) c := by
      unfold MopupCall.againAfterCall ForwardedCall.effect word
      rw [classified.memory]
    simpa only [same] using advanced.pc
  · intro r noise untouched
    apply (advanced.native r noise ?_).trans (classified.native r noise ?_)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

end OCaml.Vm.Gc.ForwardedField
