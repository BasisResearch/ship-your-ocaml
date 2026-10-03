import OCaml.Vm.Gc.FirstArgs
import OCaml.Vm.Gc.FirstYoungAccess
import OCaml.Vm.Gc.ForwardedField

namespace OCaml.Vm.Gc.FirstField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The first-field destination is the copied object's base. -/
def args (R : Nat → BitVec 64) (n : Nat) : BitVec 64 := if n = 11 then R 19 else R n

/-- Argument setup overwrites x11; all other callee input values are carried. -/
def carried (R : Nat → BitVec 64) : GRegs := (10,R 10) :: ForwardedField.carried R

structure Input (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (carried R)
  runtime : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  windows : ∀ cell ∈ OldifyEntry.saves,
    WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  even : (R 10).toNat % 2 = 0
  conditions : ForwardedCall.Conditions (args R) domain c

theorem Input.young_input {R domain c} (input : Input R domain c) : Young.Input (R 10) domain c :=
  ⟨input.good, input.minstret, input.tick, input.code,
    ⟨input.runtime, gholds_lookup _ input.registers rfl, True.intro⟩,
    input.conditions.root, input.conditions.domainWindows⟩

/-- A finite frame adapter shared by the classifier and argument setup. -/
theorem carried_of_frame {R} {writes : List Nat} {before after : Config}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r)
    (outside : ∀ n ∈ [10,2,8,9,1,18,19,20,21,22,23,24,25],
      ∀ m ∈ writes, (gprReg m == gprReg n) = false)
    (holds : GHolds before.σ (carried R)) : GHolds after.σ (carried R) := by
  apply gholds_of_frame frame (carried R) (by change KeysOK [10,2,8,9,1,18,19,20,21,22,23,24,25]; decide)
    ?_ outside holds
  change ∀ n ∈ [10,2,8,9,1,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
  decide

theorem classifier_carried {R domain before after}
    (post : Young.SiteResult FirstYoung.site (R 10) domain before after)
    (holds : GHolds before.σ (carried R)) : GHolds after.σ (carried R) :=
  carried_of_frame (post.machine.frame_subset (FirstYoung.written _ _)) (by decide) holds

theorem args_carried {R before after} (post : FirstCall.ArgsPost (R 19) before after)
    (holds : GHolds before.σ (carried R)) : GHolds after.σ (carried R) :=
  carried_of_frame (post.machine.frame_subset FirstCall.args_written) (by decide) holds

theorem callee_input {R domain before middle after} (input : Input R domain before)
    (classified : Young.SiteResult FirstYoung.site (R 10) domain before middle)
    (prepared : FirstCall.ArgsPost (R 19) middle after) :
    ForwardedCall.Input (args R) domain after := by
  have memory := prepared.memory.trans classified.memory
  have kept := args_carried prepared (classifier_carried classified input.registers)
  have combined : GHolds after.σ ((11,R 19) :: carried R) :=
    ⟨gholds_lookup _ prepared.registers rfl, kept⟩
  refine {
    toConditions := input.conditions.memory_eq memory
    entry := {
      good := prepared.machine.good, minstret := prepared.machine.minstret, tick := prepared.machine.tick
      code := memory ▸ input.oldifyCode, registers := ?_
      windows := input.windows, even := input.even } }
  apply gholds_select combined
  intro n v member
  simp only [OldifyEntry.regs, OldifyEntry.entryKeys, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

end OCaml.Vm.Gc.FirstField
