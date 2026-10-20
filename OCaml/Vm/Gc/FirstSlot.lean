import OCaml.Vm.Gc.FirstField
import OCaml.Vm.Gc.MopupSlot

/-! # Mopup's first field over any route

`FirstField.forwarded` for any `caml_oldify_one` route: the young
classifier, the argument block (`a1 = s3`, the copy), then the call through
`FirstCall.site` with a `SlotCall` supplied at the jumped-to state, and the
return continuation to the field setup (`FirstCall.setupPc`). -/
namespace OCaml.Vm.Gc.FirstField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The first field is a young pointer. -/
structure SlotInput (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (carried R)
  runtime : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  root : word c Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  lower : (Young.lowerWord domain c).toNat < (R 10).toNat
  upper : (R 10).toNat < (Young.upperWord domain c).toNat

theorem SlotInput.young_input {R domain c} (input : SlotInput R domain c) : Young.Input (R 10) domain c :=
  ⟨input.good, input.minstret, input.tick, input.code,
    ⟨input.runtime, gholds_lookup _ input.registers rfl, True.intro⟩, input.root, input.windows⟩

/-- **The first field over any route**, from the classifier to the field setup. -/
theorem first_slot {R : Nat → BitVec 64} {domain : BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (input : SlotInput R domain c)
    (supply : ∀ c' e, c'.σ.mem = c.σ.mem →
      SegCallFacts [] (OldifyBridge.carried (args R)) [] OldifyEntry.pc FirstCall.site.call.link c' e →
      SlotCall (FirstCall.site.toSlot.linked (args R)) copies pl e)
    (kept : ∀ c' e copies' mid, c'.σ.mem = c.σ.mem →
      SegCallFacts [] (OldifyBridge.carried (args R)) [] OldifyEntry.pc FirstCall.site.call.link c' e →
      SlotDone (FirstCall.site.toSlot.linked (args R)) copies copies' pl e mid →
      Code.Caml_oldify_mopupLoaded mid.σ.mem) :
    FnSummary FirstYoung.pc (fun d => d = c) (fun after => ∃ c', c'.σ.mem = c.σ.mem ∧
      OldifyBridge.SlotResumed FirstCall.site FirstCall.resume (args R) copies pl c' after) := by
  constructor
  apply Vsa.Logic.Triple.seq (FirstYoung.classify input.young_input).run
  intro middle classified
  have keptRegs := classifier_carried classified input.registers
  have argsInput : FirstCall.ArgsInput (R 19) middle :=
    ⟨classified.machine.good, classified.machine.minstret, classified.machine.tick, classified.code,
      ⟨gholds_lookup _ keptRegs rfl, True.intro⟩⟩
  have pc : PCAt FirstCall.argsPc middle := by
    have young : (Young.lowerWord domain c).toNat < (R 10).toNat ∧
        (R 10).toNat < (Young.upperWord domain c).toNat := ⟨input.lower, input.upper⟩
    simpa only [ite_eq_left young, FirstYoung.site, FirstYoung.oldifyPc, FirstCall.argsPc] using classified.pc
  obtain ⟨entered, prefixRun, prepared⟩ := (FirstCall.args_machine argsInput).run middle ⟨pc, rfl⟩
  have memory : entered.σ.mem = c.σ.mem := prepared.memory.trans classified.memory
  have combined : GHolds entered.σ ((11, R 19) :: carried R) :=
    ⟨gholds_lookup _ prepared.registers rfl, args_carried prepared keptRegs⟩
  have calleeRegs : GHolds entered.σ (OldifyBridge.carried (args R)) := by
    apply gholds_select combined
    intro n v member
    simp only [OldifyBridge.carried, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl
  have code : Code.Caml_oldify_mopupLoaded entered.σ.mem := prepared.memory ▸ classified.code
  obtain ⟨after, callRun, returned⟩ := (OldifyBridge.slot_resume FirstCall.site FirstCall.resume code
    prepared.machine.good prepared.machine.tick prepared.machine.minstret calleeRegs
    (fun e called => supply entered e memory called)
    (fun e copies' mid called done => kept entered e copies' mid memory called done)).run entered ⟨prepared.pc, rfl⟩
  exact ⟨after, prefixRun.trans callRun, entered, memory, returned⟩

end OCaml.Vm.Gc.FirstField
