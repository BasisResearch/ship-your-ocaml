import OCaml.Vm.Gc.FirstFieldInput

namespace OCaml.Vm.Gc.FirstField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- First-field classification, destination setup and complete oldify call
update the copied object's first word, retaining the restored native state. -/
structure Post (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem (ForwardedCall.effect (FirstCall.linked (args R)) before)
  first : word after (R 19).toNat = word before (R 10).toNat
  pc : PCAt FirstCall.setupPc after
  registers : GHolds after.σ (OldifyEntry.callerRegs (FirstCall.linked (args R)))
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,11,12,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Real first-field path for an already-forwarded young child. The queue
pop supplies the loaded child/parity boundary; no callee run is assumed. -/
theorem forwarded {R domain c} (input : Input R domain c) :
    FnSummary FirstYoung.pc (fun d => d = c) (Post R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (FirstYoung.classify input.young_input).run
  intro middle classified
  have kept := classifier_carried classified input.registers
  have argsInput : FirstCall.ArgsInput (R 19) middle :=
    ⟨classified.machine.good, classified.machine.minstret, classified.machine.tick, classified.code,
      ⟨gholds_lookup _ kept rfl, True.intro⟩⟩
  have pc : PCAt FirstCall.argsPc middle := by
    have young : (Young.lowerWord domain c).toNat < (R 10).toNat ∧
        (R 10).toNat < (Young.upperWord domain c).toNat :=
      ⟨input.conditions.lower, input.conditions.upper⟩
    simpa only [ite_eq_left young, FirstYoung.site, FirstYoung.oldifyPc, FirstCall.argsPc] using classified.pc
  obtain ⟨entered, prefixRun, prepared⟩ := (FirstCall.args_machine argsInput).run middle ⟨pc,rfl⟩
  have callee := callee_input input classified prepared
  have memory := prepared.memory.trans classified.memory
  obtain ⟨after, callRun, returned⟩ := (FirstCall.forwarded_resume callee
    (prepared.memory ▸ classified.code)).run entered ⟨prepared.pc,rfl⟩
  refine ⟨after, prefixRun.trans callRun, ⟨returned.body.good, returned.body.minstret,
    returned.body.tick, returned.code, returned.body.code, ?_, ?_, returned.body.pc,
    returned.body.registers, returned.body.output.trans (prepared.machine.output.trans classified.machine.output), ?_⟩⟩
  · simpa only [ForwardedCall.effect, word, memory] using returned.body.memory
  · simpa [FirstCall.linked, OldifyBridge.linked, args, word, memory] using returned.body.root
  · intro r noise untouched
    apply (OldifyBridge.abi_frame FirstCall.site returned.body callee.entry.registers r noise ?_).trans
    apply (prepared.machine.frame_subset FirstCall.args_written r noise ?_).trans
    apply classified.machine.frame_subset (FirstYoung.written _ _) r noise
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact untouched _ (by decide)
    · intro n member
      have same : n = 11 := List.mem_singleton.mp member
      subst n
      exact untouched 11 (by decide)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

end OCaml.Vm.Gc.FirstField
