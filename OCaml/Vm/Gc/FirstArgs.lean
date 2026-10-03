import OCaml.Vm.Gc.FirstForwarded

namespace OCaml.Vm.Gc.FirstCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

structure ArgsInput (target : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (argsRegs target)

structure ArgsPost (target : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost argsBlocks argsPc (argsRegs target) [] before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt call.pc after
  registers : GHolds after.σ [(11,target),(19,target)]

theorem args_machine {target c} (input : ArgsInput target c) :
    FnSummary argsPc (fun d => d = c) (ArgsPost target c) := by
  have summary := block_summary argsBlocks argsPc (argsRegs target) [] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [19]; decide,
      chainPlan_facts (args_code input.code) (args_access _ _), args_shape, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post, ?_, ?_, ?_⟩
  · rw [post.memory, args_log]; rfl
  · rw [PCAt, post.pc, args_exit]
  · simpa only [args_registers] using post.regs

end OCaml.Vm.Gc.FirstCall
