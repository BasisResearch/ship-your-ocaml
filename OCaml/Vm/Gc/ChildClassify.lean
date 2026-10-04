import OCaml.Vm.Gc.Generated.ChildClassify
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.ChildClassify
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

structure Input (child : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs child)

structure Post (child : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (blocks (even child)) pc (regs child) [] before after
  pc : PCAt (exitPc (even child)) after
  registers : GHolds after.σ (classified child)
  memory : after.σ.mem = before.σ.mem
  code : Code.Caml_oldify_oneLoaded after.σ.mem

/-- Execute either actual child tag branch, including the immediate jump.
No memory observations or write-window premises are needed by this test. -/
theorem classify {child c} (input : Input child c) :
    FnSummary pc (fun d => d = c) (Post child c) := by
  have summary := block_summary (blocks (even child)) pc (regs child) [] c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [15]; decide,
      chainPlan_facts (code_facts input.code _) (access _ _),chain_ok _,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory,no_stores]; rfl
  refine ⟨post,?_,?_,memory,memory ▸ input.code⟩
  · rw [PCAt,post.pc,endpoint]
  · simpa only [registers] using post.regs

end OCaml.Vm.Gc.ChildClassify
