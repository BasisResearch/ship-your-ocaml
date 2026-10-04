import OCaml.Vm.Gc.Generated.FfsZero
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.FfsZero
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The best-fit fallback supplies a zero filtered small-block bitmap. -/
structure Input (ra : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.FfsLoaded c.σ.mem
  registers : GHolds c.σ (regs ra)
  aligned : ra.toNat % 4 = 0

structure Post (ra : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs ra) [] before after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some 0
  memory : after.σ.mem = before.σ.mem

/-- The actual zero-input ffs callee returns zero, preserving all memory.
Its BlockPost carries the native register/output frame for the caller splice. -/
theorem zero {ra c} (input : Input ra c) :
    FnSummary pc (fun d => d = c) (Post ra c) := by
  have summary := block_summary blocks pc (regs ra) [] c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,10]; decide,
      chainPlan_facts (code_facts input.code) (access c.σ.mem ra input.aligned),chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,gholds_lookup _ post.regs (result ra),?_⟩
  · rw [PCAt,post.pc,endpoint ra input.aligned]
  · rw [post.memory,no_stores]
    rfl

end OCaml.Vm.Gc.FfsZero
