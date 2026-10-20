import OCaml.Vm.Primitives.IndirectCall
import OCaml.Vm.Boot.Startup.RuntimeReady
import OCaml.Vm.Boot.Startup.GprsSame

/-! An indirect call (`jalr ra, 0(rs)`) under allocator readiness: the
`jalr` counterpart of `OCaml.Vm.Gc.ready_call`. Stated for any call site. -/
namespace OCaml.Vm.Boot.Startup
variable {live : Nat → Prop}
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- After an indirect call: readiness with the new link, the target reached,
the carried argument registers, memory unchanged, only `ra` written. -/
structure IndirectDone (live : Nat → Prop) (H : List (Nat × Nat)) (capacity : Nat) (sp : BitVec 64)
    (call : IndirectCallInstr) (target : BitVec 64) (args : GRegs) (before after : Config) : Prop where
  ready : RuntimeReadyL live H capacity sp call.link after
  pc : after.σ.regs.get? Register.PC = some target
  regs : GHolds after.σ args
  memory : after.σ.mem = before.σ.mem
  same : GprsSame before after [1]

theorem ready_indirect {H capacity sp ra} {call : IndirectCallInstr} (shape : IndirectShape call)
    (decode : IndirectDecode call) {c : Config} (pins : IndirectPins call c) (ready : RuntimeReadyL live H capacity sp ra c)
    (args : GRegs) (holds : GHolds c.σ args) (keys : KeysOK (keysG args)) (avoid : KeysAvoidRa args)
    (value : BitVec 64) (source : lookupG call.source args = some value)
    (aligned : (call.target value).toNat % 4 = 0) {result : BitVec 64} (resultReg : lookupG 10 args = some result)
    (linkAligned : call.link.toNat % 4 = 0) :
    FnSummary call.pc (fun d => d = c) (IndirectDone live H capacity sp call (call.target value) args c) := by
  apply (indirect_registers_summary shape decode c pins ready.good ready.image ready.tick ready.minstret
    args holds keys avoid value source aligned resultReg).weaken (fun _ h => h)
  intro after post
  have same : GprsSame c after [1] := GprsSame.of_post post (by decide)
  refine ⟨?_, post.pc, post.regs.2, post.memory, same⟩
  exact ready.effect post (by decide) (by simp [keysG]) (by decide)
    (same.get (by decide) (by decide) (by decide) ready.stack) post.regs.1 linkAligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)

end OCaml.Vm.Boot.Startup
