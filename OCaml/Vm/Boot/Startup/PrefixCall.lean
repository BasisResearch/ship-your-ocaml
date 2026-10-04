import OCaml.Vm.Primitives.Call
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Compose a generated prefix with a memory-preserving continuation, retaining
its exact store log and the complete register/output frame. -/
theorem prefix_readonly_post {writes writesTail log before mid after pc value target result input output}
    (front : WriteRegistersPost writes log before pc value input mid)
    (call : RegistersPost writesTail mid.σ.mem mid target result output after) :
    WriteRegistersPost (writes ++ writesTail) log before target result output after := by
  have effects := front.toEffectPost.trans call.toEffectPost
  exact ⟨⟨effects.good, effects.image, effects.minstret, effects.tick, effects.pc,
    effects.result, call.memory.trans front.memory, effects.output, effects.frame⟩, call.regs⟩
/-- A generated direct call is the one-register special case. -/
theorem prefix_call_post {writes log before mid after pc value target result input output}
    (front : WriteRegistersPost writes log before pc value input mid)
    (call : RegistersPost [1] mid.σ.mem mid target result output after) :
    WriteRegistersPost (writes ++ [1]) log before target result output after :=
  prefix_readonly_post front call
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim
/-- Read the return link directly from a summary's finite register interface. -/
theorem RegistersPost.leaf {writes mem before after pc value regs ra}
    (post : RegistersPost writes mem before pc value regs after)
    (link : lookupG 1 regs = some ra) (aligned : ra.toNat % 4 = 0) : LeafInput ra after :=
  ⟨post.good, post.image, post.minstret, gholds_lookup _ post.regs link, aligned, post.tick⟩
end OCaml.Vm.Primitives
