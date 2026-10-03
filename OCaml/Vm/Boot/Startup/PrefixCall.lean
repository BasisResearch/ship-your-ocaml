import OCaml.Vm.Primitives.Call
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Compose a generated saving prefix with its generated JAL while retaining the
exact store log and complete ABI frame. Shared by startup call sites. -/
theorem prefix_call_post {writes log before mid after pc value target result input output}
    (front : WriteRegistersPost writes log before pc value input mid)
    (call : RegistersPost [1] mid.σ.mem mid target result output after) :
    WriteRegistersPost (writes ++ [1]) log before target result output after := by
  have effects := front.toEffectPost.trans call.toEffectPost
  exact ⟨⟨effects.good, effects.image, effects.minstret, effects.tick, effects.pc,
    effects.result, call.memory.trans front.memory, effects.output, effects.frame⟩, call.regs⟩
end OCaml.Vm.Boot.Startup
