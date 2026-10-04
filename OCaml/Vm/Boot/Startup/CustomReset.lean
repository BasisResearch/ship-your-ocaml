import OCaml.Vm.Boot.Startup.CustomFinish
import OCaml.Vm.Boot.Startup.CustomNodesReset
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Actual reset execution after the complete native custom-operation initializer. -/
structure ResetCustomReturned (initial after : Config) where
  atReturn : Config
  source : ResetCustomNodes initial atReturn
  returned : CustomReturned source.H (startupAllocatorCredits - 320) parameterStack jal_80004dd0_call.link
    (vsaReg source.entry 8) 0#64 source.entry after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem ResetCustomReturned.reset {initial after} (w : ResetCustomReturned initial after) :
    ElfResetReady elf initial := w.source.reset

theorem ResetCustomReturned.pc {initial after} (w : ResetCustomReturned initial after) :
    PCAt 0x80004dd4#64 after := w.returned.post.pc

theorem ResetCustomReturned.ready {initial after} (w : ResetCustomReturned initial after) :
    ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
      RuntimeReady H (startupAllocatorCredits - 320) parameterStack jal_80004dd0_call.link after :=
  ⟨_, w.returned.nodes.member w.source.domain, w.returned.ready⟩

theorem reset_custom_returned_exists : ∃ initial after, Nonempty (ResetCustomReturned initial after) := by
  obtain ⟨initial, atReturn, ⟨w⟩⟩ := reset_custom_nodes_exists
  obtain ⟨after, run, ⟨returned⟩⟩ := (custom_finish w.entry atReturn w.H (startupAllocatorCredits - 320)
    parameterStack jal_80004dd0_call.link (vsaReg w.entry 8) 0#64 w.nodes
    (by constructor <;> decide) (by decide)).run atReturn ⟨w.pc, rfl⟩
  exact ⟨initial, after, ⟨atReturn, w, returned, w.run.trans run⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
