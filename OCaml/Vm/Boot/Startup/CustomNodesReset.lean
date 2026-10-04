import OCaml.Vm.Boot.Startup.CustomInitial
import OCaml.Vm.Boot.Startup.CustomNodes
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Actual reset execution after four custom-operation nodes are registered,
at the initializer's restoring epilogue. -/
structure ResetCustomNodes (initial after : Config) where
  entry : Config
  source : ResetCustomEntry initial entry
  H : List (Nat × Nat)
  domain : (firstDomainPtr.toNat, 928) ∈ H
  nodes : CustomNodes H (startupAllocatorCredits - 320) parameterStack jal_80004dd0_call.link
    (vsaReg entry 8) 0#64 entry after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem ResetCustomNodes.reset {initial after} (w : ResetCustomNodes initial after) :
    ElfResetReady elf initial := w.source.reset

theorem ResetCustomNodes.pc {initial after} (w : ResetCustomNodes initial after) :
    PCAt 0x80024ac0#64 after := w.nodes.bigarray.registration.publication.pc

theorem ResetCustomNodes.ready {initial after} (w : ResetCustomNodes initial after) :
    ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
      RuntimeReady H (startupAllocatorCredits - 320) (nativeStack parameterStack 16) 0x80024aa8#64 after :=
  ⟨_, w.nodes.member w.domain, w.nodes.bigarray.registration.ready⟩

theorem reset_custom_nodes_exists : ∃ initial after, Nonempty (ResetCustomNodes initial after) := by
  obtain ⟨initial, entry, ⟨w⟩⟩ := reset_custom_entry_exists
  obtain ⟨H, domain, ready⟩ := w.ready
  have capacity : startupAllocatorCredits - 192 = (startupAllocatorCredits - 320) + 128 := by decide
  rw [capacity] at ready
  obtain ⟨after, run, ⟨nodes⟩⟩ := (custom_nodes entry H (startupAllocatorCredits - 320) parameterStack
    jal_80004dd0_call.link (vsaReg entry 8) 0#64 ready (by constructor <;> decide)
    (library_gpr ready.platform (by decide) (by decide) rfl) w.custom_head).run entry ⟨w.call.pc, rfl⟩
  exact ⟨initial, after, ⟨entry, w, H, domain, nodes, w.run.trans run⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
