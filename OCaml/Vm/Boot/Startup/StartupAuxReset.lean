import OCaml.Vm.Boot.Startup.StartupAuxReady
import OCaml.Vm.Boot.Startup.StartupControls
import OCaml.Vm.Boot.Startup.CamlAux
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- The concrete reset run after the once-only startup check and count update. -/
structure ResetStartupAuxReturned (initial after : Config) where
  source : Config
  parameter : ResetParameterReturned initial source
  called : Config
  call : WriteRegistersPost [10, 1] [] source jal_80004da4_call.target 0#64
    [(1, jal_80004da4_call.link), (10, 0#64), (2, parameterStack)] called
  post : WriteRegistersPost [1, 2, 10, 12, 13, 14, 15]
    (startupAuxLog parameterStack jal_80004da4_call.link) called jal_80004da4_call.link 1#64
    (startupAuxRegs parameterStack jal_80004da4_call.link) after
  run : Steps (Vsa.Densify.fillZero initial) after
  ready : ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
    RuntimeReady H (startupAllocatorCredits - 192) parameterStack jal_80004da4_call.link after

theorem ResetStartupAuxReturned.reset {initial after} (w : ResetStartupAuxReturned initial after) :
    ElfResetReady elf initial := w.parameter.reset

/-- Compose generated caller load/JAL and native startup summary into the
pinned ELF's own reset run, with its initial BSS flag values supplied by history. -/
theorem reset_startup_aux_returned_exists : ∃ initial after, Nonempty (ResetStartupAuxReturned initial after) := by
  obtain ⟨initial, source, ⟨w⟩⟩ := reset_parameter_returned_exists
  obtain ⟨H, domain, ready⟩ := w.ready
  have regs : GHolds source.σ (camlAuxInput parameterStack jal_80004d98_call.link) :=
    ⟨ready.stack, ready.raReg, trivial⟩
  obtain ⟨called, run1, call⟩ := (caml_aux_call source _ _ ready.toLeafInput regs w.controls.cleanup).run source ⟨w.post.pc, rfl⟩
  have ready' : RuntimeReady H (startupAllocatorCredits - 192) parameterStack jal_80004da4_call.link called := by
    apply ready.effect call (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ call.regs (by rfl))
      (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    · intro a ha; rfl
    · intro a ha; rfl
    · intro a ha; exact ha
  have input : StartupAuxInput parameterStack jal_80004da4_call.link called := {
    toLeafInput := ready'.toLeafInput
    frame := by constructor <;> decide
    regs := holds_project call.regs (by simp [startupAuxInput, lookupG])
    shutdown := by rw [call.memory]; exact w.controls.shutdown
    count := by rw [call.memory]; exact w.controls.count }
  obtain ⟨after, run2, post⟩ := (startup_aux called _ _ input).run called ⟨call.pc, rfl⟩
  exact ⟨initial, after, ⟨source, w, called, call, post, w.run.trans (run1.trans run2), H, domain,
    startup_aux_ready ready' input.frame post⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
