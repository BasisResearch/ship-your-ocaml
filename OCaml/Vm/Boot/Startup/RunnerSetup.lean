import OCaml.Vm.Boot.Startup.RunnerDefaults

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Vsa.Sim.RegisterWrites

/-- Source model initialization followed by ELF-dependent register setup. -/
def runnerSetup (elf : ELF64File) : SailM PUnit := do
  Functions.sail_model_init ()
  initializeRegisters elf

structure RunnerSetupPost (elf : ELF64File) (before after : MState) : Prop
    extends ModelSeed after, RunnerDefaults after where
  run : (runnerSetup elf).run before = .ok () after
  memory : after.mem = before.mem
  output : after.sailOutput = before.sailOutput
  cycles : after.cycleCount = before.cycleCount

/-- Both initial setup stages succeed for arbitrary loaded memory and valid HTIF metadata. -/
theorem runner_setup (elf : ELF64File) (host : Nat) (s : MState)
    (ht : tohostMetadata elf = some host) : ∃ t, RunnerSetupPost elf s t := by
  obtain ⟨mid, model⟩ := model_init s
  let final := apply (elfRegisterAssignments elf host) mid
  refine ⟨final, {
    toModelSeed := initializer_model_seed elf host mid model.toModelSeed,
    toRunnerDefaults := runner_defaults elf host mid, run := ?_, memory := ?_, output := ?_, cycles := ?_ }⟩
  · change (Functions.sail_model_init () >>= fun _ => initializeRegisters elf).run s = _
    simp only [EStateM.run, bind, EStateM.bind]
    rw [show Functions.sail_model_init () s = .ok () mid from model.run]
    exact initializeRegisters_run elf host mid ht
  · exact (Vsa.Sim.RegisterWrites.memory _ _).trans model.memory
  · exact (Vsa.Sim.RegisterWrites.output _ _).trans model.output
  · exact (Vsa.Sim.RegisterWrites.cycles _ _).trans model.cycles

end OCaml.Vm.Boot.Startup
