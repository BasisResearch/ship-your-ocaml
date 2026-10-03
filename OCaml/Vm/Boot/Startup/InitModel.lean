import OCaml.Vm.Boot.Startup.ResetPlatform
import OCaml.Vm.Boot.Startup.ConfigValid
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
structure InitModelPost (before after : MState) : Prop extends ResetPost before after where
  init_run : (init_model "").run before = .ok () after

/-- Validate the real configuration and run architectural reset. -/
theorem init_model_run (s : MState) (seed : ModelSeed s) (defs : RunnerDefaults s)
    (host : HostPins tohostAddr s) : ∃ t, InitModelPost s t := by
  obtain ⟨t, post⟩ := reset_run s seed defs host
  refine ⟨t, {toResetPost := post, init_run := ?_}⟩
  simp only [init_model, EStateM.run, Bind.bind, EStateM.bind]
  rw [show config_is_valid () s = .ok true s from config_valid s seed.pma]
  exact post.run
end OCaml.Vm.Boot.Startup
