import OCaml.Vm.Boot.Startup.InitializeRegisters
import OCaml.Vm.Boot.Startup.ModelInit

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Vsa.Sim.RegisterWrites

/-- Seed controls written by model initialization and retained by the runner. -/
def seedControls : List Register :=
  [.misa, .mstatus, .mseccfg, .senvcfg, .menvcfg, .pc_reset_address, .pma_regions, .sig_meip, .sig_seip]

/-- A finite certificate over the source-derived assignment list, not a state replay. -/
theorem register_tail_keeps_seed :
    ∀ x ∈ registerWrites.entries100, x.1 ∉ seedControls := by decide +kernel

theorem initializer_keeps_seed (elf : ELF64File) (host : Nat) (s : MState)
    (r : Register) (member : r ∈ seedControls) :
    (apply (elfRegisterAssignments elf host) s).regs.get? r = s.regs.get? r := by
  apply registers_frame
  intro x hx eq
  subst r
  simp only [elfRegisterAssignments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | tail
  · simp [seedControls] at member
  · simp [seedControls] at member
  · simp [seedControls] at member
  · exact register_tail_keeps_seed x tail member

/-- Observe an initialized tail register without reducing an accumulated machine state. -/
theorem initializer_read_tail (elf : ELF64File) (host : Nat) (s : MState)
    (r : Register) (v : RegisterType r)
    (value : lastValue registerWrites.entries100 r = some v) :
    (apply (elfRegisterAssignments elf host) s).regs.get? r = some v :=
  apply_read_append _ registerWrites.entries100 s r v value

theorem initializer_model_seed (elf : ELF64File) (host : Nat) (s : MState)
    (seed : ModelSeed s) : ModelSeed (apply (elfRegisterAssignments elf host) s) := by
  constructor <;> rw [initializer_keeps_seed elf host s _ (by decide)]
  all_goals first | exact seed.misa | exact seed.mstatus | exact seed.mseccfg |
    exact seed.senvcfg | exact seed.menvcfg | exact seed.resetPC | exact seed.pma |
    exact seed.meip | exact seed.seip

end OCaml.Vm.Boot.Startup
