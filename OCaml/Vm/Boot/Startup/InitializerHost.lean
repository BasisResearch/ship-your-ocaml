import OCaml.Vm.Boot.Startup.InitializeRegisters
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Vsa.Sim.RegisterWrites

/-- Host-interface registers set from the ELF's tohost section metadata. -/
structure HostPins (host : Nat) (s : MState) : Prop where
  address : s.regs.get? .htif_tohost = some (BitVec.ofNat 64 host)
  base : s.regs.get? .htif_tohost_base = some (some (BitVec.ofNat 64 host))

/-- The source-generated tail does not overwrite the ELF-dependent header. -/
theorem initializer_host (elf : ELF64File) (host : Nat) (s : MState) :
    HostPins host (apply (elfRegisterAssignments elf host) s) := by
  have addr : lastValue registerWrites.entries100 .htif_tohost = none := by decide +kernel
  have base : lastValue registerWrites.entries100 .htif_tohost_base = none := by decide +kernel
  constructor
  · rw [apply_read, elfRegisterAssignments, lastValue_append, addr]; rfl
  · rw [apply_read, elfRegisterAssignments, lastValue_append, base]; rfl
end OCaml.Vm.Boot.Startup
