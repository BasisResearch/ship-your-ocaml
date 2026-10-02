import OCaml.Vm.Boot.Startup.RegisterRun

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Sim.RegisterWrites

/-- The header's three register writes followed by the source-derived write list. -/
noncomputable def elfRegisterAssignments (elf : ELF64File) (host : Nat) : List Assignment :=
  [⟨.PC, elf.file_header.e_entry.toBitVec⟩,
   ⟨.htif_tohost, BitVec.ofNat 64 host⟩,
   ⟨.htif_tohost_base, some (Functions.trunc (m := 64) (BitVec.ofNat 64 host))⟩] ++
    registerWrites.entries100

/-- The ELF-dependent prefix and all undefined-value assignments form one write program. -/
theorem initializeRegisters_program (elf : ELF64File) (host : Nat)
    (ht : tohostMetadata elf = some host) :
    initializeRegisters elf = program (elfRegisterAssignments elf host) := by
  rw [initializeRegisters_values]
  unfold registerValues
  change (elf.interpreted_sections.find? is_tohost).map (fun t => t.2.section_addr) = some host at ht
  rw [ht, registerWrites.program100]
  rfl

/-- Register setup succeeds for arbitrary input states and any supplied tohost address. -/
theorem initializeRegisters_run (elf : ELF64File) (host : Nat) (s : MState)
    (ht : tohostMetadata elf = some host) :
    (initializeRegisters elf).run s = .ok () (apply (elfRegisterAssignments elf host) s) := by
  rw [initializeRegisters_program elf host ht]
  exact Vsa.Sim.RegisterWrites.run _ _

/-- Register setup leaves the ELF-loaded memory unchanged. -/
theorem initializeRegisters_preserves_memory (elf : ELF64File) (host : Nat) (s t : MState)
    (ht : tohostMetadata elf = some host)
    (h : (initializeRegisters elf).run s = .ok () t) : t.mem = s.mem := by
  rw [initializeRegisters_run elf host s ht] at h
  have stateEq := (EStateM.Result.ok.inj h).2
  exact (congrArg (fun q : MState => q.mem) stateEq).symm.trans
    (Vsa.Sim.RegisterWrites.memory _ _)

end OCaml.Vm.Boot.Startup
