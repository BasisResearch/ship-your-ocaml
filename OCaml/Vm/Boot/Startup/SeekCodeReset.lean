import OCaml.Vm.Boot.Startup.SeekCodeCall

namespace OCaml.Vm.Boot.WhileMinElfParse
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives Startup

/-- Reset reaches the actual optional-section entry. The scan is still pending. -/
structure ResetCodeSeekEntry (initial after : Config) where
  atDebugger : Config
  source : ResetInterpreterInit initial atDebugger
  localRun : Steps atDebugger after
  done : CodeSeekCallDone source.source.blocks backtraceCapacity atDebugger after
  run : Steps (Vsa.Densify.fillZero initial) after

/-- The count observed at the real optional-section entry. -/
theorem ResetCodeSeekEntry.num_sections {initial after} (S : ResetCodeSeekEntry initial after) :
    read4 after.σ.mem trailSlot.toNat = sectionsWord := by
  rw [S.done.memory]
  exact S.source.num_sections

/-- The descriptor pointer observed at the real optional-section entry. -/
theorem ResetCodeSeekEntry.table_pointer {initial after} (S : ResetCodeSeekEntry initial after) :
    bytesT after.σ.mem (trailSlot + 16#64).toNat 8 = S.source.sections.blk := by
  rw [S.done.memory]
  exact S.source.table_pointer

/-- The current heap retains the selected descriptor allocation. -/
theorem ResetCodeSeekEntry.descriptors_owned {initial after} (S : ResetCodeSeekEntry initial after) :
    (S.source.sections.blk.toNat,56) ∈ S.source.source.blocks := S.source.descriptors_owned

/-- The real fd/argv bank survives the CODE argument setup and direct call. -/
theorem ResetCodeSeekEntry.load_caller {initial after} (S : ResetCodeSeekEntry initial after) :
    LoadCaller after := S.source.load_caller.frame S.done.abi (by decide) (by decide)

theorem reset_code_seek_entry (initial : Config) (reset : ElfReset elf initial) :
    ∃ after, Nonempty (ResetCodeSeekEntry initial after) := by
  obtain ⟨before,⟨I⟩⟩ := reset_interpreter_init initial reset
  obtain ⟨after,run,D⟩ := code_seek_call before I.source.blocks backtraceCapacity
    ⟨I.done.pc,I.done.ready,I.load_caller⟩
  exact ⟨after,⟨⟨before,I,run,D,I.run.trans run⟩⟩⟩

theorem whileMin_reset_code_seek_entry {imageElf : ELF64File}
    (image : WhileMinElf imageElf) (initial : Config) (reset : ElfReset imageElf initial) :
    ∃ after, Nonempty (ResetCodeSeekEntry initial after) :=
  reset_code_seek_entry initial (reset.of_whileMinElf image whileMin_elf)

end OCaml.Vm.Boot.WhileMinElfParse
