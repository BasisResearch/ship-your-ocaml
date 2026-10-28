import OCaml.Vm.Boot.Startup.SeekOptional

namespace OCaml.Vm.Boot.WhileMinElfParse
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.VsaHeap OCaml.Vm.Primitives Startup

/-- The original filename remains on the selected actual heap ledger at CODE entry. -/
theorem ResetCodeSeekEntry.filename_owned {initial after} (S : ResetCodeSeekEntry initial after) :
    (S.source.sections.fileNode.toNat,5) ∈ S.source.source.blocks :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S.source.source.sourceOwned _
    (S.source.sections.kept_owned _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))

/-- The reviewed source handoff supplies the native scan input without later-memory premises. -/
theorem ResetCodeSeekEntry.scan_input {initial after} (S : ResetCodeSeekEntry initial after) :
    CodeScanInput S.source.source.blocks backtraceCapacity S.source.sections.blk S.source.sections.fileNode after :=
  ⟨S.done.pc,S.done.regs,S.done.ready,S.observations,S.descriptors_owned,S.filename_owned,S.load_caller⟩

/-- Reset-to-completed-CODE-seek ancestry, including the selected source and actual local run. -/
structure ResetCodeSeekDone (initial after : Config) where
  atEntry : Config
  source : ResetCodeSeekEntry initial atEntry
  localRun : Steps atEntry after
  done : CodeSeekDone source.source.source.blocks backtraceCapacity source.source.sections.blk
    source.source.sections.fileNode atEntry after
  run : Steps (Vsa.Densify.fillZero initial) after

/-- Universal parsed/matching-ELF reset through the real reverse CODE scan to caml_main 0x80004eb0.
The actual return length is 764 and descriptor 3's current source-image position is 57. -/
theorem whileMin_reset_code_seek {imageElf : ELF64File}
    (image : WhileMinElf imageElf) (initial : Config) (reset : ElfReset imageElf initial) :
    ∃ after, Nonempty (ResetCodeSeekDone initial after) := by
  obtain ⟨entry,⟨S⟩⟩ := whileMin_reset_code_seek_entry image initial reset
  obtain ⟨after,run,D⟩ := code_seek_complete S.scan_input
  exact ⟨after,⟨⟨entry,S,run,D,S.run.trans run⟩⟩⟩

end OCaml.Vm.Boot.WhileMinElfParse
