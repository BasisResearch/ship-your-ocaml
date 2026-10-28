import OCaml.Vm.Boot.Startup.SeekCodeCall
import OCaml.Vm.Boot.Startup.CodeSectionName
import OCaml.Vm.Boot.Startup.SeekSectionData

namespace OCaml.Vm.Boot.WhileMinElfParse
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.VsaHeap OCaml.Vm.Primitives Startup

/-- Reset reaches the actual optional-section entry. The scan is still pending. -/
structure ResetCodeSeekEntry (initial after : Config) where
  atDebugger : Config
  source : ResetInterpreterInit initial atDebugger
  localRun : Steps atDebugger after
  done : CodeSeekCallDone source.source.blocks backtraceCapacity atDebugger after
  run : Steps (Vsa.Densify.fillZero initial) after

/-- Current embedded source bytes at the executed optional-section entry. -/
theorem ResetCodeSeekEntry.embed {initial after} (S : ResetCodeSeekEntry initial after) : EmbedImage after :=
  S.source.embed.of_bytes fun _ _ => by rw [S.done.memory]

/-- Every byte of the selected 9,388-byte source file retains its loader value. -/
theorem ResetCodeSeekEntry.file_source {initial after} (S : ResetCodeSeekEntry initial after)
    (k : Nat) (hk : k < 9388) :
    (after.σ.mem[WhileMinImage.embedStart0 + k]?).getD 0 =
      (WhileMinImage.initialMem[WhileMinImage.embedStart0 + k]?).getD 0 :=
  S.embed.byte _ (by
    constructor <;> simp only [WhileMinImage.embedStart0, EmbedByte, heapEnd, embedLimit,
      Layout.sym_stack_top, Layout.sym_stack_size] <;> omega)

/-- The actual executable image supplies the CODE literal at the current entry. -/
theorem ResetCodeSeekEntry.code_literal {initial after} (S : ResetCodeSeekEntry initial after) :
    EnvName codeSectionName0 codeSectionChars0 after := codeSection_name_0 S.done.ready.image

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

/-- Current descriptor bytes are derived from the actual read and the selected live frame. -/
theorem ResetCodeSeekEntry.descriptor_bytes {initial after} (S : ResetCodeSeekEntry initial after)
    (k : Nat) (hk : k < 56) :
    (after.σ.mem[S.source.sections.blk.toNat + k]?).getD 0 = sectionByte k := by
  rw [S.done.memory, S.source.descriptors_from_sections.byte _ (List.mem_singleton_self _) _
    (by unfold InExt; dsimp only; omega)]
  exact S.source.sections.done.table k hk

/-- The real open-file/source records at the optional-section entry. -/
theorem ResetCodeSeekEntry.file {initial after} (S : ResetCodeSeekEntry initial after) :
    OpenFile after.σ.mem S.source.sections.fileNode := by
  rw [S.done.memory]
  exact S.source.file

/-- The current HTIF file record contains the selected source's length. -/
theorem ResetCodeSeekEntry.file_size {initial after} (S : ResetCodeSeekEntry initial after) :
    bytesT after.σ.mem (slotOne + 32) 8 = 9388#64 := S.file.slot.size

/-- Current fd position before the reverse scan; the scan must later derive its update to 57. -/
theorem ResetCodeSeekEntry.fd_position {initial after} (S : ResetCodeSeekEntry initial after) :
    bytesT after.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64 := by
  rw [S.done.memory]
  exact S.source.fd_position

/-- The selected current CODE descriptor's unsigned and signed lengths. -/
theorem ResetCodeSeekEntry.code_length {initial after} (S : ResetCodeSeekEntry initial after) :
    bytesVal .lwu (read4 after.σ.mem (S.source.sections.blk.toNat + 4)) = 764#64 ∧
    bytesVal .lw (read4 after.σ.mem (S.source.sections.blk.toNat + 4)) = 764#64 := by
  simpa only [read4, Nat.add_assoc, Nat.reduceAdd, S.descriptor_bytes 4 (by decide),
    S.descriptor_bytes 5 (by decide), S.descriptor_bytes 6 (by decide), S.descriptor_bytes 7 (by decide)]
    using seek_section_length_0

/-- Current-source observations for the actual optional-section call, before scanning. -/
structure CodeSeekSourceObserved (blk node : BitVec 64) (after : Config) : Prop where
  descriptor : ∀ k, k < 56 → (after.σ.mem[blk.toNat + k]?).getD 0 = sectionByte k
  count : read4 after.σ.mem trailSlot.toNat = sectionsWord
  table : bytesT after.σ.mem (trailSlot + 16#64).toNat 8 = blk
  file : OpenFile after.σ.mem node
  embed : EmbedImage after
  position : bytesT after.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64
  literal : EnvName codeSectionName0 codeSectionChars0 after

/-- Every observation is produced by the retained actual reset execution. -/
theorem ResetCodeSeekEntry.observations {initial after} (S : ResetCodeSeekEntry initial after) :
    CodeSeekSourceObserved S.source.sections.blk S.source.sections.fileNode after :=
  ⟨S.descriptor_bytes, S.num_sections, S.table_pointer, S.file, S.embed, S.fd_position, S.code_literal⟩

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

/-- Universal actual reset producer with concrete current-source observations.
No later-memory or additional native-run premise is required. -/
theorem whileMin_reset_code_seek_source {imageElf : ELF64File}
    (image : WhileMinElf imageElf) (initial : Config) (reset : ElfReset imageElf initial) :
    ∃ after, ∃ S : ResetCodeSeekEntry initial after,
      CodeSeekSourceObserved S.source.sections.blk S.source.sections.fileNode after := by
  obtain ⟨after, ⟨S⟩⟩ := whileMin_reset_code_seek_entry image initial reset
  exact ⟨after, S, S.observations⟩

end OCaml.Vm.Boot.WhileMinElfParse
