import OCaml.Vm.Boot.WhileMinElfTables
import Vsa.Sim.Boot.ElfSegments
import Vsa.Sim.Boot.ElfSections
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Sim.Boot WhileMinElfData

def interpretedSegments : List (ELF64ProgramHeaderTableEntry × InterpretedSegment) :=
  programs.map (fun ph => (ph, segmentView ph fileByte))

def sectionNames : ELFStringTable :=
  ⟨bytesOfView section12.sh_size.toNat (fun i => fileByte (section12.sh_offset.toNat + i))⟩

def interpretedSections : List (ELF64SectionHeaderTableEntry × InterpretedSection) :=
  sections.map (fun sh => (sh, sectionView sh fileByte (sectionName sectionNames sh)))

theorem program_bounds : ∀ ph ∈ programs,
    ProgramHeaderTableEntry.p_offset ph + ProgramHeaderTableEntry.p_filesz ph ≤ fileSize := by decide +kernel

theorem section_bounds : ∀ sh ∈ sections,
    SectionHeaderTableEntry.sh_type sh ≠ ELFSectionHeaderTableEntry.Type.SHT_NOBITS →
      SectionHeaderTableEntry.sh_offset sh + SectionHeaderTableEntry.sh_size sh ≤ fileSize := by decide +kernel

theorem segments_parse : getInterpretedSegments programs fileBytes = .ok interpretedSegments :=
  segments_view programs fileSize fileByte program_bounds

theorem names_parse : SectionHeaderTableEntry.getSectionNames
    (ELFHeader.e_shstrndx expectedHeader) sections fileBytes = .ok sectionNames :=
  sectionNames_view sections 12 (by decide) fileSize fileByte (by decide)

theorem interpreted_sections_parse : SectionHeaderTableEntry.getInterpretedSections
    sections expectedHeader fileBytes = .ok interpretedSections :=
  sections_view sections expectedHeader fileSize fileByte sectionNames names_parse section_bounds

end OCaml.Vm.Boot.WhileMinElfParse
