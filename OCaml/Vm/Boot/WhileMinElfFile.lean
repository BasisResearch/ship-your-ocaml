import OCaml.Vm.Boot.WhileMinElfInterpret
import Vsa.Sim.Boot.ElfFile
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Sim.Boot WhileMinElfData

/-- Only header geometry and file length determine the parser's unclaimed bytes. -/
theorem gaps_geometry (b : ByteArray) (size : b.size = fileSize) :
    getBitsAndBobs expectedHeader sections programs b =
      gapRanges.map (fun p => (p.1, b.extract p.1 (p.1 + p.2))) := by
  unfold getBitsAndBobs
  have gaps : getBitsAndBobs.toGaps b
      (((getInhabitedRanges expectedHeader sections programs).toArray.qsort
        (fun r₁ r₂ => r₁.1 < r₂.1)).toList) =
      gapRanges.map (fun p => (p.1, p.1 + p.2)) := by
    rw [ranges_sorted]
    simp [inhabitedSorted, getBitsAndBobs.toGaps, size, fileSize, gapRanges]
  simp only [gaps, List.map_map]
  rfl


def gaps : List (Nat × ByteArray) :=
  gapRanges.map (fun p => (p.1, bytesOfView p.2 (fun i => fileByte (p.1 + i))))

theorem gaps_parse : getBitsAndBobs expectedHeader sections programs fileBytes = gaps := by
  rw [gaps_geometry fileBytes (bytesOfView_size _ _)]
  exact rangeViews fileSize fileByte gapRanges (by decide)

def elf : ELF64File := {
  file_header := expectedHeader
  interpreted_segments := interpretedSegments
  interpreted_sections := interpretedSections
  bits_and_bobs := gaps
}

/-- The source ELF parser accepts the exact archived while_min image. -/
theorem file_parse : mkELF64File? fileBytes = .ok elf :=
  elf64File_parse fileBytes expectedHeader programs sections interpretedSegments
    interpretedSections gaps source_header_parse program_table_parse section_table_parse
    segments_parse interpreted_sections_parse gaps_parse

end OCaml.Vm.Boot.WhileMinElfParse
