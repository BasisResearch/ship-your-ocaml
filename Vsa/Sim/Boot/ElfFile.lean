import Vsa.Sim.Boot.ByteView
namespace Vsa.Sim.Boot
/-- Compose the actual parser before specializing to any concrete byte view. -/
theorem elf64File_parse (bytes : ByteArray) (header : ELF64Header)
    (programs : List ELF64ProgramHeaderTableEntry) (sections : List ELF64SectionHeaderTableEntry)
    (segments : List (ELF64ProgramHeaderTableEntry × InterpretedSegment))
    (interpreted : List (ELF64SectionHeaderTableEntry × InterpretedSection))
    (gaps : List (Nat × ByteArray))
    (hheader : mkELF64Header? bytes = .ok header)
    (hprograms : header.mkELF64ProgramHeaderTable? bytes = .ok programs)
    (hsections : header.mkELF64SectionHeaderTable? bytes = .ok sections)
    (hsegments : getInterpretedSegments programs bytes = .ok segments)
    (hinterpreted : SectionHeaderTableEntry.getInterpretedSections sections header bytes = .ok interpreted)
    (hgaps : getBitsAndBobs header sections programs bytes = gaps) :
    mkELF64File? bytes = .ok ⟨header, segments, interpreted, gaps⟩ := by
  simp only [mkELF64File?, hheader, Bind.bind, Except.bind,
    hprograms, hsections, hsegments, hinterpreted, hgaps]
/-- The raw dispatcher needs only the class byte, then reuses the 64-bit parser. -/
theorem rawElf64_parse (bytes : ByteArray) (elf : ELF64File)
    (size : 5 ≤ bytes.size) (kind : bytes[4]'(by omega) = 2)
    (parsed : mkELF64File? bytes = .ok elf) :
    mkRawELFFile? bytes = .ok (.elf64 elf) := by
  have enough : ¬ bytes.size < 5 := by omega
  simp only [mkRawELFFile?, enough, kind, parsed]
  rfl
/-- Dispatch a bounded view without elaborating an index into a concrete full array. -/
theorem rawElf64_view (n : Nat) (byte : Nat → BitVec 8) (elf : ELF64File)
    (size : 5 ≤ n) (kind : byte 4 = 2#8)
    (parsed : mkELF64File? (bytesOfView n byte) = .ok elf) :
    mkRawELFFile? (bytesOfView n byte) = .ok (.elf64 elf) := by
  apply rawElf64_parse _ elf (by simpa using size) _ parsed
  rw [bytesOfView_get n byte 4 (by omega), kind]
  rfl
/-- Extract a finite list of file ranges as bounded views. -/
theorem rangeViews (n : Nat) (byte : Nat → BitVec 8) (ranges : List (Nat × Nat))
    (bounds : ∀ p ∈ ranges, p.1 + p.2 ≤ n) :
    ranges.map (fun p => (p.1, (bytesOfView n byte).extract p.1 (p.1 + p.2))) =
      ranges.map (fun p => (p.1, bytesOfView p.2 (fun i => byte (p.1 + i)))) := by
  apply List.map_congr_left
  intro p hp
  rw [bytesOfView_extract n byte p.1 p.2 (bounds p hp)]
end Vsa.Sim.Boot
