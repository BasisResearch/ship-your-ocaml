import Vsa.Sim.Boot.ByteView
namespace Vsa.Sim.Boot
/-- A program-header entry depends only on its 56-byte slice. -/
theorem elfProgramHeader_slice (b : ByteArray) (offset : Nat) (endian : Bool)
    (bound : 56 ≤ b.size - offset) :
    mkELF64ProgramHeaderTableEntry endian b offset bound =
      mkELF64ProgramHeaderTableEntry endian (b.extract offset (offset + 56)) 0 (by simp; omega) := by
  simp only [mkELF64ProgramHeaderTableEntry,
    mkELF64ProgramHeaderTableEntry.getUInt32from, mkELF64ProgramHeaderTableEntry.getUInt64from]
  cases endian <;> elf_byte_reads

theorem elfProgramHeader_parse_slice (endian : Bool) (b : ByteArray) (offset : Nat)
    (bound : offset + 56 ≤ b.size) :
    mkELF64ProgramHeaderTableEntry? endian b offset =
      mkELF64ProgramHeaderTableEntry? endian (b.extract offset (offset + 56)) 0 := by
  unfold mkELF64ProgramHeaderTableEntry?
  rw [dif_pos (by omega), dif_pos (by simp; omega)]
  exact congrArg Except.ok (elfProgramHeader_slice b offset endian (by omega))

/-- Instantiate entry locality without evaluating a concrete backing array. -/
theorem elfProgramHeader_parse_view (n : Nat) (byte : Nat → BitVec 8) (offset : Nat)
    (endian : Bool) (bound : offset + 56 ≤ n) :
    mkELF64ProgramHeaderTableEntry? endian (bytesOfView n byte) offset =
      .ok (mkELF64ProgramHeaderTableEntry endian (bytesOfView 56 (fun i => byte (offset + i))) 0 (by simp)) := by
  rw [parser_view_of_slice (mkELF64ProgramHeaderTableEntry? endian) 56
    (elfProgramHeader_parse_slice endian) n byte offset bound]
  unfold mkELF64ProgramHeaderTableEntry?
  rw [dif_pos (by simp)]

/-- A section-header entry depends only on its 64-byte slice. -/
theorem elfSectionHeader_slice (b : ByteArray) (offset : Nat) (endian : Bool)
    (bound : 64 ≤ b.size - offset) :
    mkELF64SectionHeaderTableEntry endian b offset bound =
      mkELF64SectionHeaderTableEntry endian (b.extract offset (offset + 64)) 0 (by simp; omega) := by
  simp only [mkELF64SectionHeaderTableEntry,
    mkELF64SectionHeaderTableEntry.getUInt32from, mkELF64SectionHeaderTableEntry.getUInt64from]
  cases endian <;> elf_byte_reads

theorem elfSectionHeader_parse_slice (endian : Bool) (b : ByteArray) (offset : Nat)
    (bound : offset + 64 ≤ b.size) :
    mkELF64SectionHeaderTableEntry? endian b offset =
      mkELF64SectionHeaderTableEntry? endian (b.extract offset (offset + 64)) 0 := by
  unfold mkELF64SectionHeaderTableEntry?
  rw [dif_pos (by omega), dif_pos (by simp; omega)]
  exact congrArg Except.ok (elfSectionHeader_slice b offset endian (by omega))

/-- Instantiate entry locality without evaluating a concrete backing array. -/
theorem elfSectionHeader_parse_view (n : Nat) (byte : Nat → BitVec 8) (offset : Nat)
    (endian : Bool) (bound : offset + 64 ≤ n) :
    mkELF64SectionHeaderTableEntry? endian (bytesOfView n byte) offset =
      .ok (mkELF64SectionHeaderTableEntry endian (bytesOfView 64 (fun i => byte (offset + i))) 0 (by simp)) := by
  rw [parser_view_of_slice (mkELF64SectionHeaderTableEntry? endian) 64
    (elfSectionHeader_parse_slice endian) n byte offset bound]
  unfold mkELF64SectionHeaderTableEntry?
  rw [dif_pos (by simp)]

end Vsa.Sim.Boot
