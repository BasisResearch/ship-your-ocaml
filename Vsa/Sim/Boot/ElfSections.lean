import Vsa.Sim.Boot.ByteView
import Vsa.Sim.Boot.Parser
namespace Vsa.Sim.Boot
open SectionHeaderTableEntry

/-- Section-name table parsing keeps only its bounded byte slice. -/
theorem sectionNames_view {α : Type} [SectionHeaderTableEntry α] (sht : List α)
    (idx : Nat) (valid : idx < sht.length) (n : Nat) (byte : Nat → BitVec 8)
    (bound : sh_offset sht[idx] + sh_size sht[idx] ≤ n) :
    SectionHeaderTableEntry.getSectionNames idx sht (bytesOfView n byte) =
      .ok ⟨bytesOfView (sh_size sht[idx]) (fun i => byte (sh_offset sht[idx] + i))⟩ := by
  unfold SectionHeaderTableEntry.getSectionNames
  rw [dite_eq_right (by omega), ite_eq_right (by simp; omega)]
  rw [bytesOfView_extract n byte (sh_offset sht[idx]) (sh_size sht[idx]) bound]

def sectionView {α : Type} [SectionHeaderTableEntry α] (sh : α)
    (byte : Nat → BitVec 8) (name : Option String) : InterpretedSection := {
  section_name := sh_name sh
  section_type := sh_type sh
  section_flags := sh_flags sh
  section_addr := sh_addr sh
  section_offset := sh_offset sh
  section_size := sh_size sh
  section_link := sh_link sh
  section_info := sh_info sh
  section_align := sh_addralign sh
  section_entsize := sh_entsize sh
  section_body := if sh_type sh != ELFSectionHeaderTableEntry.Type.SHT_NOBITS
    then bytesOfView (sh_size sh) (fun i => byte (sh_offset sh + i)) else ByteArray.empty
  section_name_as_string := name }

theorem section_view {α : Type} [SectionHeaderTableEntry α] (sh : α)
    (n : Nat) (byte : Nat → BitVec 8) (name : Option String)
    (bound : sh_type sh ≠ ELFSectionHeaderTableEntry.Type.SHT_NOBITS → sh_offset sh + sh_size sh ≤ n) :
    SectionHeaderTableEntry.toSection? sh (bytesOfView n byte) name = .ok (sectionView sh byte name) := by
  unfold SectionHeaderTableEntry.toSection?
  rw [ite_eq_right (by simp only [bytesOfView_size, bne_iff_ne]; omega)]
  unfold sectionView
  by_cases empty : sh_type sh = ELFSectionHeaderTableEntry.Type.SHT_NOBITS
  · simp [empty]
  · simp only [bne_iff_ne]
    rw [bytesOfView_extract n byte (sh_offset sh) (sh_size sh) (bound empty)]

def sectionName {α : Type} [SectionHeaderTableEntry α] (names : ELFStringTable) (sh : α) : Option String :=
  if sh_name sh == 0 then none else some (names.stringAt (sh_name sh))

/-- Compose interpretation after the name-table parser has supplied its bounded view. -/
theorem sections_view {α β : Type} [SectionHeaderTableEntry α] [ELFHeader β]
    (sht : List α) (eh : β) (n : Nat) (byte : Nat → BitVec 8) (names : ELFStringTable)
    (nameTable : getSectionNames (ELFHeader.e_shstrndx eh) sht (bytesOfView n byte) = .ok names)
    (bound : ∀ sh ∈ sht, sh_type sh ≠ ELFSectionHeaderTableEntry.Type.SHT_NOBITS →
      sh_offset sh + sh_size sh ≤ n) :
    getInterpretedSections sht eh (bytesOfView n byte) =
      .ok (sht.map (fun sh => (sh, sectionView sh byte (sectionName names sh)))) := by
  simp only [getInterpretedSections, nameTable, Bind.bind, Except.bind]
  apply mapM_ok
  intro sh hs
  by_cases zero : sh_name sh = 0
  all_goals simp [sectionName, zero, section_view sh n byte _ (bound sh hs)] <;> rfl
end Vsa.Sim.Boot
