import OCaml.Vm.Boot.Startup.SeekOptionalSteps
import OCaml.Vm.Boot.Startup.StrncmpShort

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Boot.WhileMinElfParse

/-- Bounded descriptor observations; the bytes are those produced by reset. -/
structure CodeScanTable (blk : BitVec 64) (c : Config) : Prop where
  lower : heapStart ≤ blk.toNat
  upper : blk.toNat + 56 ≤ heapEnd
  byte : ∀ k, k < 56 → (c.σ.mem[blk.toNat + k]?).getD 0 = sectionByte k

/-- Descriptor address in the reverse scan, starting at descriptor six. -/
def seekCursor (blk : BitVec 64) (k : Nat) : BitVec 64 := blk + BitVec.ofNat 64 (8 * (6 - k))
def seekOffset (k : Nat) : BitVec 64 := BitVec.ofNat 64 seekSectionOffsets[k]!
def seekLength (k : Nat) : BitVec 64 := BitVec.ofNat 64 seekSectionLengths[6 - k]!

/-- Reindex the existing unsigned/signed load certificates; no new source is read. -/
theorem seek_length_certificate (j : Nat) (bound : j < 7) :
    bytesVal .lwu [sectionByte (8*j+4),sectionByte (8*j+5),sectionByte (8*j+6),sectionByte (8*j+7)] =
      BitVec.ofNat 64 seekSectionLengths[j]! ∧
    bytesVal .lw [sectionByte (8*j+4),sectionByte (8*j+5),sectionByte (8*j+6),sectionByte (8*j+7)] =
      BitVec.ofNat 64 seekSectionLengths[j]! := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact seek_section_length_0
  · exact seek_section_length_1
  · exact seek_section_length_2
  · exact seek_section_length_3
  · exact seek_section_length_4
  · exact seek_section_length_5
  · exact seek_section_length_6

/-- Reindex the seven existing four-name-byte certificates. -/
theorem seek_name_certificate (j : Nat) (bound : j < 7) :
    [sectionByte (8*j),sectionByte (8*j+1),sectionByte (8*j+2),sectionByte (8*j+3)] =
      seekSectionNames[j]! := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact seek_section_name_0
  · exact seek_section_name_1
  · exact seek_section_name_2
  · exact seek_section_name_3
  · exact seek_section_name_4
  · exact seek_section_name_5
  · exact seek_section_name_6

theorem CodeScanTable.cursor_nat {blk c} (T : CodeScanTable blk c) (k : Nat) (hk : k ≤ 6) :
    (seekCursor blk k).toNat = blk.toNat + 8 * (6-k) := by
  have b := T.upper
  simp only [seekCursor,BitVec.toNat_add,BitVec.toNat_ofNat]
  unfold heapEnd at b
  omega

theorem CodeScanTable.window {blk c} (T : CodeScanTable blk c) (k off width : Nat)
    (hk : k ≤ 6) (hw : off + width ≤ 8) :
    ReadWindow (seekCursor blk k + BitVec.ofNat 64 off) width := by
  have lo := T.lower
  have hi := T.upper
  have addr : (seekCursor blk k + BitVec.ofNat 64 off).toNat = blk.toNat + 8*(6-k) + off := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,T.cursor_nat k hk]
    unfold heapEnd at hi
    omega
  constructor <;> rw [addr]
  · unfold heapStart at lo; omega
  · unfold heapEnd at hi; omega
  · right
    have bound : Layout.sym_tohost + 8 ≤ heapStart := by decide
    omega

theorem CodeScanTable.name {blk c} (T : CodeScanTable blk c) (k j : Nat) (hk : k ≤ 6) (hj : j < 4) :
    (c.σ.mem[(seekCursor blk k).toNat + j]?).getD 0 = seekSectionNames[6-k]![j]! := by
  rw [T.cursor_nat k hk,show blk.toNat + 8*(6-k) + j = blk.toNat + (8*(6-k)+j) by omega,
    T.byte _ (by omega)]
  have h := congrArg (fun xs : List (BitVec 8) => xs[j]!) (seek_name_certificate (6-k) (by omega))
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simpa only [List.getElem!_cons_zero,List.getElem!_cons_succ,Nat.add_zero] using h

theorem CodeScanTable.length {blk c} (T : CodeScanTable blk c) (k : Nat) (hk : k ≤ 6) :
    bytesVal .lwu (read4 c.σ.mem (seekCursor blk k + 4#64).toNat) = seekLength k ∧
    bytesVal .lw (read4 c.σ.mem (seekCursor blk k + 4#64).toNat) = seekLength k := by
  have hi := T.upper
  have addr : (seekCursor blk k + 4#64).toNat = blk.toNat + (8*(6-k)+4) := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,T.cursor_nat k hk]
    unfold heapEnd at hi
    omega
  simpa only [addr,read4,Nat.add_assoc,Nat.reduceAdd,
    T.byte (8*(6-k)+4) (by omega),T.byte (8*(6-k)+5) (by omega),
    T.byte (8*(6-k)+6) (by omega),T.byte (8*(6-k)+7) (by omega),seekLength] using
    seek_length_certificate (6-k) (by omega)

/-- Literal bytes are obtained from the current executable image's C-string witness. -/
theorem code_literal_byte {c} (literal : EnvName codeSectionName0 codeSectionChars0 c)
    (k : Nat) (hk : k < 4) :
    (c.σ.mem[codeSectionName0.toNat + k]?).getD 0 = seekSectionNames[0]![k]! := by
  obtain ⟨b,pin,_,value⟩ := cstr_byte_val _ _ _ literal.bytes k (by
    change k ≤ 4; omega)
  rw [pin,Option.getD_some]
  have eq : b = BitVec.ofNat 8 (byteVal codeSectionChars0 k) := by
    rw [← value,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rw [eq]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Native comparison result for each actual reverse descriptor. -/
def codeScanResult (k : Nat) : BitVec 64 :=
  if k = 6 then 0#64 else if k = 0 then strncmpDiff 82#8 79#8
  else strncmpDiff seekSectionNames[6-k]![0]! 67#8

/-- The six non-CODE comparisons are nonzero, including the CRCS second-byte result. -/
theorem codeScanResult_nonzero (k : Nat) (hk : k < 6) : codeScanResult k ≠ 0#64 := by
  have checked : ∀ i : Fin 6, codeScanResult i.val ≠ 0#64 := by decide
  exact checked ⟨k,hk⟩

/-- Compare exactly the four current descriptor name bytes against the real CODE literal. -/
theorem code_scan_name (c : Config) (blk ra : BitVec 64) (k : Nat) (hk : k ≤ 6)
    (leaf : LeafInput ra c) (T : CodeScanTable blk c)
    (literal : EnvName codeSectionName0 codeSectionChars0 c)
    (regs : GHolds c.σ (strncmpFirstInput (seekCursor blk k) codeSectionName0 4#64)) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [10,11,12,14,15,28] [] c ra (codeScanResult k)
        [(10,codeScanResult k),(1,ra)]) := by
  have left : ReadWindow (seekCursor blk k) 4 := by
    simpa only [show BitVec.ofNat 64 0 = 0#64 from rfl,BitVec.add_zero] using
      T.window k 0 4 hk (by decide)
  have right : ReadWindow codeSectionName0 4 := by constructor <;> decide
  by_cases last : k = 6
  · subst k
    have data : EqualPrefix (seekCursor blk 6) codeSectionName0 3
        (fun j => seekSectionNames[0]![j]!) c := {
      left := left
      right := right
      leftByte := fun j hj => T.name 6 j (by decide) (by omega)
      rightByte := fun j hj => code_literal_byte literal j (by omega)
      nonzero := fun j hj => by
        have checked : ∀ i : Fin 4, seekSectionNames[0]![i.val]! ≠ 0#8 := by decide
        exact checked ⟨j,by omega⟩ }
    exact strncmp_four_equal c _ _ ra _ leaf data regs
  · by_cases first : k = 0
    · subst k
      have data : SecondMismatch (seekCursor blk 0) codeSectionName0 67#8 82#8 79#8 c := {
        left := left
        right := right
        leftFirst := by simpa only [Nat.add_zero,Nat.reduceSub,seekSectionNames,List.getElem!_cons_zero,List.getElem!_cons_succ] using T.name 0 0 (by decide) (by decide)
        rightFirst := by simpa only [Nat.add_zero,Nat.reduceSub,seekSectionNames,List.getElem!_cons_zero,List.getElem!_cons_succ] using code_literal_byte literal 0 (by decide)
        leftSecond := T.name 0 1 (by decide) (by decide)
        rightSecond := code_literal_byte literal 1 (by decide)
        nonzero := by decide
        different := seek_crcs_common_prefix.2 }
      exact strncmp_four_second c _ _ ra _ _ _ leaf regs data
    · have ne : seekSectionNames[6-k]![0]! ≠ 67#8 := by
        have checked : ∀ i : Fin 5, seekSectionNames[5 - i.val]![0]! ≠ 67#8 := by decide
        have eq : 6-k = 5-(k-1) := by omega
        rw [eq]
        exact checked ⟨k-1,by omega⟩
      simpa only [codeScanResult,if_neg last,if_neg first] using
        strncmp_four_first c _ _ ra _ 67#8 leaf regs
          (by simpa only [nameCursor,show BitVec.ofNat 64 0 = 0#64 from rfl,BitVec.add_zero]
            using name_window left (k := 0) (by decide))
          (by constructor <;> decide)
          (by simpa only [Nat.add_zero,Nat.reduceSub,seekSectionNames,List.getElem!_cons_zero,List.getElem!_cons_succ] using T.name k 0 hk (by decide))
          (by simpa only [Nat.add_zero,Nat.reduceSub,seekSectionNames,List.getElem!_cons_zero,List.getElem!_cons_succ] using code_literal_byte literal 0 (by decide)) ne

end OCaml.Vm.Boot.Startup
