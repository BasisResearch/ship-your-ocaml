import Vsa.Sim.Boot.LoaderPiece
namespace Vsa.Sim.Boot
open Vsa.MemRepr

abbrev LoaderPiece := Nat × ByteArray

def pieceShape (p : LoaderPiece) : Nat × Nat := (p.1, p.2.size)

def piecesOfElf (elf : ELF64File) : List LoaderPiece :=
  elf.interpreted_segments.map (fun p => (p.2.segment_base, p.2.segment_body)) ++ elf.bits_and_bobs

/-- Factor the frozen loader through its actual ordered list of byte-array pieces. -/
theorem initializeMemory_pieces (elf : ELF64File) : initializeMemory .B64 elf =
    (piecesOfElf elf).foldl (fun m p => loadPiece m p.1 p.2.data) ∅ := by
  simp only [initializeMemory, piecesOfElf, List.foldl_append, List.foldl_map]
  rfl

/-- Loader pieces are disjoint in address space and carry the specified image bytes. -/
structure LoaderPiecesOk (ps : List LoaderPiece) (byte : Nat → BitVec 8) : Prop where
  separate : ps.Pairwise (fun p q => p.1 + p.2.size ≤ q.1 ∨ q.1 + q.2.size ≤ p.1)
  bytes : ∀ p ∈ ps, ∀ i (hi : i < p.2.size), p.2.data[i].toBitVec = byte (p.1 + i)

/-- Preserve the abstract fold without constructing a concrete memory map. -/
theorem loadPieces_eq (ps : List LoaderPiece) (byte : Nat → BitVec 8)
    (ok : LoaderPiecesOk ps byte) (m : Mem)
    (fresh : ∀ p ∈ ps, ∀ i < p.2.size, m[p.1 + i]? = none) :
    ps.foldl (fun m p => loadPiece m p.1 p.2.data) m =
      ps.foldl (fun m p => insertRange m p.1 byte p.2.size) m := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    have tail : LoaderPiecesOk ps byte := {
      separate := (List.pairwise_cons.mp ok.separate).2
      bytes := fun q hq => ok.bytes q (by simp [hq]) }
    simp only [List.foldl_cons]
    rw [loadPiece_eq m p.1 byte p.2.data (fresh p (by simp)) (ok.bytes p (by simp))]
    apply ih tail
    intro q hq i hi
    rw [insertRange_get]
    have disjoint := (List.pairwise_cons.mp ok.separate).1 q hq
    have outside : ¬ (p.1 ≤ q.1 + i ∧ q.1 + i < p.1 + p.2.size) := by
      rcases disjoint with h | h <;> omega
    change (if p.1 ≤ q.1 + i ∧ q.1 + i < p.1 + p.2.size then some (byte (q.1 + i)) else m[q.1 + i]?) = none
    rw [if_neg outside]
    exact fresh q (by simp [hq]) i hi

/-- Kernel loader correspondence from finite piece geometry and byte-view certificates. -/
theorem initializeMemory_eq (elf : ELF64File) (byte : Nat → BitVec 8)
    (ok : LoaderPiecesOk (piecesOfElf elf) byte) :
    initializeMemory .B64 elf = loaderMem ((piecesOfElf elf).map pieceShape) byte := by
  rw [initializeMemory_pieces, loadPieces_eq _ byte ok _ (by intros; simp)]
  simp only [loaderMem, List.foldl_map, pieceShape]
end Vsa.Sim.Boot
