import Vsa.Sim.Boot.LoaderPieces
import Vsa.Sim.Boot.ByteView
namespace Vsa.Sim.Boot
/-- One file-backed loader range. Zero-length program headers are retained. -/
structure LoaderView where
  base : Nat
  size : Nat
  offset : Nat
  deriving DecidableEq

def LoaderView.piece (v : LoaderView) (byte : Nat → BitVec 8) : LoaderPiece :=
  (v.base, bytesOfView v.size (fun i => byte (v.offset + i)))

def LoaderView.shape (v : LoaderView) : Nat × Nat := (v.base, v.size)

/-- Geometry and byte aliases suffice for the real byte-array loader contract. -/
theorem loaderViews_ok (vs : List LoaderView) (file image : Nat → BitVec 8)
    (separate : vs.Pairwise (fun v w => v.base + v.size ≤ w.base ∨ w.base + w.size ≤ v.base))
    (bytes : ∀ v ∈ vs, ∀ i < v.size, file (v.offset + i) = image (v.base + i)) :
    LoaderPiecesOk (vs.map (fun v => v.piece file)) image := by
  constructor
  · simpa only [List.pairwise_map, LoaderView.piece, bytesOfView_size] using separate
  · intro p hp i hi
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    have bound : i < v.size := by simpa only [LoaderView.piece, bytesOfView_size] using hi
    change ((bytesOfView v.size (fun j => file (v.offset + j)))[i]).toBitVec = image (v.base + i)
    rw [bytesOfView_get v.size _ i bound]
    exact bytes v hv i bound

theorem loaderViews_shape (vs : List LoaderView) (file : Nat → BitVec 8) :
    (vs.map (fun v => v.piece file)).map pieceShape = vs.map LoaderView.shape := by
  simp only [List.map_map, pieceShape, LoaderView.piece, bytesOfView_size, Function.comp_def]
  rfl

/-- Empty program headers do not add bytes to memory. -/
theorem insertRange_zero (m : Vsa.MemRepr.Mem) (base : Nat) (byte : Nat → BitVec 8) :
    insertRange m base byte 0 = m := rfl
/-- Filtering empty ranges preserves a loader fold for every initial memory. -/
theorem foldRanges_nonempty (ps : List (Nat × Nat)) (byte : Nat → BitVec 8)
    (m : Vsa.MemRepr.Mem) :
    (ps.filter (fun p => p.2 != 0)).foldl (fun m p => insertRange m p.1 byte p.2) m =
      ps.foldl (fun m p => insertRange m p.1 byte p.2) m := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    by_cases empty : p.2 = 0
    · simpa only [List.filter_cons, empty, bne_self_eq_false, Bool.false_eq_true,
        ite_false, List.foldl_cons, insertRange_zero] using ih m
    · simp only [List.filter_cons, bne_iff_ne]
      rw [if_pos empty, List.foldl_cons]
      exact ih _

/-- Source loader correspondence through bounded views, normalized before instantiation. -/
theorem initializeMemory_views (elf : ELF64File) (vs : List LoaderView)
    (file image : Nat → BitVec 8) (shapes : List (Nat × Nat))
    (pieces : piecesOfElf elf = vs.map (fun v => v.piece file))
    (separate : vs.Pairwise (fun v w => v.base + v.size ≤ w.base ∨ w.base + w.size ≤ v.base))
    (bytes : ∀ v ∈ vs, ∀ i < v.size, file (v.offset + i) = image (v.base + i))
    (shape_match : (vs.map LoaderView.shape).filter (fun p => p.2 != 0) = shapes) :
    initializeMemory .B64 elf = loaderMem shapes image := by
  have ok : LoaderPiecesOk (piecesOfElf elf) image := by
    rw [pieces]
    exact loaderViews_ok vs file image separate bytes
  rw [initializeMemory_eq elf image ok, pieces, loaderViews_shape]
  rw [← shape_match]
  exact (foldRanges_nonempty _ image _).symm
end Vsa.Sim.Boot
