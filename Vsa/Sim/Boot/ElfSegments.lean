import Vsa.Sim.Boot.ByteView
import Vsa.Sim.Boot.Parser
namespace Vsa.Sim.Boot
open ProgramHeaderTableEntry
/-- The source segment record with its body represented by a bounded byte view. -/
def segmentView {α : Type} [ProgramHeaderTableEntry α] (ph : α) (byte : Nat → BitVec 8) : InterpretedSegment := {
  segment_type := p_type ph
  segment_size := p_filesz ph
  segment_memsz := p_memsz ph
  segment_base := p_vaddr ph
  segment_paddr := p_paddr ph
  segment_align := p_align ph
  segment_offset := p_offset ph
  segment_body := bytesOfView (p_filesz ph) (fun i => byte (p_offset ph + i))
  segment_flags := ⟨p_flags ph / 4 % 2 == 0, p_flags ph / 2 % 2 == 0, p_flags ph / 1 % 2 == 0⟩ }

/-- Interpretation validates bounds, then retains a slice without evaluating its bytes. -/
theorem segment_view {α : Type} [ProgramHeaderTableEntry α] (ph : α)
    (n : Nat) (byte : Nat → BitVec 8) (bound : p_offset ph + p_filesz ph ≤ n) :
    ProgramHeaderTableEntry.toSegment? ph (bytesOfView n byte) = .ok (segmentView ph byte) := by
  unfold ProgramHeaderTableEntry.toSegment?
  rw [if_neg (by simp; omega)]
  rw [bytesOfView_extract n byte (p_offset ph) (p_filesz ph) bound]
  rfl

theorem segments_view {α : Type} [ProgramHeaderTableEntry α] (ps : List α)
    (n : Nat) (byte : Nat → BitVec 8) (bound : ∀ ph ∈ ps, p_offset ph + p_filesz ph ≤ n) :
    getInterpretedSegments ps (bytesOfView n byte) = .ok (ps.map (fun ph => (ph, segmentView ph byte))) := by
  unfold getInterpretedSegments
  apply mapM_ok
  intro ph hp
  rw [segment_view ph n byte (bound ph hp)]
  rfl
end Vsa.Sim.Boot
