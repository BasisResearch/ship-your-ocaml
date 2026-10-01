import OCaml.Vm.Boot.WhileMinImageData
import OCaml.Vm.Boot.WhileMinLogChecks
import OCaml.Vm.Platform

/-! Immutable runtime image in the captured ELF loader memory and after
application of the certified observed store log. No startup run is asserted. -/
namespace OCaml.Vm.Boot.WhileMinImage
open Vsa.Sim.Boot Vsa.Sim.Code Vsa.Machine WhileMinLog

private theorem text_in_pieces {off : Nat} (h : off < Image.textSize) :
    inPieces pieces (Image.textBase + off) = true := by
  simp [inPieces, pieces, Image.textBase, Image.textSize] at *
  omega

private theorem rodata_in_pieces {off : Nat} (h : off < Image.rodataSize) :
    inPieces pieces (Image.rodataBase + off) = true := by
  simp [inPieces, pieces, Image.rodataBase, Image.rodataSize] at *
  exact Or.inr (Or.inl (decide_eq_true (by omega)))

theorem initial_text : FixedBytesLoaded Image.textBase Image.textSize Image.textByte initialMem := by
  intro off bound
  rw [initialMem, loaderMem_get, text_in_pieces bound]
  simp only [ite_true]
  unfold imageByte
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem initial_rodata : FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte initialMem := by
  intro off bound
  rw [initialMem, loaderMem_get, rodata_in_pieces bound]
  simp only [ite_true]
  have separated : Image.textBase + Image.textSize ≤ Image.rodataBase := by decide +kernel
  unfold imageByte
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem observed_text : FixedBytesLoaded Image.textBase Image.textSize Image.textByte
    (observedMem initialMem log) := by
  intro off bound
  have top : Image.textBase + Image.textSize ≤ run0.base := by decide +kernel
  rw [observedMem, memory_below initialMem (by omega)]
  exact initial_text off bound

theorem observed_rodata : FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte
    (observedMem initialMem log) := by
  intro off bound
  have top : Image.rodataBase + Image.rodataSize ≤ run0.base := by decide +kernel
  rw [observedMem, memory_below initialMem (by omega)]
  exact initial_rodata off bound

/-- The image premise of the entry assembly follows from the actual loader
image and checked write-log memory, without an additional image assumption. -/
theorem executable {c : Config} (memory : c.σ.mem = observedMem initialMem log) :
    ExecutableImage c where
  text := by rw [memory]; exact observed_text
  rodata := by rw [memory]; exact observed_rodata

end OCaml.Vm.Boot.WhileMinImage
