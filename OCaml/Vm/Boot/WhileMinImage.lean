import OCaml.Vm.Boot.WhileMinImageData
import OCaml.Vm.Boot.WhileMinLogChecks
import OCaml.Vm.Platform
import Vsa.Sim.Boot.Bytes

/-! Immutable runtime image in the captured ELF loader memory and after
application of the certified observed store log. No startup run is asserted. -/
namespace OCaml.Vm.Boot.WhileMinImage
open Vsa.Sim.Boot Vsa.Sim.Code Vsa.Machine WhileMinLog

/-- A bounded read of the capture, including untouched loader bytes. This
keeps certificate evaluation on functional views rather than the memory map. -/
theorem observed_bytes_view (a w : Nat) :
    Vsa.Sim.bytesT (observedMem initialMem log) a w =
      viewBytes (logView runs (fun x =>
        if inPieces pieces x then some (imageByte x) else none)) a w := by
  rw [observedMem_bytes logOk]
  apply viewBytes_congr
  intro i _
  unfold logView
  split
  · rfl
  · exact loaderMem_get pieces imageByte (a + i)

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

private theorem impure_pieces : ∀ i, i < 8 → inPieces pieces (Layout.sym_impure_ptr + i) = true := by decide

private theorem impure_in_pieces {i : Nat} (h : i < 8) :
    inPieces pieces (Layout.sym_impure_ptr + i) = true := impure_pieces i h

theorem initial_impure : ∀ i, i < 8 → (initialMem[Layout.sym_impure_ptr + i]?).isSome := by
  intro i h
  rw [initialMem, loaderMem_get, impure_in_pieces h]
  rfl

theorem observed_impure : ∀ i, i < 8 → ((observedMem initialMem log)[Layout.sym_impure_ptr + i]?).isSome := by
  intro i h
  rw [observedMem, memory_view]
  unfold logView
  split
  · rfl
  · exact initial_impure i h

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
  impure := by rw [memory]; exact observed_impure

end OCaml.Vm.Boot.WhileMinImage
