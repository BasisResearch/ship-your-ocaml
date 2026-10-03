import OCaml.Vm.Boot.WhileMinElfMetadata
import OCaml.Vm.Boot.WhileMinElfViews
import OCaml.Vm.Boot.Startup.ResetToCamlMain
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Sim.Boot WhileMinElfData Startup Vsa.Machine

/-- Keep the exact source-loader piece order, including the empty program header. -/
theorem pieces_view : piecesOfElf elf = loaderViews.map (fun v => v.piece fileByte) := by
  rfl

theorem pieces_ok : LoaderPiecesOk (piecesOfElf elf) WhileMinImage.imageByte := by
  rw [pieces_view]
  exact loaderViews_ok loaderViews fileByte WhileMinImage.imageByte loader_separate loader_bytes

/-- The actual source ELF loader builds the certified initial image. -/
theorem loaded_memory : initializeMemory .B64 elf = WhileMinImage.initialMem :=
  initializeMemory_views elf loaderViews fileByte WhileMinImage.imageByte WhileMinImage.pieces
    pieces_view loader_separate loader_bytes (by decide +kernel)

/-- Closed supplier of the reset image/metadata contract from the actual parsed ELF. -/
theorem whileMin_elf : WhileMinElf elf :=
  ⟨loaded_memory, entry_metadata, tohost_metadata⟩

/-- The actual parsed image has its own successful Sail reset configuration. -/
theorem reset_exists : ∃ c, ElfResetReady elf c := whileMin_reset_exists elf whileMin_elf

/-- Closed reset-to-C-entry witness. Startup after caml_main remains to be composed. -/
structure ResetCamlMainWitness (initial after : Config) : Prop where
  reset : ElfResetReady elf initial
  post : ResetCamlMainPost initial after

theorem reset_caml_main_exists : ∃ initial after, ResetCamlMainWitness initial after := by
  obtain ⟨initial, reset⟩ := reset_exists
  obtain ⟨after, post⟩ := reset_to_caml_main whileMin_elf reset.toElfReset
  exact ⟨initial, after, ⟨reset, post⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
