import OCaml.Vm.Boot.WhileMinElfData
import Vsa.Sim.Boot.ElfHeader
import OCaml.Vm.Layout
open Vsa.Sim.Boot OCaml.Vm.Boot.WhileMinElfData
namespace OCaml.Vm.Boot.WhileMinElfParse

def headerBytes := bytesOfView 64 fileByte
def header : ELF64Header := mkELF64Header headerBytes (by simp [headerBytes])

theorem source_header (h : 64 ≤ fileBytes.size) : mkELF64Header fileBytes h = header := by
  exact elfHeader_view fileSize fileByte (by decide)

theorem header_eq : header = expectedHeader := by
  unfold header expectedHeader mkELF64Header
  congr 1
  all_goals first | (apply nbytes_ext; decide +kernel) | decide +kernel
/-- The header parser succeeds on the exact pinned file, using only its bounded prefix. -/
theorem source_header_parse : mkELF64Header? fileBytes = .ok expectedHeader := by
  rw [show fileBytes = bytesOfView fileSize fileByte from rfl,
    elfHeader_parse_view fileSize fileByte (by decide)]
  change (Except.ok header : Except String ELF64Header) = _
  rw [header_eq]

theorem header_entry : header.e_entry.toBitVec = BitVec.ofNat 64 Layout.sym_start := by
  rw [header_eq]
  rfl
end OCaml.Vm.Boot.WhileMinElfParse
