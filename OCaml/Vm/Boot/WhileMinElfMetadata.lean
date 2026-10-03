import OCaml.Vm.Boot.WhileMinElfFile
import OCaml.Vm.Boot.Startup.Reset
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Sim.Boot WhileMinElfData

theorem raw_file_parse : mkRawELFFile? fileBytes = .ok (.elf64 elf) :=
  rawElf64_view fileSize fileByte elf (by decide) (by rfl) file_parse

theorem entry_metadata : elf.file_header.e_entry.toBitVec = BitVec.ofNat 64 Layout.sym_start :=
  header_entry

theorem tohost_metadata : Startup.tohostMetadata elf = some Layout.sym_tohost := by
  decide +kernel

end OCaml.Vm.Boot.WhileMinElfParse
