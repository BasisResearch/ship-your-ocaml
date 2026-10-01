import Lean
import LeanRiscv

/-! Dump exactly the segment and gap bytes consumed by `initializeMemory`.
This IO utility supplies generated data; it makes no proof claim. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: boot_elf_pieces.lean ELF")
  match ← readElf path with
  | .error e => throw (IO.userError e)
  | .ok (.elf32 _) => throw (IO.userError "expected ELF64")
  | .ok (.elf64 elf) =>
    let pieces := elf.interpreted_segments.map (fun p => (p.2.segment_base, p.2.segment_body)) ++
      elf.bits_and_bobs
    let rows := pieces.map fun (base, bytes) =>
      Lean.Json.arr #[Lean.toJson base, Lean.toJson (bytes.data.map UInt8.toNat)]
    IO.println (Lean.Json.arr rows.toArray).compress
