import Vsa.Elf
/-! Decode-AST dump for instruction words, over THIS repository's ELF
(`experiments/syi/M2_decode_ast_dump.lean` did the same over the embedded
WHILE ELF). The machine is set up exactly as `Vsa.setupElf`; decoding
depends only on the CSRs that setup fixes (`misa`, privilege, `mseccfg`),
which the generated lemmas take as hypotheses.
  lake env lean --run experiments/DecodeDump.lean ELF WORDS > dump.txt
Output lines: `<word>;OK;<ast>` (the format `gen_decode_table.py` reads). -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

def parseHex (s : String) : Nat :=
  s.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0

def main (args : List String) : IO Unit := do
  let [elfPath, wordsPath] := args | IO.println "usage: ELF WORDS"
  let lines ← IO.FS.lines wordsPath
  match (← readElf elfPath) with
  | .error e => IO.println s!"ELF-ERR {e}"
  | .ok (.elf32 _) => IO.println "ELF-ERR 32-bit"
  | .ok (.elf64 elf) =>
    let mem := initializeMemory MachineBits.B64 elf
    let σ0 : SequentialState RegisterType trivialChoiceSource :=
      ⟨Std.ExtDHashMap.emptyWithCapacity, (), mem, default, default, default⟩
    match (Vsa.setupElf elf).run σ0 with
    | .error e _ => IO.println s!"SETUP-ERR {e.print}"
    | .ok _ σ' =>
      for l in lines do
        let t := l.trimAscii.toString
        if t.isEmpty then continue
        let w : BitVec 32 := BitVec.ofNat 32 (parseHex t)
        match (ext_decode w).run σ' with
        | .ok ast _ => IO.println s!"{t};OK;{(toString (repr ast)).replace "\n" " "}"
        | .error e _ => IO.println s!"{t};ERR;{e.print}"
