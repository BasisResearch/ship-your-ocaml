import OCaml.Bytecode.Opcode

/-!
# ZINC bytecode: code words, instruction decoding, executables

OCaml 4.14.4's bytecode is an array of 32-bit words (`code_t = opcode_t *`,
`opcode_t = int32_t`, `runtime/caml/mlvalues.h`). An instruction is an
opcode word followed by its operands; operands that are code offsets are
relative to the operand's own position (`pc += *pc` in `interp.c`).

Conventions used throughout (`OCaml/Bytecode/Semantics.lean`):

* `pc` is the index of an instruction's OPCODE word. In `interp.c` the C `pc`
  has already been advanced past the opcode when an arm runs, so C's `*pc` is
  our operand `pc + 1`, and a C `pc + *pc` read at operand `k` is our
  `pc + k + operand k`.
* Operands are read as signed 32-bit integers (`int32_t`).

`SWITCH` and `CLOSUREREC` are variable-length (their operand counts come from
their first operand, as in `caml_thread_code`, `runtime/fix_code.c`).
-/

namespace OCaml.Bytecode

/-- The code segment: 32-bit little-endian words (the CODE section, after
`caml_fixup_endianness`, which is the identity on RV64). -/
abbrev Code := Array (BitVec 32)

/-- The signed operand at word index `i`. -/
def Code.arg (c : Code) (i : Nat) : Option Int := (c[i]?).map BitVec.toInt

/-- The unsigned word at index `i`. -/
def Code.word (c : Code) (i : Nat) : Option Nat := (c[i]?).map BitVec.toNat

/-- A decoded instruction: the opcode and its operands, in code order. -/
structure Instr where
  op : Opcode
  args : List Int
  deriving DecidableEq, Repr

/-- Number of words the instruction at `pc` occupies. -/
def instrLength (c : Code) (pc : Nat) (op : Opcode) : Option Nat :=
  match op with
  | .SWITCH => do
      let s ← c.word (pc + 1)
      pure (2 + s % 65536 + s / 65536)
  | .CLOSUREREC => do
      let nf ← c.word (pc + 1)
      pure (3 + nf)
  | o => pure (1 + o.nargs)

/-- Decode the instruction at `pc` (`none`: out of range or not an opcode). -/
def decodeAt (c : Code) (pc : Nat) : Option Instr := do
  let w ← c.word pc
  let op ← Opcode.ofNat? w
  let len ← instrLength c pc op
  let args ← (List.range (len - 1)).mapM fun k => c.arg (pc + 1 + k)
  pure ⟨op, args⟩

/-! ## Bytecode executables

The file format read by `caml_main` (`runtime/startup_byt.c`): the sections
are laid out back to back, followed by a section table (`name[4]`, `len[4]`
big-endian, per section) and the trailer `num_sections[4]` + `EXEC_MAGIC`
(`"Caml1999X031"`, `runtime/caml/exec.h`). -/

/-- The 4.14 executable magic. -/
def execMagic : String := "Caml1999X031"

/-- A section descriptor. -/
structure Section where
  name : String
  len : Nat
  deriving DecidableEq, Repr

private def be32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat * 2^24 + (b.get! (i+1)).toNat * 2^16 +
  (b.get! (i+2)).toNat * 2^8 + (b.get! (i+3)).toNat

private def ascii (b : ByteArray) (i n : Nat) : String :=
  String.ofList ((List.range n).map fun k => Char.ofNat (b.get! (i + k)).toNat)

/-- `read_trailer` + `caml_read_section_descriptors`: the section table, with
each section's file offset. -/
def sections (f : ByteArray) : Option (List (Section × Nat)) := do
  let sz := f.size
  if sz < 16 then none
  if ascii f (sz - 12) 12 ≠ execMagic then none
  let n := be32 f (sz - 16)
  let tocStart := sz - 16 - 8 * n
  if sz < 16 + 8 * n then none
  let secs := (List.range n).map fun k =>
    (⟨ascii f (tocStart + 8 * k) 4, be32 f (tocStart + 8 * k + 4)⟩ : Section)
  -- sections are contiguous and end where the table starts
  let total := secs.foldl (fun a s => a + s.len) 0
  if tocStart < total then none
  let start := tocStart - total
  let (_, out) := secs.foldl (fun (off, acc) s => (off + s.len, acc ++ [(s, off)])) (start, [])
  pure out

/-- The bytes of the named section. -/
def sectionBytes (f : ByteArray) (name : String) : Option ByteArray := do
  let secs ← sections f
  let (s, off) ← secs.find? (·.1.name == name)
  pure (f.extract off (off + s.len))

/-- CODE as words (little-endian, as written by `Emitcode`). -/
def codeOfBytes (b : ByteArray) : Code :=
  (List.range (b.size / 4)).toArray.map fun k =>
    BitVec.ofNat 32 ((b.get! (4*k)).toNat + (b.get! (4*k+1)).toNat * 2^8 +
      (b.get! (4*k+2)).toNat * 2^16 + (b.get! (4*k+3)).toNat * 2^24)

/-- PRIM: NUL-terminated primitive names; index `i` is `C_CALLn i`'s operand
(`caml_build_primitive_table`). -/
def primsOfBytes (b : ByteArray) : Array String :=
  let names := (String.ofList (b.toList.map fun x => Char.ofNat x.toNat)).splitOn "\x00"
  (names.filter (· ≠ "")).toArray

end OCaml.Bytecode
