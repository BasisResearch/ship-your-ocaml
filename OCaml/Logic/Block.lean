import OCaml.Logic.CodeSlice

/-! Certificates emitted by `scripts/gen_bc_rules.py`. Instruction semantics
remain `stepI`; certificate fields check only decoding and window bounds. -/
namespace OCaml.Bytecode

/-- One decoded instruction inside a small code array. -/
structure CertifiedSite (code : Code) where
  offset : Nat
  instr : Instr
  len : Nat
  bound : offset + max len 2 ≤ code.size
  opcode : (code.word offset).bind Opcode.ofNat? = some instr.op
  length : instrLength code offset instr.op = some len
  decoded : decodeAt code offset = some instr

/-- A generated window, together with kernel-checked instruction entries. -/
structure CertifiedBlock where
  base : Nat
  code : Code
  sites : List (CertifiedSite code)

/-- Only certified instruction boundaries are executable. -/
def CertifiedBlock.decode (b : CertifiedBlock) (pc : Nat) : Option Instr :=
  (b.sites.find? fun site => b.base + site.offset == pc).map (·.instr)

/-- A caller supplies a code-window pin; no large code array is reduced by
this proof or by symbolic evaluation of the generated block. -/
theorem CertifiedBlock.decode_sound (b : CertifiedBlock) (P : Prog)
    (pin : P.code.extract b.base (b.base + b.code.size) = b.code)
    (pc : Nat) (i : Instr) (hd : b.decode pc = some i) :
    decodeAt P.code pc = some i := by
  unfold CertifiedBlock.decode at hd
  cases hf : b.sites.find? (fun site => b.base + site.offset == pc) with
  | none => simp [hf] at hd
  | some site =>
    have hp : b.base + site.offset = pc := by simpa using List.find?_some hf
    have hi : site.instr = i := by simpa [hf] using hd
    subst pc
    have he := decodeAt_extract P.code b.base (b.base + b.code.size)
      (b.base + site.offset) site.len site.instr.op (by omega)
      (by have := site.bound; omega)
      (by simpa [pin] using site.opcode)
      (by simpa [pin] using site.length)
    rw [he, pin]
    simpa [hi] using site.decoded

/-- A block transition is proved by symbolic reduction of its small decoder
on a template state. Calls and back edges stop at their successor state;
`sym_seq` and `loop_rule` compose the resulting transitions. -/
theorem CertifiedBlock.run (b : CertifiedBlock) (P : Prog)
    (pin : P.code.extract b.base (b.base + b.code.size) = b.code)
    (n : Nat) (s t : St)
    (h : Run.iter (decodedK P b.decode) n s = .ok t) :
    Run.iter (bcK P) n s = .ok t :=
  decoded_run_sound P b.decode (b.decode_sound P pin) n s t h

end OCaml.Bytecode
