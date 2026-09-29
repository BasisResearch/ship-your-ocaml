import OCaml.Bytecode.Semantics

/-!
# Fragments: what Layer A covers, and the ledger of the rest

`BcSem` (`OCaml/Bytecode/Semantics.lean`) is grown fragment by fragment,
never with `sorry`: an instruction or primitive outside the current
fragment steps to `.unsupported`, and the Layer A statement assumes the
program never reaches one (`Good`). This file names the fragments, assigns
every opcode to one, and ledgers every opcode outside F1 with the reason it
is not in F1 yet. Primitives are ledgered by name in `primLedger` (the ones
`boot/ocamlc` links, `OCaml/Programs/OcamlcPrims.lean`, generated).

Fragment order (README.md, PHASES.md):

* **F1** core ZINC: stack/env/accu, integers, branches, `SWITCH`, globals,
  blocks, closures, application, exceptions caught in the program, `STOP`,
  and the F1 primitives (console channels, `%d`, named values, `Sys`
  constants, `exit`). Runs `tests/while.ml` and `f2_closures.ml` unchanged
  (VALIDATION.md §BcSem).
* **F2** data: float blocks, arrays, bytes/strings, `C_CALLN`, and the
  primitive families behind them (`caml_create_bytes`, `caml_blit_*`,
  `caml_make_vect`, polymorphic compare and hash, `caml_format_float`, …).
* **F3** objects: `GETMETHOD`, `GETPUBMET` (which WRITES its inline method
  cache into the code: the code segment is not immutable), `GETDYNMET`.
* **F4** callbacks: re-entrant `caml_interprete` (`caml_callback*`): the
  uncaught-exception path (`at_exit` then `Fatal error: exception …`),
  finalisers, signal handlers.
* **F5** files and the OS: `caml_sys_open`, reading and writing files in the
  in-memory file system (what `ocamlc` needs to read sources and `.cmi`s
  and write `.cmo`s), `Sys.getenv`, time.
* **Dbg** debugger instructions `EVENT`/`BREAK` (never emitted without
  `-g` + the debugger; stays out).
-/

namespace OCaml.Bytecode

set_option maxRecDepth 8192

inductive Fragment where
  | F1 | F2 | F3 | F4 | F5 | Dbg
  deriving DecidableEq, Repr

/-- The fragment that brings each opcode in. -/
def Opcode.fragment : Opcode → Fragment
  | .MAKEFLOATBLOCK | .GETFLOATFIELD | .SETFLOATFIELD | .VECTLENGTH | .GETVECTITEM
  | .SETVECTITEM | .GETBYTESCHAR | .SETBYTESCHAR | .GETSTRINGCHAR | .C_CALLN => .F2
  | .GETMETHOD | .GETPUBMET | .GETDYNMET => .F3
  | .EVENT | .BREAK => .Dbg
  | _ => .F1

/-- **The ledger of opcodes outside F1**, with their fragment and what they
need. -/
def ledger : List (Opcode × Fragment × String) :=
  [ (.MAKEFLOATBLOCK, .F2, "unboxed float records (Double_array_tag)"),
    (.GETFLOATFIELD, .F2, "float record read (boxes: allocation)"),
    (.SETFLOATFIELD, .F2, "float record write"),
    (.VECTLENGTH, .F2, "array length (float arrays: Double_array_tag)"),
    (.GETVECTITEM, .F2, "array read"),
    (.SETVECTITEM, .F2, "array write (caml_modify)"),
    (.GETBYTESCHAR, .F2, "bytes read"),
    (.SETBYTESCHAR, .F2, "bytes write"),
    (.GETSTRINGCHAR, .F2, "string read"),
    (.C_CALLN, .F2, "primitives with more than 5 arguments"),
    (.GETMETHOD, .F3, "method lookup (Lookup in the method table)"),
    (.GETPUBMET, .F3, "public method lookup; writes the inline cache into the CODE"),
    (.GETDYNMET, .F3, "dynamic method lookup (binary search)"),
    (.EVENT, .Dbg, "debugger event (only under ocamldebug)"),
    (.BREAK, .Dbg, "debugger breakpoint (only under ocamldebug)") ]

/-- The ledger lists exactly the non-F1 opcodes. -/
theorem ledger_exact :
    ∀ o ∈ Opcode.all, (o.fragment ≠ .F1 ↔ o ∈ ledger.map (·.1)) := by decide

/-- Every ledger entry's fragment is its opcode's fragment. -/
theorem ledger_fragment : ∀ e ∈ ledger, e.1.fragment = e.2.1 := by decide

theorem ledger_length : ledger.length = 15 := rfl

/-- The F1 opcode count: 149 opcodes, 15 ledgered. -/
theorem f1_count : (Opcode.all.filter (·.fragment = .F1)).length = 134 := by decide

/-- A primitive outside `primsF1` is `.unsupported` on every argument list
(so `primsF1` is exactly the F1 primitive set). -/
theorem primF1_unsupported (name : String) (h : name ∉ primsF1) (args : List Val)
    (hp : Heap) (w : World) : primF1 name args hp w = .unsupported := by
  simp [primF1, h]

end OCaml.Bytecode
