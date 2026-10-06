import OCaml.Bytecode.Semantics
import OCaml.Programs.OcamlcExecuted

/-!
# Fragments: what Layer A covers, and the ledger of the rest

`BcSem` (`OCaml/Bytecode/Semantics.lean`) is grown fragment by fragment,
never with `sorry`: an instruction or primitive outside the current
fragment steps to `.unsupported`, and the Layer A statement assumes the
program never reaches one (`Good`). This file names the fragments, assigns
every opcode to one, and ledgers every opcode outside F1 with the reason it
belongs to a later fragment. Implemented primitives are listed in `primsF1` and `primsF2`; coverage of
the compiler's executed primitive set remains an explicit lane obligation.

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

/-- Executable F2 opcode coverage. This records transcription status; it
is not a claim that machine-arm simulation has been proved. -/
def implementedF2 : List Opcode :=
  [.MAKEFLOATBLOCK, .GETFLOATFIELD, .SETFLOATFIELD, .VECTLENGTH,
   .GETVECTITEM, .SETVECTITEM, .GETBYTESCHAR, .SETBYTESCHAR, .GETSTRINGCHAR, .C_CALLN]

/-- **Major-heap allocations outside F1.** These F1 opcodes stay in F1 only
when their block fits the minor heap (`OCaml.Instr.minorAlloc`, part of
`OCaml.InF1`); larger blocks take interp.c's `caml_alloc_shr` path (the major
heap, the GC lane's G2/F2+). The compiler executes MAKEBLOCK with wosize 852. -/
def majorAllocLedger : List (Opcode × String) :=
  [ (.MAKEBLOCK, "wosize > Max_young_wosize: caml_alloc_shr (major heap)"),
    (.CLOSURE, "2 + nvars > Max_young_wosize: caml_alloc_shr (major heap)"),
    (.CLOSUREREC, "3 nfuncs - 1 + nvars > Max_young_wosize: caml_alloc_shr (major heap)") ]

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


/-- An entry records executable-domain coverage or an explicit open boundary.
Implemented domains may reject malformed/unsupported arguments; this is not
an arm-simulation theorem. The compiler differential is separate evidence. -/
inductive PrimitiveCoverage where
  | domain | openBoundary (reason : String)
  deriving DecidableEq, Repr

/-- Primitive names with executable cases, including partial domains such as
address-independent hashing and ordinary-block comparison. GC statistics
consume explicit GcSnapshot observations; machine correspondence is
GcObservationInput, not supplied by differential validation. -/
def primitiveDomains : List String := [
  "caml_callback", "caml_callback2", "caml_callback3", "caml_convert_raw_backtrace", "caml_ml_debug_info_status",
  "caml_alloc_dummy",
  "caml_update_dummy",
  "caml_ensure_stack_capacity",
  "caml_gc_quick_stat",
  "caml_input_value",
  "caml_output_value",
  "caml_md5_chan",
  "caml_md5_string",
  "caml_new_lex_engine",
  "caml_sys_random_seed",
  "caml_sys_read_directory",

  "caml_abs_float",
  "caml_add_float",
  "caml_array_append",
  "caml_array_blit",
  "caml_array_fill",
  "caml_array_get",
  "caml_array_get_addr",
  "caml_array_set",
  "caml_array_set_addr",
  "caml_array_sub",
  "caml_array_unsafe_get",
  "caml_array_unsafe_set",
  "caml_atan_float",
  "caml_backtrace_status",
  "caml_blit_bytes",
  "caml_blit_string",
  "caml_bytes_compare",
  "caml_bytes_get",
  "caml_bytes_of_string",
  "caml_bytes_set",
  "caml_compare",
  "caml_create_bytes",
  "caml_div_float",
  "caml_equal",
  "caml_fill_bytes",
  "caml_float_of_int",
  "caml_format_float",
  "caml_format_int",
  "caml_fresh_oo_id",
  "caml_get_exception_raw_backtrace",
  "caml_greaterequal",
  "caml_greaterthan",
  "caml_hash",
  "caml_int32_add",
  "caml_int32_and",
  "caml_int32_compare",
  "caml_int32_mul",
  "caml_int32_neg",
  "caml_int32_of_int",
  "caml_int32_or",
  "caml_int32_shift_left",
  "caml_int32_shift_right",
  "caml_int32_shift_right_unsigned",
  "caml_int32_sub",
  "caml_int32_to_int",
  "caml_int32_xor",
  "caml_int64_add",
  "caml_int64_and",
  "caml_int64_compare",
  "caml_int64_float_of_bits",
  "caml_int64_mul",
  "caml_int64_neg",
  "caml_int64_of_int",
  "caml_int64_or",
  "caml_int64_shift_left",
  "caml_int64_shift_right",
  "caml_int64_shift_right_unsigned",
  "caml_int64_sub",
  "caml_int64_to_int",
  "caml_int64_xor",
  "caml_int_compare",
  "caml_int_of_float",
  "caml_int_of_string",
  "caml_lessequal",
  "caml_lessthan",
  "caml_make_vect",
  "caml_ml_bytes_length",
  "caml_ml_close_channel",
  "caml_ml_flush",
  "caml_ml_input",
  "caml_ml_input_char",
  "caml_ml_open_descriptor_in",
  "caml_ml_open_descriptor_out",
  "caml_ml_out_channels_list",
  "caml_ml_output",
  "caml_ml_output_bytes",
  "caml_ml_output_char",
  "caml_ml_output_int",
  "caml_ml_pos_in",
  "caml_ml_pos_out",
  "caml_ml_seek_in",
  "caml_ml_seek_out",
  "caml_ml_set_binary_mode",
  "caml_ml_set_channel_name",
  "caml_ml_string_length",
  "caml_mul_float",
  "caml_nativeint_add",
  "caml_nativeint_and",
  "caml_nativeint_compare",
  "caml_nativeint_mul",
  "caml_nativeint_neg",
  "caml_nativeint_of_int",
  "caml_nativeint_or",
  "caml_nativeint_shift_left",
  "caml_nativeint_shift_right",
  "caml_nativeint_shift_right_unsigned",
  "caml_nativeint_sub",
  "caml_nativeint_to_int",
  "caml_nativeint_xor",
  "caml_neg_float",
  "caml_notequal",
  "caml_obj_block",
  "caml_obj_dup",
  "caml_obj_make_forward",
  "caml_obj_set_tag",
  "caml_obj_tag",
  "caml_register_named_value",
  "caml_restore_raw_backtrace",
  "caml_set_oo_id",
  "caml_sqrt_float",
  "caml_string_compare",
  "caml_string_equal",
  "caml_string_get",
  "caml_string_notequal",
  "caml_string_of_bytes",
  "caml_sub_float",
  "caml_sys_argv",
  "caml_sys_close",
  "caml_sys_const_backend_type",
  "caml_sys_const_big_endian",
  "caml_sys_const_int_size",
  "caml_sys_const_max_wosize",
  "caml_sys_const_naked_pointers_checked",
  "caml_sys_const_ostype_cygwin",
  "caml_sys_const_ostype_unix",
  "caml_sys_const_ostype_win32",
  "caml_sys_const_word_size",
  "caml_sys_executable_name",
  "caml_sys_exit",
  "caml_sys_file_exists",
  "caml_sys_get_argv",
  "caml_sys_get_config",
  "caml_sys_getenv",
  "caml_sys_open",
  "caml_sys_remove",
  "caml_sys_rename",
  "caml_sys_time",
  "caml_sys_time_include_children"]

/-- Remaining measured compiler primitive boundaries and their owners. -/
def primitiveOpen : List (String × String) := []

def primitiveLedger : List (String × PrimitiveCoverage) :=
  primitiveDomains.map (fun n => (n, .domain)) ++
  primitiveOpen.map (fun (n, why) => (n, .openBoundary why))

/-- Every opcode has an explicit fragment assignment, including debugger ops. -/
def opcodeLedger : List (Opcode × Fragment) := Opcode.all.map fun o => (o, o.fragment)

/-- Coverage of the successful host compiler execution census. The measurement
itself remains validation evidence, as documented in OcamlcExecuted.lean. -/
theorem executed_opcodes_ledgered :
    ∀ o ∈ ocamlcExecutedOpcodes, o ∈ opcodeLedger.map (·.1) := by decide

theorem executed_primitives_ledgered :
    ∀ n ∈ ocamlcExecutedPrimitives, n ∈ primitiveLedger.map (·.1) := by decide

/-- Every primitive in the measured compiler run has an executable domain. -/
theorem executed_primitives_implemented :
    ∀ n ∈ ocamlcExecutedPrimitives, n ∈ primitiveDomains := by decide

end OCaml.Bytecode
