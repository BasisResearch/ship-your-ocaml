import OCaml.Bytecode.Syntax
import OCaml.Bytecode.Data
import OCaml.Bytecode.FloatOps
import OCaml.Bytecode.Os
import OCaml.Run.Kernel

/-!
# `BcSem`: executable ZINC semantics, fragments F1–F5

The deterministic `step P s` transcribes OCaml 4.14.4's interpreter and
selected C primitives. `Fragment.lean` records implemented argument domains
and open compiler boundaries; a listed primitive need not support every
possible argument. Core execution includes data, objects, caught exceptions,
formatting and buffered file/environment/time operations through `osCall`.
Re-entrant callbacks, marshalling, lexer/digest helpers and collector
statistics remain explicit boundaries. Machine-arm simulation is separate
from this executable semantics and its host differential validation.

Faithfulness conventions:

* `pc` indexes the OPCODE word (`Syntax.lean`); C's `pc + *pc` at operand
  `k` is our `pc + 1 + k + arg k`.
* The stack is a list, head = `sp[0]`. The trap pointer is kept as the
  depth (from the stack bottom) of the innermost trap frame, `0` = none
  (`Caml_state->trapsp = stack_high`); a trap frame stores its link as the
  word distance to the previous frame, exactly as `Trap_link_offset`.
* Integer operations are computed on the TAGGED 64-bit word exactly as the
  C does (`tag64`/`untag`), so wrapping and shift amounts (`sll`/`srl`/`sra`
  use the low 6 bits on RV64) are the binary's.
* The heap is abstract (`Value.lean`): no collection is ever observable in
  `BcSem`. The machine's collections are the representation predicate's
  business (`OCaml/Vm/Repr.lean`).
* A state for which the binary's behaviour depends on something `BcSem`
  abstracts away (an ordered comparison of pointers, a field read from an
  integer) steps to `.wrong`. Bytecode produced by `ocamlc` from well-typed
  programs never reaches it; the Layer A theorem assumes so (`Good`).
* Output: channels buffer exactly as `runtime/io.c` (`caml_putblock`,
  `Putch`, `caml_flush`, 64 KiB buffers); bytes written to fd 1 or 2 are
  appended to the console, the HTIF console that `Vsa.Machine.output`
  observes.
-/

namespace OCaml.Bytecode

/-! ## Programs and states -/

/-- A loaded bytecode program: what `caml_main` has built when it calls
`caml_interprete(code, size)` — the code, the primitive table, and the
global data already unmarshalled into the heap. -/
structure Prog where
  code : Code
  prims : Array String
  heap0 : Heap
  /-- `caml_global_data`. -/
  globals : Val
  /-- `caml_exe_name` and `main_argv` (an array of strings in `heap0`), set
  by `caml_sys_init` before the cut point. -/
  exeName : List UInt8
  argv : Val
  /-- The files embedded in the image (`src/gen_embed.sh`), `/prog` included. -/
  files0 : List (String × List UInt8)

/-- A channel (`struct channel`, `runtime/caml/io.h`): its fd, whether it is
an output channel (`max == NULL`), and the pending bytes of its buffer. -/
structure Chan where
  fd : Int
  isOut : Bool
  buf : List UInt8
  /-- Input read-ahead storage and cursor; output uses buf above. -/
  inBuf : List UInt8 := []
  inPos : Nat := 0
  /-- C channel offset: end of read-ahead, or bytes flushed on output. -/
  offset : Int := 0
  deriving DecidableEq, Repr

/-- The C-side world the primitives act on. -/
structure World where
  /-- `caml_all_opened_channels`, in creation order (id = index). -/
  chans : List Chan
  /-- `caml_register_named_value`. -/
  named : List (String × Val)
  /-- `oo_last_id` (`runtime/obj.c`), untagged. -/
  ooId : Nat
  /-- `caml_exe_name`. -/
  exeName : List UInt8
  /-- `main_argv` (`caml_sys_init`, allocated before the cut point). -/
  argv : Val
  /-- Files, descriptors, streams, environment, clock and exit state. -/
  os : TCB.Os.OsState
  deriving DecidableEq, Repr

/-- HTIF console interleaving, observed from the OS state. -/
def World.console (w : World) : List UInt8 := w.os.streams.console

def World.files (w : World) : List (String × List UInt8) := osFiles w.os

/-- A VM state: the interpreter's registers (`pc`, `accu`, `sp`, `env`,
`extra_args`, `Caml_state->trapsp`), the heap and the world. -/
structure St where
  pc : Nat
  accu : Val
  stack : List Val
  env : Val
  extra : Nat
  trap : Nat
  heap : Heap
  world : World

/-- `caml_interprete`'s initial registers for the main program:
`accu = Val_int(0)`, `env = Atom(0)`, `extra_args = 0`, empty stack. -/
def Prog.init (P : Prog) : St :=
  ⟨0, .int 0, [], .atom 0, 0, 0, P.heap0, ⟨[], [], 0, P.exeName, P.argv, osInitial P.files0⟩⟩

/-- Result of one step. -/
inductive Res where
  | next (s : St)
  /-- the program ended: HTIF exit code and the final world -/
  | halt (e : Nat) (w : World)
  /-- outside the fragment (ledgered in `Fragment.lean`) -/
  | unsupported
  /-- behaviour depends on what `BcSem` abstracts (never for `ocamlc` output
  of well-typed programs) -/
  | wrong

/-! ## Words -/

/-- The tagged 64-bit word of an integer value. -/
def tag64 (n : BitVec 63) : BitVec 64 := (n.signExtend 64 <<< 1) ||| 1

/-- `Long_val` of a tagged word, back to 63 bits. -/
def untag (w : BitVec 64) : BitVec 63 := (w.sshiftRight 1).truncate 63

/-- `Long_val` as a (64-bit) integer. -/
def longVal (n : BitVec 63) : BitVec 64 := n.signExtend 64

/-- Physical equality of two words (`EQ`/`NEQ`), where it is determined by
the abstraction: integers are odd words, pointers even and distinct per
(block, field). -/
def physEq? : Val → Val → Option Bool
  | .raw _, _ | _, .raw _ => none
  | a, b => some (a == b)

/-- Both integers. -/
def ints? : Val → Val → Option (BitVec 63 × BitVec 63)
  | .int a, .int b => some (a, b)
  | _, _ => none

@[inline] def opt {α} (o : Option α) (k : α → Res) : Res :=
  match o with
  | some a => k a
  | none => .wrong

/-! ## Channels (`runtime/io.c`) -/

/-- `IO_BUFFER_SIZE`. -/
def ioBufferSize : Nat := 65536

/-- Write a buffer to an fd: fds 1 and 2 are the console (`htif.c`'s
`_write` writes everything); other fds are not in F1. -/
def writeFd (w : World) (fd : Int) (b : List UInt8) : Option World :=
  if fd < 0 then none else do
    let (r, os) ← osCall w.os (.write fd.toNat b b.length)
    if r = .num b.length then pure { w with os := os } else none

def World.setChan (w : World) (id : Nat) (c : Chan) : World :=
  { w with chans := w.chans.set id c }

/-- `caml_flush`: write out the whole buffer. -/
def flushChan (w : World) (id : Nat) : Option World := do
  let c ← w.chans[id]?
  if c.fd = -1 then pure w else
  let w' ← writeFd w c.fd c.buf
  pure (w'.setChan id { c with buf := [], offset := c.offset + c.buf.length })

/-- `caml_putblock` iterated by `caml_ml_output_bytes`: fill the buffer;
when a block reaches the end of the buffer (`n ≥ free`), fill it and
write it out whole. -/
def putBlock (w : World) (id : Nat) : List UInt8 → Nat → Option World
  | [], _ => some w
  | bs, 0 => if bs = [] then some w else none
  | bs, fuel + 1 => do
    let c ← w.chans[id]?
    if c.fd < 0 then none else do
    let free := ioBufferSize - c.buf.length
    if bs.length < free then
      pure (w.setChan id { c with buf := c.buf ++ bs })
    else
      let full := c.buf ++ bs.take free
      let w' ← writeFd w c.fd full
      putBlock (w'.setChan id { c with buf := [], offset := c.offset + full.length }) id (bs.drop free) fuel

/-- `Putch`: flush first if the buffer is full, then append. -/
def putChar (w : World) (id : Nat) (b : UInt8) : Option World := do
  let c ← w.chans[id]?
  if c.fd < 0 then none else if c.buf.length ≥ ioBufferSize then
    let w' ← writeFd w c.fd c.buf
    pure (w'.setChan id { c with buf := [b], offset := c.offset + c.buf.length })
  else pure (w.setChan id { c with buf := c.buf ++ [b] })

/-! ## Primitives of F1 -/

/-- Result of a C primitive. -/
inductive PRes where
  | ok (accu : Val) (h : Heap) (w : World)
  | raise (exn : Val) (h : Heap) (w : World)
  | exit (code : Nat) (w : World)
  | unsupported

def strOf? (h : Heap) : Val → Option (List UInt8)
  | .ptr l 0 => match h.get? l with
    | some (.bytes b) => some b
    | _ => none
  | _ => none

def chanOf? (h : Heap) : Val → Option Nat
  | .ptr l 0 => match h.get? l with
    | some (.channel id) => some id
    | _ => none
  | _ => none

def intArg? : Val → Option Int
  | .int n => some n.toInt
  | _ => none

/-- Decimal rendering of `%ld`. -/
def decimal (n : Int) : List UInt8 :=
  (toString n).toList.map fun c => c.toNat.toUInt8

/-- Open a channel on `fd` (`caml_ml_open_descriptor_{in,out}`). -/
def openChan (h : Heap) (w : World) (fd : Int) (isOut : Bool) : PRes :=
  let id := w.chans.length
  let (h', l) := h.alloc (.channel id)
  .ok (.ptr l 0) h' { w with chans := w.chans ++ [⟨fd, isOut, [], [], 0, (match TCB.Os.lookupFd w.os fd.toNat with | .some (.file _ off _) => (if fd < 0 then -1 else off) | _ => -1)⟩] }

/-- `caml_ml_out_channels_list`: walks `caml_all_opened_channels` (most
recent first) consing a FRESH custom block per output channel, so the
result lists output channels oldest first. -/
def outChannelsList (h : Heap) (w : World) : Heap × Val :=
  let ids := ((List.range w.chans.length).filter fun i =>
    (w.chans[i]?.map (fun c => c.isOut && c.fd != -1)).getD false).reverse
  ids.foldl (fun (h, acc) id =>
    let (h1, lc) := h.alloc (.channel id)
    let (h2, cell) := h1.alloc (.block 0 [.ptr lc 0, acc])
    (h2, .ptr cell 0)) (h, .int 0)

/-- The primitives of F1 (`Fragment.lean`). -/
def primsF1 : List String :=
  [ "caml_register_named_value", "caml_ml_open_descriptor_out",
    "caml_ml_open_descriptor_in", "caml_ml_out_channels_list", "caml_ml_flush",
    "caml_ml_output_char", "caml_ml_output", "caml_ml_output_bytes", "caml_format_int",
    "caml_ml_string_length", "caml_ml_bytes_length", "caml_string_equal",
    "caml_string_notequal", "caml_int64_float_of_bits",
    "caml_sys_const_naked_pointers_checked", "caml_sys_const_big_endian",
    "caml_sys_const_word_size", "caml_sys_const_int_size", "caml_sys_const_max_wosize",
    "caml_sys_const_ostype_unix", "caml_sys_const_ostype_win32",
    "caml_sys_const_ostype_cygwin", "caml_sys_const_backend_type", "caml_sys_get_config",
    "caml_sys_executable_name", "caml_sys_argv", "caml_sys_get_argv", "caml_int_compare",
    "caml_fresh_oo_id", "caml_sys_exit" ]

/-- The F1 primitives' behaviour, by name, on their arguments (`accu`
first). An argument shape the fragment does not cover is `.unsupported`. -/
def primF1Impl (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  let some := fun {α} (o : Option α) (k : α → PRes) => match o with
    | .some a => k a
    | .none => PRes.unsupported
  match name, args with
  | "caml_register_named_value", [vn, v] =>
      some (strOf? h vn) fun n =>
        .ok .unit h { w with named := registerNamedValue (namedValueKey n) v w.named }
  | "caml_ml_open_descriptor_out", [fd] => some (intArg? fd) fun fd => openChan h w fd true
  | "caml_ml_open_descriptor_in", [fd] => some (intArg? fd) fun fd => openChan h w fd false
  | "caml_ml_out_channels_list", [_] =>
      let (h', l) := outChannelsList h w
      .ok l h' w
  | "caml_ml_flush", [ch] =>
      some (chanOf? h ch) fun id => some (flushChan w id) fun w' => .ok .unit h w'
  | "caml_ml_output_char", [ch, c] =>
      some (chanOf? h ch) fun id => some (intArg? c) fun c =>
        some (putChar w id (c % 256).toNat.toUInt8) fun w' => .ok .unit h w'
  | "caml_ml_output", [ch, s, ofs, len]
  | "caml_ml_output_bytes", [ch, s, ofs, len] =>
      some (chanOf? h ch) fun id => some (strOf? h s) fun b =>
      some (intArg? ofs) fun o => some (intArg? len) fun n =>
        if 0 ≤ o ∧ 0 ≤ n ∧ o + n ≤ b.length then
          some (putBlock w id ((b.drop o.toNat).take n.toNat) (n.toNat + 1)) fun w' => .ok .unit h w'
        else .unsupported
  | "caml_format_int", [fmt, .int n] =>
      some (strOf? h fmt) fun f => some (formatInteger f n) fun bs =>
      let (h', l) := h.alloc (.bytes bs)
      .ok (.ptr l 0) h' w
  | "caml_ml_string_length", [s] | "caml_ml_bytes_length", [s] =>
      some (strOf? h s) fun b => .ok (Val.ofInt b.length) h w
  | "caml_string_equal", [a, b] =>
      some (strOf? h a) fun a => some (strOf? h b) fun b => .ok (Val.ofBool (a == b)) h w
  | "caml_string_notequal", [a, b] =>
      some (strOf? h a) fun a => some (strOf? h b) fun b => .ok (Val.ofBool (a != b)) h w
  | "caml_int64_float_of_bits", [v] =>
      match v with
      | .ptr l 0 => match h.get? l with
        | .some (.int64 n) => let (h', d) := h.alloc (.double n); .ok (.ptr d 0) h' w
        | _ => .unsupported
      | _ => .unsupported
  | "caml_sys_const_naked_pointers_checked", [_] => .ok (Val.ofBool false) h w
  -- `runtime/sys.c` constants of this build (`m.h`/`s.h`: 64-bit,
  -- little-endian, OCAML_OS_TYPE "Unix", bytecode backend)
  | "caml_sys_const_big_endian", [_] => .ok (Val.ofBool false) h w
  | "caml_sys_const_word_size", [_] => .ok (Val.ofInt 64) h w
  | "caml_sys_const_int_size", [_] => .ok (Val.ofInt 63) h w
  | "caml_sys_const_max_wosize", [_] => .ok (Val.ofInt (2 ^ 54 - 1)) h w
  | "caml_sys_const_ostype_unix", [_] => .ok (Val.ofBool true) h w
  | "caml_sys_const_ostype_win32", [_] | "caml_sys_const_ostype_cygwin", [_] => .ok (Val.ofBool false) h w
  | "caml_sys_const_backend_type", [_] => .ok (Val.ofInt 1) h w
  | "caml_sys_get_config", [_] =>
      let (h1, os) := h.alloc (.bytes ("Unix".toList.map (·.toNat.toUInt8)))
      let (h2, r) := h1.alloc (.block 0 [.ptr os 0, Val.ofInt 64, Val.ofBool false])
      .ok (.ptr r 0) h2 w
  | "caml_sys_executable_name", [_] =>
      -- `caml_exe_name`: the path `caml_main` opened (`src/main.c`: "/prog")
      let (h', l) := h.alloc (.bytes w.exeName)
      .ok (.ptr l 0) h' w
  | "caml_sys_argv", [_] => .ok w.argv h w
  | "caml_sys_get_argv", [_] =>
      let (h1, e) := h.alloc (.bytes w.exeName)
      let (h2, r) := h1.alloc (.block 0 [.ptr e 0, w.argv])
      .ok (.ptr r 0) h2 w
  | "caml_int_compare", [a, b] =>
      some (intArg? a) fun a => some (intArg? b) fun b =>
        .ok (Val.ofInt (if a < b then -1 else if a > b then 1 else 0)) h w
  | "caml_fresh_oo_id", [_] => .ok (Val.ofInt w.ooId) h { w with ooId := w.ooId + 1 }
  | "caml_sys_exit", [c] => some (intArg? c) fun c =>
    let e := (BitVec.ofInt 32 c).toNat
    some (osCall w.os (.exit e)) fun (_, os) => .exit e { w with os := os }
  | _, _ => .unsupported

/-- The F1 primitives: `primF1Impl` on `primsF1`, `.unsupported` elsewhere. -/
def primF1 (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  if name ∈ primsF1 then primF1Impl name args h w else .unsupported

/-- Allocate the result of a data primitive. -/
def primAlloc (h : Heap) (w : World) (o : Obj) : PRes :=
  let (h', l) := h.alloc o
  .ok (.ptr l 0) h' w

/-- `caml_raise_with_string` with a built-in exception constructor. -/
def primException (globals : Val) (h : Heap) (w : World) (idx : Nat) (msg : String) : PRes :=
  match field? h globals idx with
  | none => .unsupported
  | .some ex =>
    let (h, l) := h.alloc (.bytes (msg.toList.map (·.toNat.toUInt8)))
    let (h, e) := h.alloc (.block 0 [ex, .ptr l 0])
    .raise (.ptr e 0) h w

/-- The data primitives currently transcribed from array.c, str.c and compare.c. -/
def primsF2 : List String :=
  [ "caml_string_compare", "caml_bytes_compare", "caml_array_sub", "caml_array_append", "caml_array_blit", "caml_array_fill", "caml_int_of_string", "caml_hash", "caml_array_unsafe_get", "caml_array_unsafe_set", "caml_string_of_bytes", "caml_bytes_of_string", "caml_make_vect", "caml_array_get", "caml_array_get_addr", "caml_array_set",
    "caml_array_set_addr", "caml_create_bytes", "caml_blit_bytes", "caml_blit_string",
    "caml_fill_bytes", "caml_bytes_get", "caml_string_get", "caml_bytes_set",
    "caml_compare", "caml_equal", "caml_notequal", "caml_lessthan", "caml_lessequal",
    "caml_greaterthan", "caml_greaterequal" ]

/-- F2's defined argument domain; unsafe calls outside their C preconditions
remain unsupported. `globals` supplies built-in exception identities. -/
def primF2 (globals : Val) (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  let some := fun {α} (o : Option α) (k : α → PRes) => match o with
    | .some a => k a
    | .none => PRes.unsupported
  let bounds := primException globals h w 3 "index out of bounds"
  match name, args with
  | "caml_make_vect", [.int n, v] =>
    if n.toInt < 0 ∨ n.toNat > 2^54 - 1 then primException globals h w 3 "Array.make"
    else if n = 0 then .ok (.atom 0) h w
    else match doubleOf? h v with
      | .some d => primAlloc h w (.doubleArray (List.replicate n.toNat d))
      | .none => primAlloc h w (.block 0 (List.replicate n.toNat v))
  | "caml_array_get", [a, .int n] | "caml_array_get_addr", [a, .int n]
  | "caml_array_unsafe_get", [a, .int n] =>
    some (size? h a) fun sz =>
    if n.toInt < 0 ∨ n.toNat ≥ sz then
      (if name = "caml_array_unsafe_get" ∨ name = "caml_array_unsafe_set" then .unsupported else bounds) else
    if name != "caml_array_get_addr" && tag? h a == .some doubleArrayTag then
      some (floatField? h a n.toNat) fun d => primAlloc h w (.double d)
    else some (field? h a n.toNat) fun v => .ok v h w
  | "caml_array_set", [a, .int n, v] | "caml_array_set_addr", [a, .int n, v]
  | "caml_array_unsafe_set", [a, .int n, v] =>
    some (size? h a) fun sz =>
    if n.toInt < 0 ∨ n.toNat ≥ sz then
      (if name = "caml_array_unsafe_get" ∨ name = "caml_array_unsafe_set" then .unsupported else bounds) else
    let write := if name != "caml_array_set_addr" && tag? h a == .some doubleArrayTag then
        (doubleOf? h v).bind (setFloatField? h a n.toNat)
      else setField? h a n.toNat v
    some write fun h' => .ok .unit h' w
  | "caml_string_compare", [a, b] | "caml_bytes_compare", [a, b] =>
    some (strOf? h a) fun a => some (strOf? h b) fun b => .ok (Val.ofInt (compareBytes a b)) h w
  | "caml_array_sub", [a, .int off, .int len] =>
    some (arrayObj? h a) fun a =>
    if off.toInt < 0 ∨ len.toInt < 0 then .unsupported else
    some (arraySlice a off.toNat len.toNat) fun o =>
      if o.wosize = 0 then .ok (.atom 0) h w else primAlloc h w o
  | "caml_array_append", [a, b] =>
    some (arrayObj? h a) fun a => some (arrayObj? h b) fun b =>
    some (arrayAppend a b) fun o =>
      if o.wosize = 0 then .ok (.atom 0) h w else primAlloc h w o
  | "caml_array_blit", [src, .int off, dst, .int to, .int len] =>
    if off.toInt < 0 ∨ to.toInt < 0 ∨ len.toInt < 0 then .unsupported else
    some (arrayObj? h src) fun src => some (arrayObj? h dst) fun target =>
    some (arraySlice src off.toNat len.toNat) fun part =>
    some (arraySplice target to.toNat part) fun out =>
      match dst with
      | .ptr l 0 => .ok .unit (h.set l out) w
      | .atom 0 => if len = 0 then .ok .unit h w else .unsupported
      | _ => .unsupported
  | "caml_array_fill", [dst, .int off, .int len, v] =>
    if off.toInt < 0 ∨ len.toInt < 0 then .unsupported else
    some (arrayObj? h dst) fun target =>
    let filled := match target with
      | .block 0 _ => .some (Obj.block 0 (List.replicate len.toNat v))
      | .doubleArray _ => (doubleOf? h v).map fun d => Obj.doubleArray (List.replicate len.toNat d)
      | _ => .none
    some filled fun part => some (arraySplice target off.toNat part) fun out =>
      match dst with
      | .ptr l 0 => .ok .unit (h.set l out) w
      | .atom 0 => if len = 0 then .ok .unit h w else .unsupported
      | _ => .unsupported
  | "caml_int_of_string", [v] => some (strOf? h v) fun bs =>
    match parseInteger bs with
    | .some n => .ok n h w
    | .none => primException globals h w 2 "int_of_string"
  | "caml_hash", [.int count, .int _, .int seed, .int v] =>
    let hsh := if count.toInt > 0 then hashIntnat (seed.setWidth 32) (tag64 v) else seed.setWidth 32
    .ok (Val.ofInt (hashFinish hsh).toNat) h w
  | "caml_string_of_bytes", [v] | "caml_bytes_of_string", [v] => .ok v h w
  | "caml_create_bytes", [.int n] =>
    if n.toInt < 0 ∨ n.toNat > (2^54 - 1)*8 - 1 then primException globals h w 3 "Bytes.create"
    else primAlloc h w (.bytes (List.replicate n.toNat 0))
  | "caml_blit_bytes", [src, .int off, dst, .int to, .int len]
  | "caml_blit_string", [src, .int off, dst, .int to, .int len] =>
    some (strOf? h src) fun bs => some (strOf? h dst) fun ds =>
    match dst with
    | .ptr l 0 =>
      if off.toInt < 0 ∨ to.toInt < 0 ∨ len.toInt < 0 ∨
          off.toNat + len.toNat > bs.length ∨ to.toNat + len.toNat > ds.length then .unsupported
      else .ok .unit (h.set l (.bytes (ds.take to.toNat ++
        (bs.drop off.toNat).take len.toNat ++ ds.drop (to.toNat + len.toNat)))) w
    | _ => .unsupported
  | "caml_fill_bytes", [dst, .int off, .int len, .int v] =>
    some (strOf? h dst) fun ds => match dst with
    | .ptr l 0 =>
      if off.toInt < 0 ∨ len.toInt < 0 ∨ off.toNat + len.toNat > ds.length then .unsupported
      else .ok .unit (h.set l (.bytes (ds.take off.toNat ++
        List.replicate len.toNat v.toNat.toUInt8 ++ ds.drop (off.toNat + len.toNat)))) w
    | _ => .unsupported
  | "caml_bytes_get", [a, .int n] | "caml_string_get", [a, .int n] =>
    some (strOf? h a) fun bs =>
    if n.toInt < 0 ∨ n.toNat ≥ bs.length then bounds
    else .ok (Val.ofInt (bs[n.toNat]!).toNat) h w
  | "caml_bytes_set", [a, .int n, .int v] =>
    some (strOf? h a) fun bs =>
    if n.toInt < 0 ∨ n.toNat ≥ bs.length then bounds else
    match a with
    | .ptr l 0 => .ok .unit (h.set l (.bytes (bs.set n.toNat v.toNat.toUInt8))) w
    | _ => .unsupported
  | nm, [a, b] =>
    if nm ∈ ["caml_compare", "caml_equal", "caml_notequal", "caml_lessthan", "caml_lessequal",
        "caml_greaterthan", "caml_greaterequal"] then
      some (compareVal h (nm == "caml_compare") (h.size + 1) a b) fun r =>
      let v := if nm = "caml_compare" then Val.ofInt r
        else Val.ofBool (match nm with
          | "caml_equal" => r == 0 | "caml_notequal" => r != 0
          | "caml_lessthan" => r < 0 | "caml_lessequal" => r ≤ 0
          | "caml_greaterthan" => r > 0 | _ => r ≥ 0)
      .ok v h w
    else .unsupported
  | _, _ => .unsupported

/-- Binary method-table search, from GETDYNMET's `li = 3`, tagged `hi`.
A miss is outside the safe domain of method invocation. -/
def methodLookup? (h : Heap) (obj : Val) (label : BitVec 63) : Option Val := do
  let methods ← field? h obj 0
  let .int count ← field? h methods 0 | none
  let rec search : Nat → Nat → Nat → Option Nat
    | 0, _, _ => none
    | fuel + 1, lo, hi => do
      if lo ≥ hi then return lo
      let mid := ((lo + hi) / 2) ||| 1
      let .int tag ← field? h methods mid | none
      if label.toInt < tag.toInt then search fuel lo (mid - 2)
      else search fuel mid hi
  let idx ← search (count.toNat + 1) 3 (2 * count.toNat + 1)
  let .int tag ← field? h methods idx | none
  if tag != label then none else field? h methods (idx - 1)

/-- Object primitives' supported domain (`runtime/obj.c`). Raw no-scan
allocation and retagging across representation kinds remain unsupported. -/
def primsF3 : List String :=
  ["caml_obj_block", "caml_obj_dup", "caml_obj_tag", "caml_obj_set_tag",
   "caml_obj_make_forward", "caml_set_oo_id"]

def primF3 (globals : Val) (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  let some := fun {α} (o : Option α) (k : α → PRes) => match o with
    | .some a => k a
    | .none => PRes.unsupported
  match name, args with
  | "caml_obj_block", [.int tag, .int n] =>
    let t := tag.toNat % 256
    if n.toInt < 0 ∨ t ≥ noScanTag then .unsupported
    else if t = closureTag ∧ n.toNat < 2 then primException globals h w 3 "Obj.new_block"
    else if n = 0 then .ok (.atom t) h w
    else
      let fs := List.replicate n.toNat Val.unit
      let fs := if t = closureTag then fs.set 1 (Val.ofInt 2) else fs
      primAlloc h w (.block t fs)
  | "caml_obj_dup", [.atom t] => .ok (.atom t) h w
  | "caml_obj_dup", [.ptr l 0] => some (h.get? l) fun o =>
    -- Custom operations pointers are preserved by memcpy. Channels alias
    -- the same external struct, as reflected by their unchanged channel id.
    primAlloc h w o
  | "caml_obj_tag", [v] =>
    if v.isInt then .ok (Val.ofInt 1000) h w
    else some (tag? h v) fun t => .ok (Val.ofInt t) h w
  | "caml_obj_set_tag", [.ptr l 0, .int t] => some (h.get? l) fun
    | .block _ fs => if t.toNat % 256 < noScanTag then
        .ok .unit (h.set l (.block (t.toNat % 256) fs)) w else .unsupported
    | _ => .unsupported
  | "caml_obj_make_forward", [.ptr l 0, v] => some (h.get? l) fun
    | .block _ (_ :: xs) => .ok .unit (h.set l (.block forwardTag (v :: xs))) w
    | _ => .unsupported
  | "caml_set_oo_id", [v] => some (setField? h v 1 (Val.ofInt w.ooId)) fun h' =>
    .ok v h' { w with ooId := w.ooId + 1 }
  | _, _ => .unsupported

/-- Fixed-width custom integer extraction, from runtime/ints.c. -/
def boxedInt? (h : Heap) (kind : String) : Val → Option (BitVec 64)
  | .ptr l 0 => match h.get? l with
    | .some (.int64 n) => if kind = "int64" then .some n else .none
    | .some (.nativeint n) => if kind = "nativeint" then .some n else .none
    | .some (.int32 n) => if kind = "int32" then .some (n.signExtend 64) else .none
    | _ => .none
  | _ => .none

def primBoxed (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  let some := fun {α} (o : Option α) (k : α → PRes) => match o with
    | .some a => k a
    | .none => PRes.unsupported
  let parts := name.splitOn "_"
  let kind := parts[1]?.getD ""
  let op := "_".intercalate (parts.drop 2)
  let box := fun (n : BitVec 64) => primAlloc h w
    (if kind = "int32" then .int32 (n.setWidth 32) else if kind = "nativeint" then .nativeint n else .int64 n)
  if kind ∉ ["int64", "int32", "nativeint"] then .unsupported else
  match op, args with
  | "of_int", [.int n] => box (n.signExtend 64)
  | "to_int", [v] => some (boxedInt? h kind v) fun n => .ok (Val.ofInt n.toInt) h w
  | "neg", [v] => some (boxedInt? h kind v) fun n => box (-n)
  | "shift_left", [v, .int n] => some (boxedInt? h kind v) fun v => box (v <<< (n.toNat % 64))
  | "shift_right", [v, .int n] => some (boxedInt? h kind v) fun v => box (v.sshiftRight (n.toNat % 64))
  | "shift_right_unsigned", [v, .int n] => some (boxedInt? h kind v) fun v =>
    box ((if kind = "int32" then v &&& 0xffffffff else v) >>> (n.toNat % 64))
  | op, [a, b] => some (boxedInt? h kind a) fun a => some (boxedInt? h kind b) fun b =>
    match op with
    | "add" => box (a + b) | "sub" => box (a - b) | "mul" => box (a * b)
    | "and" => box (a &&& b) | "or" => box (a ||| b) | "xor" => box (a ^^^ b)
    | "compare" => .ok (Val.ofInt (if a.toInt < b.toInt then -1 else if a.toInt > b.toInt then 1 else 0)) h w
    | _ => .unsupported
  | _, _ => .unsupported

/-- runtime/floats.c arithmetic and decimal printf. -/
def primFloat (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  let some := fun {α} (o : Option α) (k : α → PRes) => match o with
    | .some a => k a
    | .none => PRes.unsupported
  let box := fun (f : Float) => primAlloc h w (.double (floatBits f))
  match name, args with
  | "caml_format_float", [fmt, v] =>
    some (strOf? h fmt) fun fmt => some (doubleOf? h v) fun d =>
    some (formatDouble fmt d) fun bs => primAlloc h w (.bytes bs)
  | "caml_float_of_int", [.int n] =>
    let f := n.toInt.natAbs.toUInt64.toFloat
    box (if n.toInt < 0 then -f else f)
  | "caml_int_of_float", [v] => some (doubleOf? h v) fun d =>
    some (doubleRatio d) fun (n, den) =>
    let n := n / den
    if n ≥ 2^63 then .unsupported else
    .ok (Val.ofInt (if d.toNat / 2^63 = 0 then (n : Int) else -(n : Int))) h w
  | op, [v] => some (doubleOf? h v) fun d =>
    let f := floatFromBits d
    match op with
    | "caml_sqrt_float" => box f.sqrt
    | "caml_atan_float" => box (atan64 f)
    | "caml_neg_float" => box (-f)
    | "caml_abs_float" => box f.abs
    | _ => .unsupported
  | op, [a, b] => some (doubleOf? h a) fun a => some (doubleOf? h b) fun b =>
    let a := floatFromBits a
    let b := floatFromBits b
    match op with
    | "caml_add_float" => box (a + b) | "caml_sub_float" => box (a - b)
    | "caml_mul_float" => box (a * b) | "caml_div_float" => box (a / b)
    | _ => .unsupported
  | _, _ => .unsupported

/-- `caml_convert_flag_list` for sys.c's nine open flags. -/
def openFlags? (h : Heap) (v : Val) : Option TCB.Os.Fs.OpenFlags :=
  let rec go : Nat → Val → TCB.Os.Fs.OpenFlags → Option TCB.Os.Fs.OpenFlags
    | 0, _, _ => none
    | fuel + 1, v, f => match v with
      | .int 0 => some f
      | _ => do
        let .int k ← field? h v 0 | none
        let tail ← field? h v 1
        let f ← match k.toNat with
          | 0 => some f
          | 1 => some { f with access := .wronly }
          | 2 => some { f with access := .wronly, append := true }
          | 3 => some { f with creat := true }
          | 4 => some { f with trunc := true }
          | 5 => some { f with excl := true }
          | 6 | 7 | 8 => some f
          | _ => none
        go fuel tail f
  go (h.size + 1) v { access := .rdonly }

/-- strerror text used by the configured runtime's ordinary I/O failures. -/
def errnoText : TCB.Os.Errno → String
  | .ENOENT => "No such file or directory" | .EBADF => "Bad file descriptor"
  | .EACCES => "Permission denied" | .EEXIST => "File exists"
  | .ENOTDIR => "Not a directory" | .EISDIR => "Is a directory"
  | .EINVAL => "Invalid argument" | .ESPIPE => "Illegal seek"
  | .EROFS => "Read-only file system" | .ENOSPC => "No space left on device"
  | .ENOTEMPTY => "Directory not empty" | .EMFILE => "Too many open files"
  | e => e.name

def sysError (P : Prog) (h : Heap) (w : World) (e : TCB.Os.Errno) (path : String := "") : PRes :=
  primException P.globals h w 1 ((if path = "" then "" else path ++ ": ") ++ errnoText e)

/-- `caml_ml_input`'s one-buffer read, including its short-read behaviour.
The channel offset is the end of the read-ahead buffer, not the logical
position returned to OCaml. -/
def readChan (w : World) (id n : Nat) : Option (TCB.Os.Ret × World) := do
  let c ← w.chans[id]?
  if n = 0 then return (.bytes [], w)
  if c.fd < 0 then return (.err .EBADF, w)
  if c.isOut then none else do
  let n := min n (2^31 - 1)
  let unread := c.inBuf.drop c.inPos
  if n = 0 || !unread.isEmpty then
    let bs := unread.take n
    return (.bytes bs, w.setChan id { c with inPos := c.inPos + bs.length })
  let (r, os) ← osCall w.os (.read c.fd.toNat ioBufferSize)
  let w := { w with os := os }
  match r with
  | .bytes bs =>
    let out := bs.take n
    return (.bytes out, w.setChan id { c with inBuf := bs, inPos := out.length, offset := c.offset + bs.length })
  | _ => return (r, w)

/-- Input seeks inside the read-ahead buffer do not move the file descriptor. -/
def seekChan (w : World) (id : Nat) (pos : Int) : Option (TCB.Os.Ret × World) := do
  let c ← w.chans[id]?
  if c.fd < 0 then return (.err .EBADF, w)
  if !c.isOut && pos ≥ c.offset - c.inBuf.length && pos ≤ c.offset then
    return (.none, w.setChan id { c with inPos := (pos - c.offset + c.inBuf.length).toNat })
  let w ← if c.isOut then flushChan w id else some w
  let c ← w.chans[id]?
  let (r, os) ← osCall w.os (.lseek c.fd.toNat pos 0)
  let w := { w with os := os }
  match r with
  | .num p => return (.none, w.setChan id { c with inBuf := [], inPos := 0, offset := p })
  | _ => return (r, w)

/-- Environment lookup (`runtime/sys.c`), with Not_found's global identity. -/
def primOs (P : Prog) (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  let some := fun {α} (o : Option α) (k : α → PRes) => match o with
    | .some a => k a
    | .none => PRes.unsupported
  match name, args with
  | "caml_sys_open", [path, flags, .int _] =>
    some (strOf? h path) fun path => some (openFlags? h flags) fun flags =>
    let path := String.ofList (path.map fun b => Char.ofNat b.toNat)
    if path.contains '\x00' then sysError P h w .ENOENT path else
    some (osCall w.os (.open path flags)) fun (r, os) =>
    let w := { w with os := os }
    match r with
    | .num fd => .ok (Val.ofInt fd) h w
    | .err e => sysError P h w e path
    | _ => .unsupported
  | "caml_sys_file_exists", [path] => some (strOf? h path) fun bs =>
    let path := String.ofList (bs.map fun b => Char.ofNat b.toNat)
    some (osCall w.os (.stat path)) fun (r, os) =>
    .ok (Val.ofBool (match r with | .stats _ => true | _ => false)) h { w with os := os }
  | "caml_sys_remove", [path] => some (strOf? h path) fun bs =>
    let path := String.ofList (bs.map fun b => Char.ofNat b.toNat)
    some (osCall w.os (.unlink path)) fun (r, os) =>
    let w := { w with os := os }
    match r with
    | .none => .ok .unit h w | .err e => sysError P h w e path | _ => .unsupported
  | "caml_sys_rename", [src, dst] => some (strOf? h src) fun src => some (strOf? h dst) fun dst =>
    let src := String.ofList (src.map fun b => Char.ofNat b.toNat)
    let dst := String.ofList (dst.map fun b => Char.ofNat b.toNat)
    some (osCall w.os (.rename src dst)) fun (r, os) =>
    let w := { w with os := os }
    match r with
    | .none => .ok .unit h w | .err e => sysError P h w e | _ => .unsupported
  | "caml_sys_close", [.int fd] =>
    if fd.toInt < 0 then .ok .unit h w else
    some (osCall w.os (.close fd.toNat)) fun (_, os) => .ok .unit h { w with os := os }
  | "caml_ml_set_channel_name", [ch, nm] =>
    some (chanOf? h ch) fun _ => some (strOf? h nm) fun _ => .ok .unit h w
  | "caml_ml_set_binary_mode", [ch, .int _] => some (chanOf? h ch) fun _ => .ok .unit h w
  | "caml_ml_close_channel", [ch] => some (chanOf? h ch) fun id => some w.chans[id]? fun c =>
    if c.fd < 0 then .ok .unit h w else
    some (osCall w.os (.close c.fd.toNat)) fun (r, os) =>
    let w := ({ w with os := os } : World).setChan id { c with fd := -1, buf := [], inBuf := [], inPos := 0 }
    match r with
    | .none => .ok .unit h w | .err e => sysError P h w e | _ => .unsupported
  | "caml_ml_input", [ch, dst, .int start, .int len] =>
    some (chanOf? h ch) fun id => some (strOf? h dst) fun buf =>
    if start.toInt < 0 ∨ len.toInt < 0 ∨ start.toNat + len.toNat > buf.length then .unsupported else
    some (readChan w id len.toNat) fun (r, w) =>
    match r, dst with
    | .bytes bs, .ptr l 0 =>
      let out := buf.take start.toNat ++ bs ++ buf.drop (start.toNat + bs.length)
      .ok (Val.ofInt bs.length) (h.set l (.bytes out)) w
    | .err e, _ => sysError P h w e
    | _, _ => .unsupported
  | "caml_ml_input_char", [ch] => some (chanOf? h ch) fun id =>
    some (readChan w id 1) fun (r, w) => match r with
    | .bytes [b] => .ok (Val.ofInt b.toNat) h w
    | .bytes [] => some (field? h P.globals 4) fun exn => .raise exn h w
    | .err e => sysError P h w e
    | _ => .unsupported
  | "caml_ml_output_int", [ch, .int n] => some (chanOf? h ch) fun id =>
    let bs := [24, 16, 8, 0].map fun shift => (n.toNat / 2^shift % 256).toUInt8
    some (putBlock w id bs 5) fun w => .ok .unit h w
  | "caml_ml_pos_out", [ch] | "caml_ml_pos_in", [ch] =>
    some (chanOf? h ch) fun id => some w.chans[id]? fun c =>
    if c.fd < 0 then .unsupported else
    .ok (Val.ofInt (if c.isOut then c.offset + c.buf.length else c.offset - (c.inBuf.length - c.inPos))) h w
  | "caml_ml_seek_out", [ch, .int pos] | "caml_ml_seek_in", [ch, .int pos] =>
    some (chanOf? h ch) fun id => some (seekChan w id pos.toInt) fun (r, w) =>
    match r with
    | .none => .ok .unit h w | .err e => sysError P h w e | _ => .unsupported
  | "caml_sys_time", [_] | "caml_sys_time_include_children", [_] =>
    some (osCall w.os .clock) fun (r, os) => match r with
    | .num n => primAlloc h { w with os := os } (.double (floatBits (n.toNat.toUInt64.toFloat / 1000000.0)))
    | _ => .unsupported
  | "caml_sys_getenv", [v] => match strOf? h v with
    | none => .unsupported
    | .some bs =>
      let key := String.ofList (bs.map fun b => Char.ofNat b.toNat)
      match osCall w.os (.getenv key) with
      | .some (.bytes bytes, os) => primAlloc h { w with os := os } (.bytes bytes)
      | .some (.none, os) => match field? h P.globals 6 with
        | .some exn => .raise exn h { w with os := os }
        | none => .unsupported
      | _ => .unsupported
  | _, _ => .unsupported

/-- Fragment dispatcher. An unsupported argument domain remains explicit. -/
def prim (P : Prog) (name : String) (args : List Val) (h : Heap) (w : World) : PRes :=
  if name ∈ primsF1 then primF1 name args h w
  else if name ∈ primsF2 then primF2 P.globals name args h w
  else if name ∈ primsF3 then primF3 P.globals name args h w
  else if name = "caml_get_exception_raw_backtrace" && args == [.unit] then .ok (.atom 0) h w
  else if name = "caml_restore_raw_backtrace" && args.length == 2 && args[1]? == .some (.atom 0) then .ok .unit h w
  else if name = "caml_backtrace_status" && args == [.unit] then .ok (Val.ofBool false) h w
  else match primBoxed name args h w with
    | .unsupported => match primFloat name args h w with
      | .unsupported => primOs P name args h w
      | r => r
    | r => r

/-! ## The step function -/

section
variable (P : Prog) (s : St)

/-- Advance past an instruction of `n` words. -/
def St.adv (s : St) (n : Nat) : St := { s with pc := s.pc + n }

/-- Code target `pc + 1 + k + ofs` of operand `k` (an absolute code index). -/
def target (pc k : Nat) (ofs : Int) : Option Nat :=
  let t := (pc + 1 + k : Int) + ofs
  if t < 0 then none else some t.toNat

/-- The exception-raising path (`raise_notrace:` in `interp.c`): unwind to
the innermost trap frame. An exception reaching the top is not in F1. -/
def raiseTo (s : St) (exn : Val) : Res :=
  if s.trap = 0 then .unsupported else
  let len := s.stack.length
  if len < s.trap then .wrong else
  match s.stack.drop (len - s.trap) with
  | .code h :: .int link :: env :: .int ex :: rest =>
      let d := s.trap
      if link.toNat > d then .wrong else
      .next { s with pc := h, accu := exn, stack := rest, env := env, extra := ex.toNat, trap := d - link.toNat }
  | _ => .wrong

/-- Apply the closure in `accu` (`pc = Code_val(accu); env = accu`). -/
def enter (s : St) (stack : List Val) (extra : Nat) : Res :=
  opt (field? s.heap s.accu 0) fun
    | .code c => .next { s with pc := c, env := s.accu, stack := stack, extra := extra }
    | _ => .wrong

/-- Run a C primitive (`C_CALLn`, `n = args.length`): pops `n - 1` stack
words. -/
def cCall (P : Prog) (s : St) (len : Nat) (name : String) (args : List Val) : Res :=
  let heap := s.heap
  let world := s.world
  let s := { s with heap := ⟨#[]⟩, world := world }
  match prim P name args heap world with
  | .ok a h w => .next { s with pc := s.pc + len, accu := a, heap := h, world := w, stack := s.stack.drop (args.length - 1) }
  | .raise e h w =>
      let s' : St := { s with heap := h, world := w, stack := s.stack.drop (args.length - 1) }
      raiseTo s' e
  | .exit c w => .halt c w
  | .unsupported => .unsupported

/-- Integer binary operation computed on the tagged words (`accu` op `sp[0]`). -/
def intOp (f : BitVec 64 → BitVec 64 → BitVec 64) : Res :=
  match s.stack with
  | b :: rest => opt (ints? s.accu b) fun (x, y) =>
      .next { s with pc := s.pc + 1, accu := .int (untag (f (tag64 x) (tag64 y))), stack := rest }
  | [] => .wrong

/-- Word comparison producing `Val_int`. -/
def cmpOp (f : BitVec 64 → BitVec 64 → Bool) : Res :=
  match s.stack with
  | b :: rest => opt (ints? s.accu b) fun (x, y) =>
      .next { s with pc := s.pc + 1, accu := Val.ofBool (f (tag64 x) (tag64 y)), stack := rest }
  | [] => .wrong

/-- `Integer_branch_comparison`: compare the operand `n` with `Long_val(accu)`. -/
def brOp (n ofs : Int) (f : BitVec 64 → BitVec 64 → Bool) : Res :=
  match s.accu with
  | .int a =>
      if f (BitVec.ofInt 64 n) (longVal a) then
        opt (target s.pc 1 ofs) fun t => .next { s with pc := t }
      else .next (s.adv 3)
  | _ => .wrong

/-- `MAKEBLOCK`: `Field(b,0) = accu`, the rest popped from the stack. -/
def makeBlock (len size tag : Nat) : Res :=
  if size = 0 then .wrong else
  if s.stack.length < size - 1 then .wrong else
  let (h, l) := s.heap.alloc (.block tag (s.accu :: s.stack.take (size - 1)))
  .next { s with pc := s.pc + len, accu := .ptr l 0, heap := h, stack := s.stack.drop (size - 1) }

/-- Push `accu` first (the `PUSH…` variants). -/
def pushAccu (s : St) : St := { s with stack := s.accu :: s.stack }

/-- One step of the ZINC machine: `caml_interprete`'s arm for the
instruction at `pc`. -/
def stepI (i : Instr) : Res :=
  let pc := s.pc
  let stk := s.stack
  let nth := fun (k : Nat) => stk[k]?
  match i.op, i.args with
  -- Accumulator and stack
  | .ACC0, [] => opt (nth 0) fun v => .next { (s.adv 1) with accu := v }
  | .ACC1, [] => opt (nth 1) fun v => .next { (s.adv 1) with accu := v }
  | .ACC2, [] => opt (nth 2) fun v => .next { (s.adv 1) with accu := v }
  | .ACC3, [] => opt (nth 3) fun v => .next { (s.adv 1) with accu := v }
  | .ACC4, [] => opt (nth 4) fun v => .next { (s.adv 1) with accu := v }
  | .ACC5, [] => opt (nth 5) fun v => .next { (s.adv 1) with accu := v }
  | .ACC6, [] => opt (nth 6) fun v => .next { (s.adv 1) with accu := v }
  | .ACC7, [] => opt (nth 7) fun v => .next { (s.adv 1) with accu := v }
  | .ACC, [n] => opt (stk[n.toNat]?) fun v => .next { (s.adv 2) with accu := v }
  | .PUSH, [] | .PUSHACC0, [] => .next (pushAccu (s.adv 1))
  | .PUSHACC1, [] => opt (nth 0) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC2, [] => opt (nth 1) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC3, [] => opt (nth 2) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC4, [] => opt (nth 3) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC5, [] => opt (nth 4) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC6, [] => opt (nth 5) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC7, [] => opt (nth 6) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHACC, [n] =>
      -- `*--sp = accu; accu = sp[*pc++]` : index n of the pushed stack
      opt ((s.accu :: stk)[n.toNat]?) fun v => .next { (pushAccu (s.adv 2)) with accu := v }
  | .POP, [n] => if stk.length < n.toNat then .wrong else .next { (s.adv 2) with stack := stk.drop n.toNat }
  | .ASSIGN, [n] =>
      if n.toNat < stk.length then
        .next { (s.adv 2) with stack := stk.set n.toNat s.accu, accu := .unit }
      else .wrong
  -- Environment
  | .ENVACC1, [] => opt (field? s.heap s.env 1) fun v => .next { (s.adv 1) with accu := v }
  | .ENVACC2, [] => opt (field? s.heap s.env 2) fun v => .next { (s.adv 1) with accu := v }
  | .ENVACC3, [] => opt (field? s.heap s.env 3) fun v => .next { (s.adv 1) with accu := v }
  | .ENVACC4, [] => opt (field? s.heap s.env 4) fun v => .next { (s.adv 1) with accu := v }
  | .ENVACC, [n] => opt (field? s.heap s.env n.toNat) fun v => .next { (s.adv 2) with accu := v }
  | .PUSHENVACC1, [] => opt (field? s.heap s.env 1) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHENVACC2, [] => opt (field? s.heap s.env 2) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHENVACC3, [] => opt (field? s.heap s.env 3) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHENVACC4, [] => opt (field? s.heap s.env 4) fun v => .next { (pushAccu (s.adv 1)) with accu := v }
  | .PUSHENVACC, [n] => opt (field? s.heap s.env n.toNat) fun v => .next { (pushAccu (s.adv 2)) with accu := v }
  -- Function application
  | .PUSH_RETADDR, [ofs] => opt (target pc 0 ofs) fun r =>
      .next { (s.adv 2) with stack := .code r :: s.env :: Val.ofInt s.extra :: stk }
  | .APPLY, [n] => if n < 1 then .wrong else enter s stk (n.toNat - 1)
  | .APPLY1, [] => match stk with
      | a1 :: rest => enter s (a1 :: .code (pc + 1) :: s.env :: Val.ofInt s.extra :: rest) 0
      | _ => .wrong
  | .APPLY2, [] => match stk with
      | a1 :: a2 :: rest => enter s (a1 :: a2 :: .code (pc + 1) :: s.env :: Val.ofInt s.extra :: rest) 1
      | _ => .wrong
  | .APPLY3, [] => match stk with
      | a1 :: a2 :: a3 :: rest =>
          enter s (a1 :: a2 :: a3 :: .code (pc + 1) :: s.env :: Val.ofInt s.extra :: rest) 2
      | _ => .wrong
  | .APPTERM, [nargs, slot] =>
      let n := nargs.toNat; let k := slot.toNat
      if n = 0 ∨ k < n ∨ stk.length < k then .wrong else
      enter s (stk.take n ++ stk.drop k) (s.extra + n - 1)
  | .APPTERM1, [slot] =>
      if slot < 1 ∨ stk.length < slot.toNat then .wrong else
      enter s (stk.take 1 ++ stk.drop slot.toNat) s.extra
  | .APPTERM2, [slot] =>
      if slot < 2 ∨ stk.length < slot.toNat then .wrong else
      enter s (stk.take 2 ++ stk.drop slot.toNat) (s.extra + 1)
  | .APPTERM3, [slot] =>
      if slot < 3 ∨ stk.length < slot.toNat then .wrong else
      enter s (stk.take 3 ++ stk.drop slot.toNat) (s.extra + 2)
  | .RETURN, [n] =>
      let rest := stk.drop n.toNat
      if stk.length < n.toNat then .wrong else
      if s.extra > 0 then enter s rest (s.extra - 1)
      else match rest with
        | .code r :: env :: .int ex :: rest' =>
            .next { s with pc := r, env := env, extra := ex.toNat, stack := rest' }
        | _ => .wrong
  | .RESTART, [] =>
      match s.env with
      | .ptr l 0 => match s.heap.get? l with
        | some (.block _ fs) =>
            if fs.length < 3 then .wrong else
            .next { (s.adv 1) with
              stack := fs.drop 3 ++ stk, env := fs.getD 2 .unit, extra := s.extra + (fs.length - 3) }
        | _ => .wrong
      | _ => .wrong
  | .GRAB, [req] =>
      if req.toNat ≤ s.extra then .next { (s.adv 2) with extra := s.extra - req.toNat }
      else
        let na := 1 + s.extra
        -- C's `pc - 3` is taken after the operand read (C `pc` = our `pc + 2`):
        -- the RESTART just before this GRAB
        if stk.length < na + 3 ∨ pc < 1 then .wrong else
        let (h, l) := s.heap.alloc (.block closureTag
          (.code (pc - 1) :: Val.ofInt 2 :: s.env :: stk.take na))
        match stk.drop na with
        | .code r :: env :: .int ex :: rest =>
            .next { s with pc := r, accu := .ptr l 0, heap := h, env := env, extra := ex.toNat, stack := rest }
        | _ => .wrong
  | .CLOSURE, [nv, ofs] =>
      let n := nv.toNat
      let stk' := if n > 0 then s.accu :: stk else stk
      if stk'.length < n then .wrong else
      opt (target pc 1 ofs) fun c =>
      let (h, l) := s.heap.alloc (.block closureTag (.code c :: Val.ofInt 2 :: stk'.take n))
      .next { (s.adv 3) with accu := .ptr l 0, heap := h, stack := stk'.drop n }
  | .CLOSUREREC, nf :: nv :: ofss =>
      let f := nf.toNat; let n := nv.toNat
      if f = 0 ∨ ofss.length ≠ f then .wrong else
      let stk' := if n > 0 then s.accu :: stk else stk
      if stk'.length < n then .wrong else
      -- `pc + pc[i]` with `pc` at the first offset: every offset is relative
      -- to the table start (operand 2), not to its own slot
      opt (ofss.mapM fun o => target pc 2 o) fun cs =>
      let envofs := 3 * f - 1
      -- function k ≥ 1 sits at field 3k, its infix header at 3k - 1
      let funWords := (cs.zipIdx.map fun (c, k) =>
        (if k = 0 then [] else [Val.raw (BitVec.ofNat 64 ((3 * k) * 1024 + infixTag))]) ++
        [Val.code c, Val.ofInt (envofs - 3 * k)]).flatten
      let (h, l) := s.heap.alloc (.block closureTag (funWords ++ stk'.take n))
      -- `*--sp = accu` then the infix pointers, last function on top
      let infixPtrs := ((List.range f).drop 1).reverse.map fun k => Val.ptr l (3 * k)
      .next { (s.adv (3 + f)) with accu := .ptr l 0, heap := h, stack := infixPtrs ++ (Val.ptr l 0 :: stk'.drop n) }
  | .OFFSETCLOSUREM3, [] | .PUSHOFFSETCLOSUREM3, [] | .OFFSETCLOSURE0, []
  | .PUSHOFFSETCLOSURE0, [] | .OFFSETCLOSURE3, [] | .PUSHOFFSETCLOSURE3, []
  | .OFFSETCLOSURE, [_] | .PUSHOFFSETCLOSURE, [_] =>
      let d : Int := match i.op, i.args with
        | .OFFSETCLOSUREM3, _ | .PUSHOFFSETCLOSUREM3, _ => -3
        | .OFFSETCLOSURE3, _ | .PUSHOFFSETCLOSURE3, _ => 3
        | .OFFSETCLOSURE, [n] | .PUSHOFFSETCLOSURE, [n] => n
        | _, _ => 0
      let push := match i.op with
        | .PUSHOFFSETCLOSUREM3 | .PUSHOFFSETCLOSURE0 | .PUSHOFFSETCLOSURE3
        | .PUSHOFFSETCLOSURE => true
        | _ => false
      let s1 := if push then pushAccu s else s
      match s.env with
      | .ptr l k =>
          if (k : Int) + d < 0 then .wrong else
          .next { (s1.adv (1 + i.args.length)) with accu := .ptr l ((k : Int) + d).toNat }
      | _ => .wrong
  -- Globals
  | .GETGLOBAL, [n] => opt (field? s.heap P.globals n.toNat) fun v => .next { (s.adv 2) with accu := v }
  | .PUSHGETGLOBAL, [n] =>
      opt (field? s.heap P.globals n.toNat) fun v => .next { (pushAccu (s.adv 2)) with accu := v }
  | .GETGLOBALFIELD, [n, k] =>
      opt (field? s.heap P.globals n.toNat) fun g =>
      opt (field? s.heap g k.toNat) fun v => .next { (s.adv 3) with accu := v }
  | .PUSHGETGLOBALFIELD, [n, k] =>
      opt (field? s.heap P.globals n.toNat) fun g =>
      opt (field? s.heap g k.toNat) fun v => .next { (pushAccu (s.adv 3)) with accu := v }
  | .SETGLOBAL, [n] =>
      opt (setField? s.heap P.globals n.toNat s.accu) fun h =>
        .next { (s.adv 2) with heap := h, accu := .unit }
  -- Blocks
  | .ATOM0, [] => .next { (s.adv 1) with accu := .atom 0 }
  | .ATOM, [t] => .next { (s.adv 2) with accu := .atom t.toNat }
  | .PUSHATOM0, [] => .next { (pushAccu (s.adv 1)) with accu := .atom 0 }
  | .PUSHATOM, [t] => .next { (pushAccu (s.adv 2)) with accu := .atom t.toNat }
  | .MAKEBLOCK, [sz, t] => makeBlock s 3 sz.toNat t.toNat
  | .MAKEBLOCK1, [t] => makeBlock s 2 1 t.toNat
  | .MAKEBLOCK2, [t] => makeBlock s 2 2 t.toNat
  | .MAKEBLOCK3, [t] => makeBlock s 2 3 t.toNat
  | .GETFIELD0, [] => opt (field? s.heap s.accu 0) fun v => .next { (s.adv 1) with accu := v }
  | .GETFIELD1, [] => opt (field? s.heap s.accu 1) fun v => .next { (s.adv 1) with accu := v }
  | .GETFIELD2, [] => opt (field? s.heap s.accu 2) fun v => .next { (s.adv 1) with accu := v }
  | .GETFIELD3, [] => opt (field? s.heap s.accu 3) fun v => .next { (s.adv 1) with accu := v }
  | .GETFIELD, [n] => opt (field? s.heap s.accu n.toNat) fun v => .next { (s.adv 2) with accu := v }
  | .SETFIELD0, [] | .SETFIELD1, [] | .SETFIELD2, [] | .SETFIELD3, [] | .SETFIELD, [_] =>
      let k := match i.op, i.args with
        | .SETFIELD1, _ => 1 | .SETFIELD2, _ => 2 | .SETFIELD3, _ => 3
        | .SETFIELD, [n] => n.toNat | _, _ => 0
      match stk with
      | v :: rest => opt (setField? s.heap s.accu k v) fun h =>
          .next { (s.adv (1 + i.args.length)) with heap := h, accu := .unit, stack := rest }
      | [] => .wrong
  -- F2 data: runtime/interp.c, MAKEFLOATBLOCK through SETBYTESCHAR.
  | .MAKEFLOATBLOCK, [sz] =>
      if sz ≤ 0 ∨ stk.length < sz.toNat - 1 then .wrong else
      opt ((s.accu :: stk.take (sz.toNat - 1)).mapM (doubleOf? s.heap)) fun ds =>
      let (h, l) := s.heap.alloc (.doubleArray ds)
      .next { (s.adv 2) with accu := .ptr l 0, heap := h, stack := stk.drop (sz.toNat - 1) }
  | .GETFLOATFIELD, [n] => opt (floatField? s.heap s.accu n.toNat) fun d =>
      let (h, l) := s.heap.alloc (.double d)
      .next { (s.adv 2) with accu := .ptr l 0, heap := h }
  | .SETFLOATFIELD, [n] => match stk with
      | v :: rest => opt (doubleOf? s.heap v) fun d =>
          opt (setFloatField? s.heap s.accu n.toNat d) fun h =>
          .next { (s.adv 2) with accu := .unit, heap := h, stack := rest }
      | _ => .wrong
  | .VECTLENGTH, [] => opt (size? s.heap s.accu) fun n =>
      .next { (s.adv 1) with accu := Val.ofInt n }
  | .GETVECTITEM, [] => match stk with
      | .int n :: rest => opt (field? s.heap s.accu n.toNat) fun v =>
          .next { (s.adv 1) with accu := v, stack := rest }
      | _ => .wrong
  | .SETVECTITEM, [] => match stk with
      | .int n :: v :: rest => opt (setField? s.heap s.accu n.toNat v) fun h =>
          .next { (s.adv 1) with accu := .unit, heap := h, stack := rest }
      | _ => .wrong
  | .GETBYTESCHAR, [] | .GETSTRINGCHAR, [] => match stk with
      | .int n :: rest => opt (strOf? s.heap s.accu) fun bs => opt bs[n.toNat]? fun b =>
          .next { (s.adv 1) with accu := Val.ofInt b.toNat, stack := rest }
      | _ => .wrong
  | .SETBYTESCHAR, [] => match s.accu, stk with
      | .ptr l 0, .int n :: .int b :: rest => opt (strOf? s.heap s.accu) fun bs =>
          if n.toNat < bs.length then
            .next { (s.adv 1) with accu := .unit, stack := rest, heap := s.heap.set l (.bytes (bs.set n.toNat b.toNat.toUInt8)) }
          else .wrong
      | _, _ => .wrong
  -- F3: the uncached lookup path of interp.c. Cache correctness is a
  -- separate representation obligation; semantic lookup checks the label.
  | .GETMETHOD, [] => match s.accu, stk with
      | .int n, obj :: _ => opt (field? s.heap obj 0) fun ms =>
        opt (field? s.heap ms n.toNat) fun v => .next { (s.adv 1) with accu := v }
      | _, _ => .wrong
  | .GETPUBMET, [label, _] => opt (methodLookup? s.heap s.accu (BitVec.ofInt 63 label)) fun v =>
      .next { (s.adv 3) with accu := v, stack := s.accu :: stk }
  | .GETDYNMET, [] => match s.accu, stk with
      | .int label, obj :: _ => opt (methodLookup? s.heap obj label) fun v =>
        .next { (s.adv 1) with accu := v }
      | _, _ => .wrong
  -- Branches
  | .BRANCH, [ofs] => opt (target pc 0 ofs) fun t => .next { s with pc := t }
  | .BRANCHIF, [ofs] =>
      if s.accu = .int 0 then .next (s.adv 2) else opt (target pc 0 ofs) fun t => .next { s with pc := t }
  | .BRANCHIFNOT, [ofs] =>
      if s.accu = .int 0 then opt (target pc 0 ofs) fun t => .next { s with pc := t } else .next (s.adv 2)
  | .SWITCH, sizes :: tbl =>
      let nc := sizes.toNat % 65536
      let idx : Option Nat := match s.accu with
        | .int n => if 0 ≤ n.toInt ∧ n.toInt < nc then some n.toNat else none
        | v => (tag? s.heap v).bind fun t => if t < sizes.toNat / 65536 then some (nc + t) else none
      -- `pc += pc[k]` with `pc` at the table start (operand 1)
      opt idx fun k => opt tbl[k]? fun o => opt (target pc 1 o) fun t => .next { s with pc := t }
  | .BOOLNOT, [] => match s.accu with
      | .int n => .next { (s.adv 1) with accu := .int (1 - n) }
      | _ => .wrong
  -- Exceptions
  | .PUSHTRAP, [ofs] => opt (target pc 0 ofs) fun h =>
      let d := stk.length + 4
      .next { (s.adv 2) with stack := .code h :: Val.ofInt (d - s.trap) :: s.env :: Val.ofInt s.extra :: stk, trap := d }
  | .POPTRAP, [] => match stk with
      | _ :: .int link :: _ :: _ :: rest =>
          if link.toNat > stk.length then .wrong else
          .next { (s.adv 1) with trap := stk.length - link.toNat, stack := rest }
      | _ => .wrong
  | .RAISE, [] | .RERAISE, [] | .RAISE_NOTRACE, [] => raiseTo s s.accu
  | .CHECK_SIGNALS, [] => .next (s.adv 1)
  -- C calls
  | .C_CALL1, [p] => opt P.prims[p.toNat]? fun nm => cCall P s 2 nm [s.accu]
  | .C_CALL2, [p] => opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: stk.take 1)
  | .C_CALL3, [p] => opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: stk.take 2)
  | .C_CALL4, [p] => opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: stk.take 3)
  | .C_CALL5, [p] => opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: stk.take 4)
  | .C_CALLN, [n, p] =>
      if n ≤ 0 ∨ stk.length < n.toNat - 1 then .wrong else
      opt P.prims[p.toNat]? fun nm => cCall P s 3 nm (s.accu :: stk.take (n.toNat - 1))
  -- Integer constants and arithmetic
  | .CONST0, [] => .next { (s.adv 1) with accu := .int 0 }
  | .CONST1, [] => .next { (s.adv 1) with accu := .int 1 }
  | .CONST2, [] => .next { (s.adv 1) with accu := .int 2 }
  | .CONST3, [] => .next { (s.adv 1) with accu := .int 3 }
  | .CONSTINT, [n] => .next { (s.adv 2) with accu := Val.ofInt n }
  | .PUSHCONST0, [] => .next { (pushAccu (s.adv 1)) with accu := .int 0 }
  | .PUSHCONST1, [] => .next { (pushAccu (s.adv 1)) with accu := .int 1 }
  | .PUSHCONST2, [] => .next { (pushAccu (s.adv 1)) with accu := .int 2 }
  | .PUSHCONST3, [] => .next { (pushAccu (s.adv 1)) with accu := .int 3 }
  | .PUSHCONSTINT, [n] => .next { (pushAccu (s.adv 2)) with accu := Val.ofInt n }
  | .NEGINT, [] => match s.accu with
      | .int a => .next { (s.adv 1) with accu := .int (untag (2 - tag64 a)) }
      | _ => .wrong
  | .ADDINT, [] => intOp s fun a b => a + b - 1
  | .SUBINT, [] => intOp s fun a b => a - b + 1
  | .MULINT, [] => intOp s fun a b => tag64 (untag a * untag b)
  | .DIVINT, [] | .MODINT, [] => match stk with
      | b :: rest => opt (ints? s.accu b) fun (x, y) =>
          if y = 0 then
            -- `caml_raise_zero_divide`: Field(caml_global_data, ZERO_DIVIDE_EXN = 5)
            opt (field? s.heap P.globals 5) fun e => raiseTo { s with stack := rest } e
          else
            let r := if i.op = .DIVINT then x.sdiv y else x.srem y
            .next { (s.adv 1) with accu := .int r, stack := rest }
      | [] => .wrong
  | .ANDINT, [] => intOp s fun a b => a &&& b
  | .ORINT, [] => intOp s fun a b => a ||| b
  | .XORINT, [] => intOp s fun a b => (a ^^^ b) ||| 1
  | .LSLINT, [] => intOp s fun a b => ((a - 1) <<< ((untag b).toNat % 64)) + 1
  | .LSRINT, [] => intOp s fun a b => (a >>> ((untag b).toNat % 64)) ||| 1
  | .ASRINT, [] => intOp s fun a b => (a.sshiftRight ((untag b).toNat % 64)) ||| 1
  | .EQ, [] | .NEQ, [] => match stk with
      | b :: rest => opt (physEq? s.accu b) fun e =>
          .next { (s.adv 1) with accu := Val.ofBool (if i.op = .EQ then e else !e), stack := rest }
      | [] => .wrong
  | .LTINT, [] => cmpOp s fun a b => a.slt b
  | .LEINT, [] => cmpOp s fun a b => a.sle b
  | .GTINT, [] => cmpOp s fun a b => b.slt a
  | .GEINT, [] => cmpOp s fun a b => b.sle a
  | .ULTINT, [] => cmpOp s fun a b => a.ult b
  | .UGEINT, [] => cmpOp s fun a b => b.ule a
  | .OFFSETINT, [n] => match s.accu with
      | .int a => .next { (s.adv 2) with accu := .int (untag (tag64 a + ((BitVec.ofInt 32 n <<< 1).signExtend 64))) }
      | _ => .wrong
  | .OFFSETREF, [n] => opt (field? s.heap s.accu 0) fun
      | .int a => opt (setField? s.heap s.accu 0 (.int (untag (tag64 a + ((BitVec.ofInt 32 n <<< 1).signExtend 64)))))
          fun h => .next { (s.adv 2) with heap := h, accu := .unit }
      | _ => .wrong
  | .ISINT, [] => match s.accu with
      | .raw _ => .wrong
      | v => .next { (s.adv 1) with accu := Val.ofBool v.isInt }
  | .BEQ, [n, o] | .BNEQ, [n, o] =>
      match s.accu with
      | .int _ => brOp s n o (if i.op = .BEQ then fun a b => a == b else fun a b => a != b)
      | .ptr .. | .atom _ =>
        if i.op = .BEQ then .next (s.adv 3)
        else opt (target pc 1 o) fun t => .next { s with pc := t }
      | _ => .wrong
  | .BLTINT, [n, o] => brOp s n o fun a b => a.slt b
  | .BLEINT, [n, o] => brOp s n o fun a b => a.sle b
  | .BGTINT, [n, o] => brOp s n o fun a b => b.slt a
  | .BGEINT, [n, o] => brOp s n o fun a b => b.sle a
  | .BULTINT, [n, o] => brOp s n o fun a b => a.ult b
  | .BUGEINT, [n, o] => brOp s n o fun a b => b.ule a
  -- Machine control: `STOP` returns to `caml_main`, which exits 0
  | .STOP, [] => .halt 0 s.world
  | _, _ => .unsupported

/-- One step at `s.pc`. -/
def step : Res :=
  match decodeAt P.code s.pc with
  | some i => stepI P s i
  | none => .wrong

end

/-! ## The relation and the behaviours -/

/-- The graph of `step`. -/
inductive Step (P : Prog) : St → St → Prop where
  | mk {s s' : St} : step P s = .next s' → Step P s s'

/-- Exactly `n` steps. -/
inductive StepsN (P : Prog) : Nat → St → St → Prop where
  | zero (s : St) : StepsN P 0 s s
  | succ {n : Nat} {a b c : St} : Step P a b → StepsN P n b c → StepsN P (n + 1) a c

/-- Reachable from the initial state. -/
def Reach (P : Prog) (s : St) : Prop := ∃ n, StepsN P n P.init s

/-- Bytes to the console string, one `Char` per byte (`Vsa.Machine.output`'s
convention for the HTIF console). -/
def bytesToString (b : List UInt8) : String := String.ofList (b.map fun x => Char.ofNat x.toNat)

/-- **`BcSem`**: the program halts with exit code `e` having printed `out`. -/
def BcHalts (P : Prog) (out : String) (e : Nat) : Prop :=
  ∃ s w, Reach P s ∧ step P s = .halt e w ∧ bytesToString w.console = out

/-- `BcSem` with the file system observed: halts with exit `e`, console
`out` and final files `fs`. -/
def BcRun (P : Prog) (out : String) (e : Nat) (fs : List (String × List UInt8)) : Prop :=
  ∃ s w, Reach P s ∧ step P s = .halt e w ∧ bytesToString w.console = out ∧ w.files = fs

theorem BcRun.halts {P : Prog} {out : String} {e : Nat} {fs : List (String × List UInt8)}
    (h : BcRun P out e fs) : BcHalts P out e := by
  obtain ⟨s, w, hr, hs, ho, -⟩ := h
  exact ⟨s, w, hr, hs, ho⟩

theorem BcHalts.run {P : Prog} {out : String} {e : Nat} (h : BcHalts P out e) :
    ∃ fs, BcRun P out e fs := by
  obtain ⟨s, w, hr, hs, ho⟩ := h
  exact ⟨w.files, s, w, hr, hs, ho, rfl⟩

/-- The program runs forever. -/
def BcDiverges (P : Prog) : Prop := ∀ n, ∃ s, StepsN P n P.init s

/-- The program never reaches an unsupported or wrong state: it is inside
the fragment, and its behaviour does not depend on the abstraction. -/
def Good (P : Prog) : Prop :=
  ∀ s, Reach P s → step P s ≠ .unsupported ∧ step P s ≠ .wrong

/-! ## Determinism and the trichotomy -/

theorem Step.det {P : Prog} {a b b' : St} (h : Step P a b) (h' : Step P a b') : b = b' := by
  cases h with | mk e => cases h' with | mk e' => rw [e] at e'; cases e'; rfl

/-! ### `BcSem` as a run kernel (`OCaml/Run/Kernel.lean`)

The run laws below are corollaries of the kernel; never re-prove them by
induction on `StepsN` (discipline rule O5). -/

/-- `BcSem` of `P` as a kernel; the outcome is the whole non-`next` result. -/
def bcK (P : Prog) (s : St) : Except Res St :=
  match step P s with
  | .next s' => .ok s'
  | r => .error r

theorem bcK_graph (P : Prog) : Run.Graph (bcK P) (Step P) :=
  ⟨fun {a _} => ⟨fun ⟨h⟩ => by simp [bcK, h], fun h => ⟨by unfold bcK at h; split at h <;> simp_all⟩⟩⟩

theorem bcK_error {P : Prog} {s : St} {o : Res} (h : bcK P s = .error o) : step P s = o := by
  unfold bcK at h; split at h <;> simp_all

theorem bcK_halt {P : Prog} {s : St} {e : Nat} {w : World} (h : step P s = .halt e w) :
    bcK P s = .error (.halt e w) := by simp [bcK, h]

theorem bcK_not_next {P : Prog} {s s' : St} : bcK P s ≠ .error (.next s') := by
  unfold bcK; split <;> simp_all

theorem stepsN_pres (P : Prog) : Run.ConsPres (Step P) (StepsN P) :=
  ⟨.zero, .succ, fun h => by cases h with | zero => exact .inl ⟨rfl, rfl⟩ | succ s r => exact .inr ⟨_, _, rfl, s, r⟩⟩

theorem stepsN_iff {P : Prog} {n : Nat} {a b : St} : StepsN P n a b ↔ Run.iter (bcK P) n a = .ok b :=
  (stepsN_pres P).iff (bcK_graph P)

theorem bcDiverges_iff {P : Prog} : BcDiverges P ↔ Run.DivK (bcK P) P.init :=
  forall_congr' fun _ => exists_congr fun _ => stepsN_iff

theorem bcHalts_iff {P : Prog} {out : String} {e : Nat} :
    BcHalts P out e ↔ ∃ w, Run.HaltsK (bcK P) P.init (.halt e w) ∧ bytesToString w.console = out :=
  ⟨fun ⟨s, w, ⟨n, hn⟩, hst, ho⟩ => ⟨w, ⟨s, ⟨n, stepsN_iff.1 hn⟩, bcK_halt hst⟩, ho⟩,
   fun ⟨w, ⟨s, ⟨n, hn⟩, hs⟩, ho⟩ => ⟨s, w, ⟨n, stepsN_iff.2 hn⟩, bcK_error hs, ho⟩⟩

/-- `Good` excludes the bad outcomes of the `BcSem` kernel. -/
theorem Good.halt {P : Prog} (hg : Good P) {o : Res} (h : Run.HaltsK (bcK P) P.init o) :
    ∃ e w, o = .halt e w := by
  obtain ⟨s, ⟨n, hn⟩, hs⟩ := h
  obtain ⟨hu, hw⟩ := hg s ⟨n, stepsN_iff.2 hn⟩
  have hst := bcK_error hs
  cases o with
  | next s' => exact (bcK_not_next hs).elim
  | halt e w => exact ⟨e, w, rfl⟩
  | unsupported => exact (hu hst).elim
  | wrong => exact (hw hst).elim

theorem StepsN.det {P : Prog} {n : Nat} {a b b' : St}
    (h : StepsN P n a b) (h' : StepsN P n a b') : b = b' := by
  have := stepsN_iff.1 h; rw [stepsN_iff.1 h'] at this; cases this; rfl

theorem StepsN.snoc {P : Prog} {n : Nat} {a b c : St}
    (h : StepsN P n a b) (s : Step P b c) : StepsN P (n + 1) a c :=
  stepsN_iff.2 (by rw [Run.iter_succ', stepsN_iff.1 h]; exact (bcK_graph P).iff.1 s)

/-- A state of `n` steps that does not step has no successor at `n + 1`. -/
theorem StepsN.stop {P : Prog} {n : Nat} {a b c : St} (h : StepsN P n a b)
    (hs : ∀ x, ¬ step P b = .next x) (h' : StepsN P (n + 1) a c) : False :=
  Run.iter_stop (stepsN_iff.1 h) (fun x hx => by obtain ⟨h⟩ := (bcK_graph P).iff.2 hx; exact hs x h) c
    (stepsN_iff.1 h')

/-- Every run of a `Good` program halts or diverges. -/
theorem halts_or_diverges (P : Prog) (hg : Good P) :
    (∃ out e, BcHalts P out e) ∨ BcDiverges P := by
  rw [bcDiverges_iff]
  refine (Run.halts_or_div (f := bcK P) P.init).imp (fun ⟨o, h⟩ => ?_) id
  obtain ⟨e, w, rfl⟩ := hg.halt h
  exact ⟨_, e, bcHalts_iff.2 ⟨w, h, rfl⟩⟩

/-- A halting program does not diverge. -/
theorem BcHalts.not_diverges {P : Prog} {out : String} {e : Nat}
    (h : BcHalts P out e) : ¬ BcDiverges P := fun hd => by
  obtain ⟨w, h, -⟩ := bcHalts_iff.1 h; exact h.not_div (bcDiverges_iff.1 hd)

/-- Every run has all its prefixes. -/
theorem StepsN.prefix {P : Prog} {m : Nat} :
    ∀ {k : Nat} {a c : St}, StepsN P (m + k) a c → ∃ b, StepsN P m a b := fun h =>
  let ⟨b, hb⟩ := Run.iter_prefix (stepsN_iff.1 h); ⟨b, stepsN_iff.2 hb⟩

/-- `BcSem` is deterministic. -/
theorem BcHalts.det {P : Prog} {out out' : String} {e e' : Nat}
    (h : BcHalts P out e) (h' : BcHalts P out' e') : out = out' ∧ e = e' := by
  obtain ⟨w, hk, rfl⟩ := bcHalts_iff.1 h; obtain ⟨w', hk', rfl⟩ := bcHalts_iff.1 h'
  cases hk.unique hk'; exact ⟨rfl, rfl⟩

end OCaml.Bytecode
