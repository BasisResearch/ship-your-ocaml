/-!
# ZINC values and the abstract heap

`BcSem` works over an ABSTRACT heap: blocks are named by locations
(`Nat`), never by addresses, and are never moved or freed. This is the
point of the design (README §GC strategy): the copying minor GC and the
compactor move blocks, so the representation predicate
(`OCaml/Vm/Repr.lean`) relates abstract locations to machine addresses
through a map `φ` that each collection is allowed to change, and `BcSem`
itself never sees a collection.

Values mirror `runtime/caml/mlvalues.h`:

* `int n` — a tagged integer `(n << 1) | 1`, `n` a 63-bit two's-complement
  integer (arithmetic wraps: the runtime is built with `-fwrapv`);
* `ptr l k` — a pointer to field `k` of block `l`; `k = 0` for ordinary
  pointers, `k > 0` for the infix pointers `CLOSUREREC` creates into a
  mutually recursive closure block (`Infix_tag` headers at `k - 1`);
* `code pc` — a code pointer (closure code fields, return addresses,
  trap-frame handlers): the index of an instruction in the code array;
* `atom t` — `Atom(t)`, the statically allocated zero-size block of tag `t`
  (`caml_atom_table`);
* `raw w` — a word that is not a value but lives in a block: the infix
  headers `Make_header(3 i, Infix_tag, _)` inside a `CLOSUREREC` block.
-/

namespace OCaml.Bytecode

/-- A ZINC machine word. -/
inductive Val where
  | int (n : BitVec 63)
  | ptr (l : Nat) (k : Nat)
  | code (pc : Nat)
  | atom (tag : Nat)
  | raw (w : BitVec 64)
  deriving DecidableEq, Repr, Inhabited

namespace Val

/-- `Val_long`. -/
def ofInt (n : Int) : Val := .int (BitVec.ofInt 63 n)
/-- `Val_unit` = `Val_false` = `Val_int(0)`. -/
def unit : Val := .int 0
/-- `Val_true`. -/
def true_ : Val := .int 1
def ofBool (b : Bool) : Val := if b then .int 1 else .int 0

/-- `Is_long`. -/
def isInt : Val → Bool
  | .int _ => true
  | _ => false

end Val

/-- Tags (`runtime/caml/mlvalues.h`). -/
def closureTag : Nat := 247
def objectTag : Nat := 248
def infixTag : Nat := 249
def forwardTag : Nat := 250
def noScanTag : Nat := 251
def stringTag : Nat := 252
def doubleTag : Nat := 253
def doubleArrayTag : Nat := 254
def customTag : Nat := 255

/-- A heap block. Structured blocks keep every word as a `Val` (including a
`CLOSUREREC` block's infix headers, as `Val.raw`); the no-scan blocks keep
their payload in its natural type. Custom blocks are listed by the
operations the runtime installs (`caml_int64_ops` `_j`, `caml_int32_ops`
`_i`, `caml_nativeint_ops` `_n`, channels `_chan`). -/
inductive Obj where
  | block (tag : Nat) (fields : List Val)
  | bytes (b : List UInt8)
  | double (d : BitVec 64)
  | doubleArray (ds : List (BitVec 64))
  | int64 (n : BitVec 64)
  | int32 (n : BitVec 32)
  | nativeint (n : BitVec 64)
  | channel (id : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Obj

/-- `Tag_val`. -/
def tag : Obj → Nat
  | .block t _ => t
  | .bytes _ => stringTag
  | .double _ => doubleTag
  | .doubleArray _ => doubleArrayTag
  | _ => customTag

/-- `Wosize_val` (payload words; strings padded as in `caml_alloc_string`). -/
def wosize : Obj → Nat
  | .block _ fs => fs.length
  | .bytes b => b.length / 8 + 1
  | .double _ => 1
  | .doubleArray ds => ds.length
  | .int64 _ | .nativeint _ => 2   -- ops pointer + payload
  | .int32 _ => 2
  | .channel _ => 2

end Obj

/-- The abstract heap: an allocation counter and the blocks allocated so
far. Allocation always takes `next`, so locations are never reused. -/
structure Heap where
  objs : List Obj
  deriving DecidableEq, Repr, Inhabited

namespace Heap

def get? (h : Heap) (l : Nat) : Option Obj := h.objs[l]?

/-- Allocate `o`, returning its location. -/
def alloc (h : Heap) (o : Obj) : Heap × Nat := (⟨h.objs ++ [o]⟩, h.objs.length)

/-- Replace block `l` (mutation). -/
def set (h : Heap) (l : Nat) (o : Obj) : Heap := ⟨h.objs.set l o⟩

/-- Words allocated so far (headers included): the no-GC budget measure. -/
def words (h : Heap) : Nat := h.objs.foldl (fun a o => a + o.wosize + 1) 0

end Heap

/-- Read field `i` of the block a value points to (`Field(v, i)`). -/
def field? (h : Heap) : Val → Nat → Option Val
  | .ptr l k, i => match h.get? l with
    | some (.block _ fs) => fs[k + i]?
    | _ => none
  | _, _ => none

/-- `Tag_val` of a pointer (`Infix_tag` for an infix pointer). -/
def tag? (h : Heap) : Val → Option Nat
  | .atom t => some t
  | .ptr l 0 => (h.get? l).map Obj.tag
  | .ptr _ _ => some infixTag
  | _ => none

/-- Write field `i` (`caml_modify` / `Field(v,i) = x`). -/
def setField? (h : Heap) : Val → Nat → Val → Option Heap
  | .ptr l k, i, x => match h.get? l with
    | some (.block t fs) =>
        if k + i < fs.length then some (h.set l (.block t (fs.set (k + i) x))) else none
    | _ => none
  | _, _, _ => none

end OCaml.Bytecode
