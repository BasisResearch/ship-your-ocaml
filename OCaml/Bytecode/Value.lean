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
  /-- Allocated byte payload: `none` has not been initialized and cannot be read. -/
  | partialBytes (b : List (Option UInt8))
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
  | .bytes _ | .partialBytes _ => stringTag
  | .double _ => doubleTag
  | .doubleArray _ => doubleArrayTag
  | _ => customTag

/-- `Wosize_val` (payload words; strings padded as in `caml_alloc_string`). -/
def wosize : Obj → Nat
  | .block _ fs => fs.length
  | .bytes b => b.length / 8 + 1
  | .partialBytes b => b.length / 8 + 1
  | .double _ => 1
  | .doubleArray ds => ds.length
  | .int64 _ | .nativeint _ => 2   -- ops pointer + payload
  | .int32 _ => 2
  | .channel _ => 2

end Obj

/-- The abstract heap: an allocation counter and the blocks allocated so
far. Allocation always takes `next`, so locations are never reused. -/
instance : Coe (List Obj) (Array Obj) := ⟨List.toArray⟩


structure Heap where
  storage : Array Obj
  deriving DecidableEq, Repr, Inhabited

namespace Heap

/-- List view for existing symbolic specifications; execution uses the array. -/
def objs (h : Heap) : List Obj := h.storage.toList

@[simp] theorem storage_list_eq (h : Heap) : h.storage.toList = h.objs := rfl

/-- Keep array sizes in the existing symbolic heap interface. -/
@[simp] theorem storage_size_eq (h : Heap) : h.storage.size = h.objs.length := rfl

def size (h : Heap) : Nat := h.storage.size

def get? (h : Heap) (l : Nat) : Option Obj := h.storage.toList[l]?

def getArray? (h : Heap) (l : Nat) : Option Obj := h.storage[l]?

/-- The compiled read uses Array's constant-time operation; the specification
retains the existing list view and its symbolic allocation laws. -/
@[csimp] theorem get?_eq_getArray : @get? = @getArray? := by
  funext h l
  exact Array.getElem?_toList

/-- Allocate `o`, returning its location. -/
def alloc (h : Heap) (o : Obj) : Heap × Nat :=
  let n := h.storage.size
  (⟨h.storage.push o⟩, n)

/-- Replace block `l` (mutation). -/
def set (h : Heap) (l : Nat) (o : Obj) : Heap := ⟨h.storage.setIfInBounds l o⟩

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

/-- A SWITCH selector whose tag the machine reads from a header the model
does not represent: an atom (the atom table's header) or an interior/infix
pointer (the word before it). Compiled code never switches on either. -/
def Val.switchExotic : Val → Bool
  | .atom _ => true
  | .ptr _ (_ + 1) => true
  | _ => false

/-- Write field `i` (`caml_modify` / `Field(v,i) = x`). -/
def setField? (h : Heap) : Val → Nat → Val → Option Heap
  | .ptr l k, i, x => match h.get? l with
    | some (.block t fs) =>
        if k + i < fs.length then some (h.set l (.block t (fs.set (k + i) x))) else none
    | _ => none
  | _, _, _ => none

/-- A boxed double, as used by the float-field arms in `interp.c`. -/
def doubleOf? (h : Heap) : Val → Option (BitVec 64)
  | .ptr l 0 => match h.get? l with
    | some (.double d) => some d
    | _ => none
  | _ => none

/-- Unboxed float-field access (`Double_flat_field`). -/
def floatField? (h : Heap) : Val → Nat → Option (BitVec 64)
  | .ptr l 0, i => match h.get? l with
    | some (.doubleArray ds) => ds[i]?
    | _ => none
  | _, _ => none

def setFloatField? (h : Heap) : Val → Nat → BitVec 64 → Option Heap
  | .ptr l 0, i, d => match h.get? l with
    | some (.doubleArray ds) =>
        if i < ds.length then some (h.set l (.doubleArray (ds.set i d))) else none
    | _ => none
  | _, _, _ => none

/-- Bytes with explicit initialization state. Length and writes do not read
uninitialized payload; observations require `some` at every observed cell. -/
def byteCells? (h : Heap) : Val → Option (List (Option UInt8))
  | .ptr l 0 => match h.get? l with
    | some (.bytes b) => some (b.map some)
    | some (.partialBytes b) => some b
    | _ => none
  | _ => none

/-- Normalize fully initialized buffers back to ordinary strings. -/
def Obj.ofByteCells (b : List (Option UInt8)) : Obj :=
  match b.mapM id with
  | some bs => .bytes bs
  | none => .partialBytes b

/-- Read only the requested range, rejecting any uninitialized cell. -/
def byteSlice? (h : Heap) (v : Val) (off len : Nat) : Option (List UInt8) := do
  match v with
  | .ptr l 0 => match ← h.get? l with
    | .bytes b => if off + len ≤ b.length then some ((b.drop off).take len) else none
    | .partialBytes b => if off + len ≤ b.length then ((b.drop off).take len).mapM id else none
    | _ => none
  | _ => none

/-- Writes preserve the initialization state of untouched bytes. -/
def writeByteCells? (h : Heap) (v : Val) (off : Nat)
    (src : List (Option UInt8)) : Option Heap := do
  let cells ← byteCells? h v
  match v with
  | .ptr l 0 =>
    if off + src.length ≤ cells.length then
      some (h.set l (Obj.ofByteCells (cells.take off ++ src ++ cells.drop (off + src.length))))
    else none
  | _ => none

/-- `Wosize_val`, including static atoms and infix pointers. -/
def size? (h : Heap) : Val → Option Nat
  | .atom _ => some 0
  | .ptr l k => (h.get? l).map fun o => o.wosize - k
  | _ => none

end OCaml.Bytecode
