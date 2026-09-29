/-!
# Lambda: the intermediate language `OCamlSem` is written on (syntax)

Transcribed from OCaml 4.14.4's `lambda/lambda.mli` (constructors in the
same order, scoped locations and debug events dropped). This is the
language between the two halves of `ocamlc`: `Translcore`/`Matching`
produce it from the typed tree, `Bytegen`/`Emitcode` consume it. Layer C's
`OCamlSem` (to be written, PLAN.md §Layer C) is a big-step semantics on this
syntax (first cut) and later on the typed tree.

Nested pairs and options are flattened into parallel lists (a `default`
list has at most one element) to keep the inductive non-nested beyond `List`.

Primitives are the ones `Bytegen.comp_primitive` compiles; the rest of
`Lambda.primitive` is `Pother` by name until a fragment needs it.
-/

namespace OCaml.Source

abbrev Ident := String

inductive Constant where
  | int (n : Int) | char (c : Char) | string (s : String) | float (lit : String)
  | int32 (n : Int) | int64 (n : Int) | nativeint (n : Int)
  deriving Repr, DecidableEq

inductive StructuredConstant where
  | const (c : Constant)
  | block (tag : Nat) (fields : List StructuredConstant)
  | floatArray (lits : List String)
  | immString (s : String)
  deriving Repr

inductive Primitive where
  | Pidentity | Pignore | Pgetglobal (id : Ident) | Psetglobal (id : Ident)
  | Pmakeblock (tag : Nat) (mutable : Bool) | Pfield (n : Nat) | Psetfield (n : Nat)
  | Pccall (name : String) (arity : Nat)
  | Praise | Psequand | Psequor | Pnot
  | Pnegint | Paddint | Psubint | Pmulint | Pdivint | Pmodint
  | Pandint | Porint | Pxorint | Plslint | Plsrint | Pasrint
  | Pintcomp (op : String) | Poffsetint (n : Int) | Poffsetref (n : Int)
  | Pisint | Pmakearray | Parraylength | Parrayrefu | Parraysetu | Parrayrefs | Parraysets
  | Pstringlength | Pstringrefu | Pstringrefs | Pbyteslength | Pbytesrefu | Pbytessetu
  | Pother (name : String)
  deriving Repr, DecidableEq

inductive Lambda where
  | Lvar (x : Ident)
  | Lmutvar (x : Ident)
  | Lconst (c : StructuredConstant)
  | Lapply (f : Lambda) (args : List Lambda)
  | Lfunction (params : List Ident) (body : Lambda)
  | Llet (x : Ident) (e body : Lambda)
  | Lmutlet (x : Ident) (e body : Lambda)
  | Lletrec (names : List Ident) (defs : List Lambda) (body : Lambda)
  | Lprim (p : Primitive) (args : List Lambda)
  | Lswitch (e : Lambda) (constKeys : List Nat) (constArms : List Lambda)
      (blockKeys : List Nat) (blockArms : List Lambda) (default : List Lambda)
  | Lstringswitch (e : Lambda) (keys : List String) (arms : List Lambda) (default : List Lambda)
  | Lstaticraise (lbl : Nat) (args : List Lambda)
  | Lstaticcatch (body : Lambda) (lbl : Nat) (params : List Ident) (handler : Lambda)
  | Ltrywith (body : Lambda) (x : Ident) (handler : Lambda)
  | Lifthenelse (c t e : Lambda)
  | Lsequence (a b : Lambda)
  | Lwhile (c body : Lambda)
  | Lfor (x : Ident) (lo hi : Lambda) (up : Bool) (body : Lambda)
  | Lassign (x : Ident) (e : Lambda)
  | Lsend (kind : String) (meth obj : Lambda) (args : List Lambda)
  | Lifused (x : Ident) (e : Lambda)
  deriving Repr

/-- A compilation unit after `Translmod`: its Lambda code. A whole program
is the linked units in order (what `Bytelink` lays out). -/
structure Unit where
  name : String
  code : Lambda

abbrev Program := List Unit

end OCaml.Source
