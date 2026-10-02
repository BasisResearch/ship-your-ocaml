import OCaml.Bytecode.Value

/-! Data operations transcribed from runtime/{array,str,compare,callback}.c.
Fuel bounds only traversal of possibly cyclic values; exhaustion leaves the
operation outside the supported fragment. -/
namespace OCaml.Bytecode

/-- `runtime/callback.c` hashes and compares the first-NUL-terminated C name. -/
def namedValueKey (bytes : List UInt8) : String :=
  String.ofList ((bytes.takeWhile (· != 0)).map fun b => Char.ofNat b.toNat)

/-- `caml_register_named_value` updates an existing root slot, or allocates a
new one when no key matches. Table order is abstract; keys remain unique from
an initially unique table. Replaced values cease to be named GC roots. -/
def registerNamedValue (name : String) (v : Val) : List (String × Val) → List (String × Val)
  | [] => [(name, v)]
  | (key, old) :: rest =>
      if key == name then (key, v) :: rest else (key, old) :: registerNamedValue name v rest

/-- Byte lexicographic order (`memcmp`, followed by length). -/
def compareBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a < b then -1 else if b < a then 1 else compareBytes as bs

/-- `compare_val` for integers, strings and ordinary structured blocks.
Unsupported custom blocks and functional values stay explicit. -/
def compareVal (h : Heap) (total : Bool) : Nat → Val → Val → Option Int
  | 0, _, _ => none
  | fuel + 1, a, b => do
    if total && a == b then return 0
    match a, b with
    | .int x, .int y => return if x.toInt < y.toInt then -1 else if y.toInt < x.toInt then 1 else 0
    | _, _ =>
      let ta ← if a.isInt then some 0 else tag? h a
      let tb ← if b.isInt then some 0 else tag? h b
      if ta = forwardTag then
        compareVal h total fuel (← field? h a 0) b
      else if tb = forwardTag then
        compareVal h total fuel a (← field? h b 0)
      else if a.isInt then pure (-1)
      else if b.isInt then pure 1
      else if ta ≠ tb then pure (if ta < tb then -1 else 1)
      else if ta = stringTag then
        match a, b with
        | .ptr l 0, .ptr m 0 => match h.get? l, h.get? m with
          | some (.bytes x), some (.bytes y) => pure (compareBytes x y)
          | _, _ => none
        | _, _ => none
      else if ta = objectTag then
        compareVal h total fuel (← field? h a 1) (← field? h b 1)
      else if ta ≥ closureTag then none
      else
        let na ← size? h a
        let nb ← size? h b
        if na ≠ nb then return if na < nb then -1 else 1
        (List.range na).foldlM (fun r i =>
          if r ≠ 0 then pure r else do
            compareVal h total fuel (← field? h a i) (← field? h b i)) 0

/-- Positional digits for the integer conversions of `caml_format_int`. -/
def radixDigits (base : Nat) (upper : Bool) (n : Nat) : String :=
  let rec go : Nat → Nat → List Char
    | 0, _ => []
    | fuel + 1, n =>
      let d := n % base
      let c := Char.ofNat (if d < 10 then 48 + d else (if upper then 65 else 97) + d - 10)
      if n < base then [c] else c :: go fuel (n / base)
  String.ofList (go 64 n).reverse

/-- The integer printf conversion domain used by OCaml's format engine.
Flags, width, precision and the ignored l/n/L suffix follow `ints.c`
`parse_format` and C integer printf. Noninteger conversions stay unsupported. -/
def formatInteger (fmt : List UInt8) (n : BitVec 63) : Option (List UInt8) := do
  let cs := fmt.map fun b => Char.ofNat b.toNat
  if cs.head? != some '%' || cs.length < 2 || cs.length + 2 ≥ 32 then none else do
  let conv ← cs.getLast?
  if !(['d', 'i', 'u', 'x', 'X', 'o'].contains conv) then none else do
  let mid := (cs.drop 1).take (cs.length - 2)
  let flags := mid.takeWhile fun c => ['-', '+', ' ', '#', '0'].contains c
  let rest := mid.drop flags.length
  let widthCs := rest.takeWhile Char.isDigit
  let decimalChars := fun (ds : List Char) => ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
  let width := decimalChars widthCs
  let rest := rest.drop widthCs.length
  let (precision, rest) := if rest.head? == some '.' then
      let ds := (rest.drop 1).takeWhile Char.isDigit
      (some (decimalChars ds), rest.drop (ds.length + 1))
    else (none, rest)
  if rest != [] && rest != ['l'] && rest != ['n'] && rest != ['L'] then none else do
  let signed := conv == 'd' || conv == 'i'
  let neg := signed && n.toInt < 0
  let magnitude := if signed then n.toInt.natAbs else n.toNat
  let base := if conv == 'o' then 8 else if conv == 'x' || conv == 'X' then 16 else 10
  let digits := if precision == some 0 && magnitude == 0 then [] else (radixDigits base (conv == 'X') magnitude).toList
  let digits := List.replicate (precision.getD 0 - digits.length) '0' ++ digits
  let sign := if neg then ['-'] else if signed && flags.contains '+' then ['+']
    else if signed && flags.contains ' ' then [' '] else []
  let radixPrefix := if flags.contains '#' then
      if base == 16 && magnitude != 0 then (if conv == 'X' then ['0', 'X'] else ['0', 'x'])
      else if base == 8 && digits.head? != some '0' then ['0'] else []
    else []
  let pad := width - sign.length - radixPrefix.length - digits.length
  let text := if flags.contains '-' then sign ++ radixPrefix ++ digits ++ List.replicate pad ' '
    else if flags.contains '0' && precision.isNone then sign ++ radixPrefix ++ List.replicate pad '0' ++ digits
    else List.replicate pad ' ' ++ sign ++ radixPrefix ++ digits
  pure (text.map (·.toNat.toUInt8))

/-- `parse_intnat` for the 63-bit `int_of_string` domain. -/
def parseInteger (bs : List UInt8) : Option Val := do
  let cs := bs.map fun b => Char.ofNat b.toNat
  let neg := cs.head? == some '-'
  let cs := if neg || cs.head? == some '+' then cs.drop 1 else cs
  let (base, signed, cs) := match cs with
    | '0' :: c :: rest =>
      if c == 'x' || c == 'X' then (16, false, rest)
      else if c == 'o' || c == 'O' then (8, false, rest)
      else if c == 'b' || c == 'B' then (2, false, rest)
      else if c == 'u' || c == 'U' then (10, false, rest)
      else (10, true, cs)
    | _ => (10, true, cs)
  if cs.isEmpty || cs.head? == some '_' then none else do
  let n ← cs.foldlM (fun (n : Nat) c => do
    if c == '_' then return n
    let d := if c ≥ '0' && c ≤ '9' then c.toNat - 48
      else if c ≥ 'a' && c ≤ 'f' then c.toNat - 97 + 10
      else if c ≥ 'A' && c ≤ 'F' then c.toNat - 65 + 10 else 16
    if d ≥ base || n * base + d ≥ 2^64 then none else pure (n * base + d)) 0
  if (if signed then (if neg then n > 2^62 else n ≥ 2^62) else n ≥ 2^63) then none
  else pure (Val.ofInt (if neg then -(n : Int) else n))

/-- MurmurHash mixing from runtime/hash.c (32-bit wraparound). -/
def hashMix (h d : BitVec 32) : BitVec 32 :=
  let d := d * 0xcc9e2d51
  let d := d.rotateLeft 15 * 0x1b873593
  let h := (h ^^^ d).rotateLeft 13
  h * 5 + 0xe6546b64

def hashFinish (h : BitVec 32) : BitVec 32 :=
  let h := (h ^^^ (h >>> 16)) * 0x85ebca6b
  let h := (h ^^^ (h >>> 13)) * 0xc2b2ae35
  (h ^^^ (h >>> 16)) &&& 0x3fffffff

/-- caml_hash_mix_intnat on LP64 (signed high-word folding). -/
def hashIntnat (h : BitVec 32) (v : BitVec 64) : BitVec 32 :=
  hashMix h ((v.sshiftRight 32 ^^^ v.sshiftRight 63 ^^^ v).setWidth 32)

/-- String mixing from hash.c, including the final length xor. -/
def hashString (seed : BitVec 32) (bs : List UInt8) : BitVec 32 :=
  let blocks := (List.range ((bs.length + 3) / 4)).foldl (fun h i =>
    let bytes := (bs.drop (4 * i)).take 4
    let word := bytes.reverse.foldl (fun n b => 256 * n + b.toNat) 0
    hashMix h (BitVec.ofNat 32 word)) seed
  blocks ^^^ BitVec.ofNat 32 bs.length

def hashDouble (seed : BitVec 32) (d : BitVec 64) : BitVec 32 :=
  let hi := (d >>> 32).setWidth 32
  let lo := d.setWidth 32
  let (hi, lo) := if hi &&& 0x7ff00000 = 0x7ff00000 ∧ (lo ||| (hi &&& 0xfffff)) ≠ 0 then
      (0x7ff00000, 1)
    else if hi = 0x80000000 ∧ lo = 0 then (0, lo) else (hi, lo)
  hashMix (hashMix seed lo) hi

/-- Forward links are bounded exactly as hash.c's MAX_FORWARD_DEREFERENCE. -/
private def hashForward (h : Heap) : Nat → Val → Option Val
  | 0, _ => none
  | fuel + 1, v => match v with
    | .ptr l 0 => match h.get? l with
      | some (.block 250 (x :: _)) => hashForward h fuel x
      | _ => some v
    | _ => some v

/-- Bounded breadth-first structural hash. Code pointers/closures remain
outside the address-independent domain; ordinary blocks may contain cycles. -/
def hashData (h : Heap) (count limit : Int) (seed : BitVec 32) (value : Val) : Option (BitVec 32) :=
  let capacity := if limit < 0 ∨ limit > 256 then 256 else limit.toNat
  let rec go : Nat → Nat → BitVec 32 → List Val → Nat → Option (BitVec 32)
    | 0, _, _, _, _ => none
    | fuel + 1, num, acc, queue, written => do
      if num = 0 then some (hashFinish acc) else
      match queue with
      | [] => some (hashFinish acc)
      | v :: queue =>
        match hashForward h 1001 v with
        | none => go fuel num acc queue written
        | some v =>
          let again := fun acc => go fuel (num - 1) acc queue written
          let block := fun tag (fields : List Val) =>
            let added := fields.take (capacity - written)
            go fuel num (hashMix acc (BitVec.ofNat 32 (fields.length * 1024 + tag)))
              (queue ++ added) (written + added.length)
          match v with
          | .int n => again (hashIntnat acc ((n.signExtend 64 <<< 1) ||| 1))
          | .atom t => block t []
          | .ptr l 0 => match ← h.get? l with
            | .bytes b => again (hashString acc b)
            | .partialBytes b => do let b ← b.mapM id; again (hashString acc b)
            | .double d => again (hashDouble acc d)
            | .doubleArray ds =>
              let used := ds.take num
              go fuel (num - used.length) (used.foldl hashDouble acc) queue written
            | .int32 n => again (hashMix acc n)
            | .int64 n => again (hashMix acc ((n ^^^ (n >>> 32)).setWidth 32))
            | .nativeint n => again (hashIntnat acc n)
            | .channel _ => none
            | .block 251 _ => go fuel num acc queue written
            | .block 248 (_ :: .int oid :: _) =>
              again (hashIntnat acc ((oid.signExtend 64 <<< 1) ||| 1))
            | .block t fs => if t ≥ 247 then none else block t fs
          | _ => none
  go 258 count.toNat seed [value] 1

/-- IEEE binary64 payload as a nonnegative rational, before decimal printf.
`none` denotes infinity or NaN. -/
def doubleRatio (d : BitVec 64) : Option (Nat × Nat) :=
  let exp : Nat := (d.toNat / 2^52) % 2048
  let frac := d.toNat % 2^52
  if exp = 2047 then none else
  let mant := if exp = 0 then frac else frac + 2^52
  let shift : Int := ((if exp = 0 then 1 else exp) : Nat) - (1075 : Int)
  if shift < 0 then some (mant, 2^shift.natAbs) else some (mant * 2^shift.toNat, 1)

/-- Round a nonnegative rational to nearest integer, ties to even. -/
def roundRatio (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2*r > d || (2*r == d && q % 2 == 1) then q + 1 else q

/-- Round after scaling by a signed decimal exponent. -/
def roundDecimal (n d : Nat) (shift : Int) : Nat :=
  if shift ≥ 0 then roundRatio (n * 10^shift.toNat) d
  else roundRatio n (d * 10^shift.natAbs)

def fixedDecimal (n places : Nat) : String :=
  let digits := (toString n).toList
  if places = 0 then String.ofList digits else
  let digits := List.replicate (places + 1 - digits.length) '0' ++ digits
  String.ofList (digits.take (digits.length - places)) ++ "." ++
    String.ofList (digits.drop (digits.length - places))

def trimDecimal (s : String) : String :=
  if !s.contains '.' then s else
  let cs := s.toList.reverse.dropWhile (· == '0')
  String.ofList ((if cs.head? == some '.' then cs.drop 1 else cs).reverse)

/-- Finite binary64 `snprintf` decimal conversions, computed with exact
integer arithmetic. The accepted format subset is %.Ng, %.Ne, %.Nf and
uppercase equivalents, with default precision 6. Other formats remain open. -/
def formatDouble (fmt : List UInt8) (bits : BitVec 64) : Option (List UInt8) := do
  let cs := fmt.map fun b => Char.ofNat b.toNat
  if cs.head? != some '%' || cs.length < 2 then none else do
  let conv ← cs.getLast?
  if !("gGeEfF".contains conv) then none else do
  let mid := (cs.drop 1).take (cs.length - 2)
  let prec ← if mid.isEmpty then some 6 else
    if mid.head? == some '.' then (String.ofList (mid.drop 1)).toNat? else none
  -- The C printer's huge-output resource domain is left outside this model.
  if prec > 1000 then none else do
  let neg := bits.toNat / 2^63 != 0
  let sign := if neg then "-" else ""
  let upper := "GEF".contains conv
  let text := match doubleRatio bits with
    | none => if bits.toNat % 2^52 = 0 then (if upper then "INF" else "inf")
        else (if upper then "NAN" else "nan")
    | some (n, d) => Id.run do
      let scientific := fun (digits : Nat) (places : Nat) (exp : Int) =>
        fixedDecimal digits places ++ (if upper then "E" else "e") ++
        (if exp < 0 then "-" else "+") ++
        (if exp.natAbs < 10 then "0" else "") ++ toString exp.natAbs
      if conv == 'f' || conv == 'F' then
        return fixedDecimal (roundDecimal n d prec) prec
      let e : Int := if n = 0 then 0 else if n ≥ d then
          ((List.range 310).takeWhile fun k => n ≥ d * 10^k).length - (1 : Int)
        else -((List.range 325).takeWhile fun k => n * 10^k < d).length
      let isG := conv == 'g' || conv == 'G'
      let p := if isG then max 1 prec else prec + 1
      let digits := roundDecimal n d ((p : Int) - 1 - e)
      let (digits, e) := if digits ≥ 10^p then (digits / 10, e + 1) else (digits, e)
      if !isG then return scientific digits prec e
      if e < -4 || e ≥ p then
        return trimDecimal (fixedDecimal digits (p - 1)) ++ (if upper then "E" else "e") ++
          (if e < 0 then "-" else "+") ++ (if e.natAbs < 10 then "0" else "") ++ toString e.natAbs
      return trimDecimal (fixedDecimal digits ((p : Int) - 1 - e).toNat)
  pure ((sign ++ text).toList.map (·.toNat.toUInt8))

/-- Array payload snapshots; atoms represent zero-sized arrays. -/
def arrayObj? (h : Heap) : Val → Option Obj
  | .atom 0 => some (.block 0 [])
  | .ptr l 0 => match h.get? l with
    | some (.block 0 fs) => some (.block 0 fs)
    | some (.doubleArray ds) => some (.doubleArray ds)
    | _ => none
  | _ => none

def arraySlice (o : Obj) (off len : Nat) : Option Obj :=
  if off + len > o.wosize then none else match o with
  | .block 0 fs => some (.block 0 ((fs.drop off).take len))
  | .doubleArray ds => some (.doubleArray ((ds.drop off).take len))
  | _ => none

def arrayAppend : Obj → Obj → Option Obj
  | .block 0 [], b => some b
  | a, .block 0 [] => some a
  | .block 0 a, .block 0 b => some (.block 0 (a ++ b))
  | .doubleArray a, .doubleArray b => some (.doubleArray (a ++ b))
  | _, _ => none

/-- Splice a snapshotted payload, giving memmove semantics for overlapping arrays. -/
def arraySplice (dst : Obj) (off : Nat) (src : Obj) : Option Obj := do
  let before ← arraySlice dst 0 off
  let after ← arraySlice dst (off + src.wosize) (dst.wosize - off - src.wosize)
  arrayAppend (← arrayAppend before src) after

end OCaml.Bytecode
