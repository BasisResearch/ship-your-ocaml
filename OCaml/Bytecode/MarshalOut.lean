import OCaml.Bytecode.Value

/-! Marshal output for ordinary data, transcribed from runtime/extern.c.
Code pointers, closures, channels and forwarding blocks are outside this
entry's domain. Sharing and cyclic ordinary blocks are preserved. -/
namespace OCaml.Bytecode

private def beBytes (n width : Nat) : List UInt8 :=
  ((List.range width).map fun i => (n / 256^i % 256).toUInt8).reverse

private def signedBytes (n : Int) (width : Nat) : List UInt8 :=
  beBytes (n % (256^width : Nat)).toNat width

private def marshalInt (n : Int) : List UInt8 :=
  if 0 ≤ n ∧ n < 64 then [(64 + n).toNat.toUInt8]
  else if -128 ≤ n ∧ n < 128 then 0 :: signedBytes n 1
  else if -32768 ≤ n ∧ n < 32768 then 1 :: signedBytes n 2
  else if -(2^30) ≤ n ∧ n < 2^30 then 2 :: signedBytes n 4
  else 3 :: signedBytes n 8

private def marshalHeader (tag size : Nat) : List UInt8 :=
  if tag < 16 ∧ size < 8 then [(128 + tag + size * 16).toUInt8]
  else if size * 1024 + tag < 2^32 then 8 :: beBytes (size * 1024 + tag) 4
  else 0x13 :: beBytes (size * 1024 + tag) 8

private def marshalString (b : List UInt8) : List UInt8 :=
  (if b.length < 32 then [(32 + b.length).toUInt8]
   else if b.length < 256 then [9, b.length.toUInt8]
   else if b.length < 2^32 then 10 :: beBytes b.length 4
   else 0x15 :: beBytes b.length 8) ++ b

private structure MarshalState where
  out : List UInt8 := []
  seen : List Nat := []
  size32 : Nat := 0
  size64 : Nat := 0

private def MarshalState.emit (s : MarshalState) (b : List UInt8) : MarshalState :=
  { s with out := b.reverse ++ s.out }

private def marshalRec (h : Heap) : Nat → Val → MarshalState → Option MarshalState
  | 0, _, _ => none
  | fuel + 1, v, st => do
    match v with
    | .int n => some (st.emit (marshalInt n.toInt))
    | .atom t => some (st.emit (marshalHeader t 0))
    | .ptr l 0 =>
      let o ← h.get? l
      if o.wosize = 0 then some (st.emit (marshalHeader o.tag 0)) else do
      match st.seen.idxOf? l with
      | some idx =>
        let dist := idx + 1
        let bytes := if dist < 256 then [4, dist.toUInt8]
          else if dist < 65536 then 5 :: beBytes dist 2
          else if dist < 2^32 then 6 :: beBytes dist 4 else 0x14 :: beBytes dist 8
        some (st.emit bytes)
      | none =>
        let st := { st with seen := l :: st.seen }
        match o with
        | .block t fs =>
          if t ≥ 247 then none else do
          let st := { (st.emit (marshalHeader t fs.length)) with
            size32 := st.size32 + fs.length + 1, size64 := st.size64 + fs.length + 1 }
          fs.foldlM (fun st v => marshalRec h fuel v st) st
        | .bytes b =>
          some { (st.emit (marshalString b)) with
            size32 := st.size32 + 1 + (b.length + 4) / 4,
            size64 := st.size64 + 1 + (b.length + 8) / 8 }
        | .partialBytes _ => none
        | .double d =>
          some { (st.emit (0x0c :: (beBytes d.toNat 8).reverse)) with
            size32 := st.size32 + 3, size64 := st.size64 + 2 }
        | .doubleArray ds =>
          let head := if ds.length < 256 then [0x0e, ds.length.toUInt8]
            else if ds.length < 2^32 then 7 :: beBytes ds.length 4
            else 0x17 :: beBytes ds.length 8
          some { (st.emit (head ++ ds.flatMap (fun d => (beBytes d.toNat 8).reverse))) with
            size32 := st.size32 + 1 + 2 * ds.length, size64 := st.size64 + 1 + ds.length }
        | .int64 n =>
          some { (st.emit ([0x19, 95, 106, 0] ++ beBytes n.toNat 8)) with
            size32 := st.size32 + 4, size64 := st.size64 + 3 }
        | .int32 n =>
          some { (st.emit ([0x19, 95, 105, 0] ++ beBytes n.toNat 4)) with
            size32 := st.size32 + 3, size64 := st.size64 + 3 }
        | .nativeint n =>
          let payload := if -(2^31) ≤ n.toInt ∧ n.toInt < 2^31 then
            1 :: signedBytes n.toInt 4 else 2 :: beBytes n.toNat 8
          some { (st.emit ([0x19, 95, 110, 0] ++ payload)) with
            size32 := st.size32 + 3, size64 := st.size64 + 3 }
        | .channel _ => none
    | _ => none

/-- Marshal's default sharing mode, small format header. -/
def marshal (h : Heap) (v : Val) : Option (List UInt8) := do
  let st ← marshalRec h (h.size + 1) v {}
  let data := st.out.reverse
  if data.length ≥ 2^32 ∨ st.seen.length ≥ 2^32 ∨ st.size32 ≥ 2^32 ∨ st.size64 ≥ 2^32 then none else
  some (beBytes 0x8495a6be 4 ++ beBytes data.length 4 ++ beBytes st.seen.length 4 ++
    beBytes st.size32 4 ++ beBytes st.size64 4 ++ data)

end OCaml.Bytecode
