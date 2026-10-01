import OCaml.Bytecode.Value

/-! Data operations transcribed from runtime/{array,str,compare}.c.
Fuel bounds only traversal of possibly cyclic values; exhaustion leaves the
operation outside the supported fragment. -/
namespace OCaml.Bytecode

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

end OCaml.Bytecode
