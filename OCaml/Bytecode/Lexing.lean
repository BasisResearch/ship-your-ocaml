import OCaml.Bytecode.Value

/-! The table engine and position-memory bytecode from runtime/lexing.c.
All table indices and byte reads are checked. `none` is outside the
represented domain; a missing action reports `lexing: empty token`. -/
namespace OCaml.Bytecode

private def lexInt (h : Heap) (v : Val) (i : Nat) : Option Int := do
  match ← field? h v i with
  | .int n => some n.toInt
  | _ => none

private def lexShort (h : Heap) (tbl : Val) (field : Nat) (index : Int) : Option Int := do
  if index < 0 then none else do
  let bytes ← field? h tbl field >>= fun v => byteSlice? h v (2 * index.toNat) 2
  match bytes with
  | [lo, hi] => some ((BitVec.ofNat 16 (lo.toNat + 256 * hi.toNat)).toInt)
  | _ => none

/-- `run_mem` and `run_tag` share their two-byte instruction format. -/
private def lexMoves (h : Heap) (code mem : Val) (off : Nat) (replacement : Val) :
    Nat → Option Heap
  | 0 => none
  | fuel + 1 => do
    let dst ← byteSlice? h code off 1
    match dst with
    | [dst] =>
      if dst = 255 then some h else do
      let src ← byteSlice? h code (off + 1) 1
      match src with
      | [src] =>
        let v ← if src = 255 then some replacement else field? h mem src.toNat
        let h ← setField? h mem dst.toNat v
        lexMoves h code mem (off + 2) replacement fuel
      | _ => none
    | _ => none

private def lexRun (tbl buf code mem : Val) (moveFuel : Nat) :
    Nat → Heap → Int → Option (Option Int × Heap)
  | 0, _, _ => none
  | fuel + 1, h, state => do
    let base ← lexShort h tbl 0 state
    if base < 0 then
      let off ← lexShort h tbl 5 state
      if off < 0 then none else do
      let h ← lexMoves h code mem off.toNat (Val.ofInt (-1)) moveFuel
      some (some (-base - 1), h)
    else do
      let back ← lexShort h tbl 1 state
      let h ← if back < 0 then some h else do
        let off ← lexShort h tbl 6 state
        if off < 0 then none else do
        let h ← lexMoves h code mem off.toNat (Val.ofInt (-1)) moveFuel
        let curr ← field? h buf 5
        let h ← setField? h buf 6 curr
        setField? h buf 7 (Val.ofInt back)
      let pos ← lexInt h buf 5
      let len ← lexInt h buf 2
      let eof ← lexInt h buf 8
      if pos ≥ len && eof = 0 then some (some (-state - 1), h) else do
      let (ch, h) ← if pos ≥ len then some (256, h) else do
        if pos < 0 then none else do
        let bytes ← field? h buf 1 >>= fun v => byteSlice? h v pos.toNat 1
        match bytes with
        | [b] =>
          let h ← setField? h buf 5 (Val.ofInt (pos + 1))
          some (b.toNat, h)
        | _ => none
      let check ← lexShort h tbl 4 (base + ch)
      let next ← if check = state then lexShort h tbl 3 (base + ch) else lexShort h tbl 2 state
      if next < 0 then
        let last ← field? h buf 6
        let h ← setField? h buf 5 last
        let action ← lexInt h buf 7
        some (if action = -1 then none else some action, h)
      else do
        let baseCode ← lexShort h tbl 5 state
        let checkCode ← lexShort h tbl 9 (baseCode + ch)
        let off ← if checkCode = state then lexShort h tbl 8 (baseCode + ch) else lexShort h tbl 7 state
        let h ← if off ≤ 0 then some h else do
          let curr ← field? h buf 5
          lexMoves h code mem off.toNat curr moveFuel
        let h ← if ch = 256 then setField? h buf 8 .unit else some h
        lexRun tbl buf code mem moveFuel fuel h next

/-- New lexer engine. The bound covers one transition per input byte and
an EOF transition followed by a refill/acceptance. -/
def newLexEngine (h : Heap) (tbl : Val) (start : Int) (buf : Val) :
    Option (Option Int × Heap) := do
  let buffer ← field? h buf 1 >>= byteCells? h
  let code ← field? h tbl 10
  let codeBytes ← byteCells? h code
  let mem ← field? h buf 9
  let h ← if start < 0 then some h else do
    let curr ← field? h buf 5
    let h ← setField? h buf 4 curr
    let h ← setField? h buf 6 curr
    setField? h buf 7 (Val.ofInt (-1))
  lexRun tbl buf code mem (codeBytes.length + 1) (buffer.length + 3) h
    (if start < 0 then -start - 1 else start)

end OCaml.Bytecode
