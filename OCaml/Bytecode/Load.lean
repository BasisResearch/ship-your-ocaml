import OCaml.Bytecode.Semantics

/-!
# Loading a bytecode executable into a `Prog` (executable model of the
cut-point state)

What `caml_main` does before calling `caml_interprete`: read CODE and PRIM,
unmarshal DATA (`caml_input_val`, `runtime/intern.c`) into the heap, and set
`caml_global_data` to the result. This file transcribes the unmarshaller
for the codes that occur in executables' global data, allocating objects in
`intern.c`'s `obj_counter` order, so `SHARED` back-references are location
arithmetic.

This is an EXECUTABLE model, used to run `BcSem` on real bytecode
(`experiments/RunBc.lean`, VALIDATION.md). It is not part of the trusted
statement: `Loaded` (`OCaml/Refinement.lean`) relates `P.heap0` to the
machine's memory through the representation predicate, whatever produced it.
-/

namespace OCaml.Bytecode

structure Rd where
  b : ByteArray
  pos : Nat

namespace Rd
def u8 (r : Rd) : Option (Nat × Rd) :=
  if r.pos < r.b.size then some ((r.b.get! r.pos).toNat, { r with pos := r.pos + 1 }) else none
def ubytes (r : Rd) (n : Nat) : Option (Nat × Rd) :=
  if r.pos + n ≤ r.b.size then
    some ((List.range n).foldl (fun a k => a * 256 + (r.b.get! (r.pos + k)).toNat) 0,
          { r with pos := r.pos + n })
  else none
def sbytes (r : Rd) (n : Nat) : Option (Int × Rd) := do
  let (u, r') ← r.ubytes n
  pure (if u ≥ 2 ^ (8 * n - 1) then (u : Int) - 2 ^ (8 * n) else u, r')
def raw (r : Rd) (n : Nat) : Option (List UInt8 × Rd) :=
  if r.pos + n ≤ r.b.size then
    some ((List.range n).map fun k => r.b.get! (r.pos + k), { r with pos := r.pos + n })
  else none
/-- A NUL-terminated identifier. -/
def cstr (r : Rd) : Option (String × Rd) :=
  let rec go (r : Rd) (acc : List Char) : Nat → Option (String × Rd)
    | 0 => none
    | f + 1 => do
      let (c, r') ← r.u8
      if c = 0 then pure (String.ofList acc.reverse, r') else go r' (Char.ofNat c :: acc) f
  go r [] 64
end Rd

/-- Little-endian 8 bytes of a double as read by `readfloat`
(`CODE_DOUBLE_LITTLE`); big-endian otherwise. -/
def dbl (bs : List UInt8) (little : Bool) : BitVec 64 :=
  let bs := if little then bs.reverse else bs
  BitVec.ofNat 64 (bs.foldl (fun a x => a * 256 + x.toNat) 0)

/-- Unmarshaller state: the heap (objects in `obj_counter` order, from
location `base`). -/
structure IS where
  r : Rd
  h : Heap

/-- `intern_rec`, with fuel. Returns the value and the new state. -/
def internRec (base : Nat) : Nat → IS → Option (Val × IS)
  | 0, _ => none
  | fuel + 1, st => do
    let (code, r) ← st.r.u8
    let st := { st with r := r }
    let newObj := fun (o : Obj) (st : IS) =>
      let (h, l) := st.h.alloc o
      (Val.ptr l 0, { st with h := h })
    let block := fun (tag size : Nat) (st : IS) => do
      if size = 0 then pure (Val.atom tag, st) else
      let (h, l) := st.h.alloc (.block tag [])
      let (fs, st) ← (List.range size).foldlM (fun (acc, st) _ => do
          let (v, st) ← internRec base fuel st
          pure (acc ++ [v], st)) (([] : List Val), { st with h := h })
      pure (Val.ptr l 0, { st with h := st.h.set l (.block tag fs) })
    let str := fun (len : Nat) (st : IS) => do
      let (bs, r) ← st.r.raw len
      pure (newObj (.bytes bs) { st with r := r })
    let shared := fun (ofs : Nat) (st : IS) =>
      let n := st.h.size - base
      if ofs = 0 ∨ ofs > n then none else some (Val.ptr (base + n - ofs) 0, st)
    if code ≥ 0x80 then block (code % 16) ((code / 16) % 8) st
    else if code ≥ 0x40 then pure (Val.ofInt (code % 64), st)
    else if code ≥ 0x20 then str (code % 32) st
    else match code with
    | 0x0 => do let (n, r) ← st.r.sbytes 1; pure (Val.ofInt n, { st with r := r })
    | 0x1 => do let (n, r) ← st.r.sbytes 2; pure (Val.ofInt n, { st with r := r })
    | 0x2 => do let (n, r) ← st.r.sbytes 4; pure (Val.ofInt n, { st with r := r })
    | 0x3 => do let (n, r) ← st.r.sbytes 8; pure (Val.ofInt n, { st with r := r })
    | 0x4 => do let (o, r) ← st.r.ubytes 1; shared o { st with r := r }
    | 0x5 => do let (o, r) ← st.r.ubytes 2; shared o { st with r := r }
    | 0x6 => do let (o, r) ← st.r.ubytes 4; shared o { st with r := r }
    | 0x14 => do let (o, r) ← st.r.ubytes 8; shared o { st with r := r }
    | 0x8 => do let (hd, r) ← st.r.ubytes 4; block (hd % 256) (hd / 1024) { st with r := r }
    | 0x13 => do let (hd, r) ← st.r.ubytes 8; block (hd % 256) (hd / 1024) { st with r := r }
    | 0x9 => do let (n, r) ← st.r.ubytes 1; str n { st with r := r }
    | 0xA => do let (n, r) ← st.r.ubytes 4; str n { st with r := r }
    | 0x15 => do let (n, r) ← st.r.ubytes 8; str n { st with r := r }
    | 0xB | 0xC => do
        let (bs, r) ← st.r.raw 8
        pure (newObj (.double (dbl bs (code = 0xC))) { st with r := r })
    | 0xD | 0xE | 0xF | 0x7 | 0x16 | 0x17 => do
        let lw := if code = 0xD ∨ code = 0xE then 1 else if code = 0xF ∨ code = 0x7 then 4 else 8
        let little := code = 0xE ∨ code = 0x7 ∨ code = 0x17
        let (n, r) ← st.r.ubytes lw
        let (bs, r) ← r.raw (8 * n)
        let ds := (List.range n).map fun k => dbl ((bs.drop (8 * k)).take 8) little
        pure (newObj (.doubleArray ds) { st with r := r })
    | 0x18 | 0x19 => do
        let (ident, r) ← st.r.cstr
        let r ← if code = 0x18 then (do let (_, r) ← r.ubytes 4; let (_, r) ← r.ubytes 8; pure r) else pure r
        match ident with
        | "_j" => do let (n, r) ← r.ubytes 8; pure (newObj (.int64 (BitVec.ofNat 64 n)) { st with r := r })
        | "_i" => do let (n, r) ← r.ubytes 4; pure (newObj (.int32 (BitVec.ofNat 32 n)) { st with r := r })
        | "_n" => do
            let (k, r) ← r.u8
            if k = 1 then do
              let (n, r) ← r.sbytes 4; pure (newObj (.nativeint (BitVec.ofInt 64 n)) { st with r := r })
            else do
              let (n, r) ← r.ubytes 8; pure (newObj (.nativeint (BitVec.ofNat 64 n)) { st with r := r })
        | _ => none
    | _ => none

/-- `caml_input_val` on a DATA section: header, then the value. -/
def unmarshal (b : ByteArray) (h : Heap) : Option (Val × Heap) := do
  let r : Rd := ⟨b, 0⟩
  let (magic, r) ← r.ubytes 4
  let r ← if magic = 0x8495A6BE then (do let (_, r) ← r.raw 16; pure r)
          else if magic = 0x8495A6BF then (do let (_, r) ← r.raw 28; pure r)
          else none
  let (v, st) ← internRec h.size (b.size * 4 + 16) ⟨r, h⟩
  pure (v, st.h)

def strBytes (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

/-- Load a bytecode executable (the file's bytes) as the cut-point `Prog`,
with the command line `src/main.c` bakes in: `caml_exe_name = "/prog"`,
`main_argv = [| "/prog"; args… |]`. -/
def loadExe (f : ByteArray) (args : List String := [])
    (files : List (String × List UInt8) := []) : Option Prog := do
  let code ← sectionBytes f "CODE"
  let prim ← sectionBytes f "PRIM"
  let data ← sectionBytes f "DATA"
  let (g, h) ← unmarshal data ⟨#[]⟩
  let (h, ls) := ("/prog" :: args).foldl (fun (h, ls) a =>
    let (h, l) := h.alloc (.bytes (strBytes a)); (h, ls ++ [Val.ptr l 0])) (h, [])
  let (h, av) := if ls.isEmpty then (h, Val.atom 0) else
    let (h, l) := h.alloc (.block 0 ls); (h, Val.ptr l 0)
  pure ⟨codeOfBytes code, primsOfBytes prim, h, g, strBytes "/prog", av,
    ("/prog", f.toList) :: files⟩

/-- A halting run, as a checkable function: `runTo P k s = some (e, w)` if
`s` halts with `(e, w)` within `k` steps. -/
def runTo (P : Prog) : Nat → St → Option (Nat × World)
  | 0, _ => none
  | k + 1, s => match step P s with
    | .next s' => runTo P k s'
    | .halt e w => some (e, w)
    | _ => none

theorem runTo_sound (P : Prog) :
    ∀ k s, Reach P s → ∀ e w, runTo P k s = some (e, w) →
      ∃ s', Reach P s' ∧ step P s' = .halt e w := by
  intro k
  induction k with
  | zero => intro s _ e w h; simp [runTo] at h
  | succ k ih =>
    intro s hr e w h
    simp only [runTo] at h
    split at h
    · rename_i s' hs
      obtain ⟨n, hn⟩ := hr
      exact ih s' ⟨n + 1, hn.snoc (.mk hs)⟩ e w h
    · rename_i e' w' hs
      cases h; exact ⟨s, hr, hs⟩
    · cases h

/-- **Checked runs are behaviours**: if `runTo` halts from the initial
state, `BcSem` halts with that output and exit code. -/
theorem bcHalts_of_runTo {P : Prog} {k : Nat} {e : Nat} {w : World}
    (h : runTo P k P.init = some (e, w)) : BcHalts P (bytesToString w.console) e := by
  obtain ⟨s, hr, hs⟩ := runTo_sound P k P.init ⟨0, .zero _⟩ e w h
  exact ⟨s, w, hr, hs, rfl⟩

/-- The primitive a `C_CALLn` at `s.pc` calls, for diagnostics. -/
def primNameAt (P : Prog) (pc : Nat) : String :=
  match decodeAt P.code pc with
  | some ⟨.C_CALL1, [p]⟩ | some ⟨.C_CALL2, [p]⟩ | some ⟨.C_CALL3, [p]⟩
  | some ⟨.C_CALL4, [p]⟩ | some ⟨.C_CALL5, [p]⟩ | some ⟨.C_CALLN, [_, p]⟩ =>
      P.prims[p.toNat]?.getD "?"
  | _ => ""

/-- Run `BcSem` for at most `fuel` steps (executable; for validation). -/
def run (P : Prog) : Nat → St → Nat → (String × Option Nat × Nat × String)
  | 0, s, n => (bytesToString s.world.console, none, n, s!"fuel out at pc {s.pc}")
  | fuel + 1, s, n =>
    -- Retain only diagnostic scalars/output across step. Keeping s alive
    -- here forces every otherwise-exclusive heap array update to copy.
    let pc := s.pc
    let output := s.world.console
    match step P s with
    | .next s' => run P fuel s' (n + 1)
    | .halt e w => (bytesToString w.console, some e, n, "halt")
    | .unsupported =>
      (bytesToString output, none, n,
        s!"unsupported at pc {pc}: {repr ((decodeAt P.code pc).map (·.op))} {primNameAt P pc}")
    | .wrong => (bytesToString output, none, n,
        s!"wrong at pc {pc}: {repr ((decodeAt P.code pc).map (·.op))}")

end OCaml.Bytecode
