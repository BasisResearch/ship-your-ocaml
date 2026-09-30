import OCaml.Logic.Symbolic
import OCaml.Run.Local

/-!
# Code locality with absolute machine addresses

A slice decodes at `pc - base`, but executes the real `stepI` on the original
state and program. Thus branch offsets, closure code pointers, saved return
addresses and primitive/global lookups retain their original meaning.
-/
namespace OCaml.Bytecode

private theorem mapM_congr_on {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Decoding depends only on the opcode, length operand (for variable-length
instructions), and the declared operands. This is independent of code size. -/
theorem decodeAt_local (a b : Code) (pa pb len : Nat) (op : Opcode)
    (hw : a.word pa = b.word pb)
    (hop : (b.word pb).bind Opcode.ofNat? = some op)
    (hl : instrLength b pb op = some len)
    (hw1 : a.word (pa + 1) = b.word (pb + 1))
    (ha : ∀ k, k < len - 1 → a.arg (pa + 1 + k) = b.arg (pb + 1 + k)) :
    decodeAt a pa = decodeAt b pb := by
  have hlen : instrLength a pa op = instrLength b pb op := by
    unfold instrLength
    split <;> simp only [hw1]
  have hargs : (List.range (len - 1)).mapM (fun k => a.arg (pa + 1 + k)) =
      (List.range (len - 1)).mapM (fun k => b.arg (pb + 1 + k)) :=
    mapM_congr_on _ _ _ (fun k hk => ha k (List.mem_range.mp hk))
  unfold decodeAt
  cases hb : b.word pb with
  | none => simp [hb] at hop
  | some w =>
    simp only [hb, Option.bind_some] at hop
    simp [hw, hb, hop, hlen, hl, hargs]

/-- Word lookup in an extracted window uses an absolute address only in
this proof; symbolic evaluation subsequently sees just the small array. -/
theorem code_extract_word (code : Code) (base stop pc : Nat)
    (lo : base ≤ pc) (hi : pc < stop) :
    (code.extract base stop)[pc - base]? = code[pc]? := by
  simp only [Array.getElem?_extract]
  split <;> simp_all <;> omega

/-- A complete instruction in an extracted window decodes identically.
The extra word bound includes the size operand of variable-length opcodes. -/
theorem decodeAt_extract (code : Code) (base stop pc len : Nat) (op : Opcode)
    (lo : base ≤ pc) (hi : pc + max len 2 ≤ stop)
    (hop : (Code.word (code.extract base stop) (pc - base)).bind Opcode.ofNat? = some op)
    (hl : instrLength (code.extract base stop) (pc - base) op = some len) :
    decodeAt code pc = decodeAt (code.extract base stop) (pc - base) := by
  apply decodeAt_local code (code.extract base stop) pc (pc - base) len op
  · unfold Code.word
    rw [code_extract_word code base stop pc lo (by omega)]
  · exact hop
  · exact hl
  · unfold Code.word
    rw [show pc - base + 1 = (pc + 1) - base by omega,
      code_extract_word code base stop (pc + 1) (by omega) (by omega)]
  · intro k hk
    unfold Code.arg
    rw [show pc - base + 1 + k = (pc + 1 + k) - base by omega,
      code_extract_word code base stop (pc + 1 + k) (by omega) (by omega)]

/-- Execute using a local decoder and the real instruction semantics. -/
def decodedK (P : Prog) (decode : Nat → Option Instr) (s : St) : Except Res St :=
  match (match decode s.pc with | some i => stepI P s i | none => .wrong) with
  | .next t => .ok t
  | r => .error r

/-- A code window carries its absolute origin separately from its words. -/
structure CodeSlice where
  base : Nat
  code : Code

/-- PCs below the origin cannot wrap through truncated subtraction. -/
def CodeSlice.decode (c : CodeSlice) (pc : Nat) : Option Instr :=
  if c.base ≤ pc then decodeAt c.code (pc - c.base) else none

/-- The decoder agreement needed for a local symbolic run. Generated tables
supply this at instruction boundaries; operands must fit inside the slice. -/
structure CodeSlice.Covers (c : CodeSlice) (P : Prog) (region : Nat → Prop) : Prop where
  decode_eq : ∀ pc, region pc → decodeAt P.code pc = c.decode pc

/-- A run confined to certified instruction boundaries is identical on the
code slice. This includes halted, wrong and unsupported outcomes and permits
the last instruction to leave the region. -/
theorem CodeSlice.iter_eq (c : CodeSlice) (P : Prog) (region : Nat → Prop)
    (cover : c.Covers P region) (n : Nat) (s : St)
    (confined : ∀ k, k < n → ∀ t, Run.iter (bcK P) k s = .ok t → region t.pc) :
    Run.iter (bcK P) n s = Run.iter (decodedK P c.decode) n s := by
  apply Run.iter_eq_of_agree
  intro k hk t ht
  unfold bcK step decodedK
  rw [cover.decode_eq t.pc (confined k hk t ht)]
  rfl

/-- A successful local run needs decoder agreement only where it decoded
an instruction. The successful-run premise rules out all window escapes
before its last step, so clients need no separate confinement proof. -/
theorem decoded_run_sound (P : Prog) (decode : Nat → Option Instr)
    (cover : ∀ pc i, decode pc = some i → decodeAt P.code pc = some i)
    (n : Nat) (s t : St) (h : Run.iter (decodedK P decode) n s = .ok t) :
    Run.iter (bcK P) n s = .ok t := by
  apply Run.iter_ok_of_step (decodedK P decode) (bcK P) _ n s t h
  intro a b hab
  cases hd : decode a.pc with
  | none => simp [decodedK, hd] at hab
  | some i =>
    unfold bcK step
    rw [cover a.pc i hd]
    simp only [decodedK, hd] at hab
    cases hr : stepI P a i <;> simp_all

end OCaml.Bytecode
