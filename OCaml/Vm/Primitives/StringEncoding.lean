import OCaml.Vm.Primitives.StringContract
import OCaml.Vm.Reloc
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- OCaml's string allocator zeroes the last payload word before filling
bytes and writing the final padding count. Equality compares these full words. -/
structure PaddedString (c : Config) (a : Nat) (b : List UInt8) : Prop
    extends StringShape c a b where
  data : ∀ i x, b[i]? = some x → byte c (a + i) = BitVec.ofNat 8 x.toNat
  zeroPad : ∀ i, b.length ≤ i → i < 8 * ((b.length + 8) / 8) - 1 → byte c (a + i) = 0

/-- Canonical allocator padding survives writes outside the string object. -/
theorem PaddedString.frame_log {c c' a b log} (h : PaddedString c a b)
    (outside : ObjectOutside log a (.bytes b))
    (memory : c'.σ.mem = writeLog c.σ.mem log) : PaddedString c' a b := by
  have header : word c' (a - 8) = word c (a - 8) :=
    Reloc.bytesT_congr (copied_of_writeLog memory outside.header)
  have extent : (Obj.bytes b).wosize = (b.length + 8) / 8 := by
    simp only [Obj.wosize]
    omega
  have payload := copied_of_writeLog memory outside.payload
  rw [extent] at payload
  have positive : 0 < 8 * ((b.length + 8) / 8) := by omega
  have last : a + 8 * ((b.length + 8) / 8) - 1 = a + (8 * ((b.length + 8) / 8) - 1) := by omega
  constructor
  · exact ⟨by rw [header]; exact h.headerSize,
      by rw [last, payload _ (by omega), ← last]; exact h.padding⟩
  · intro i x hi
    rw [payload i (by have := (List.getElem?_eq_some_iff.mp hi).1; omega)]
    exact h.data i x hi
  · intro i low high
    rw [payload i (by omega)]
    exact h.zeroPad i low high

/-- Read a byte from a total machine word, using the RAM observation algebra. -/
theorem word_byte_extract (c : Config) (a i : Nat) (hi : i < 8) :
    (word c a).extractLsb' (8 * i) 8 = byte c (a + i) :=
  bytesT_extract c.σ.mem a 8 i 1 (by omega)

/-- Equal words cover the entire payload, including its padding count. -/
theorem words_copied {c : Config} {a a' n : Nat}
    (words : ∀ i, i < n → word c (a' + 8 * i) = word c (a + 8 * i)) :
    Reloc.Copied c c a a' (8 * n) := by
  intro i hi
  have hq : i / 8 < n := by omega
  have he := congrArg (fun w : BitVec 64 => w.extractLsb' (8 * (i % 8)) 8) (words (i / 8) hq)
  rw [word_byte_extract _ _ _ (by omega), word_byte_extract _ _ _ (by omega)] at he
  have ha : a + 8 * (i / 8) + i % 8 = a + i := by omega
  have hb : a' + 8 * (i / 8) + i % 8 = a' + i := by omega
  simpa only [ha, hb] using he

/-- Header word counts and equal payload words determine the abstract bytes. -/
theorem PaddedString.eq_of_words {c a a' b b'}
    (h : PaddedString c a b) (h' : PaddedString c a' b')
    (size : (b.length + 8) / 8 = (b'.length + 8) / 8)
    (words : ∀ i, i < (b.length + 8) / 8 → word c (a' + 8 * i) = word c (a + 8 * i)) :
    b = b' := by
  have copied := words_copied words
  have positive : 0 < 8 * ((b.length + 8) / 8) := by omega
  have last := copied (8 * ((b.length + 8) / 8) - 1) (by omega)
  have addr : ∀ x, x + (8 * ((b.length + 8) / 8) - 1) = x + 8 * ((b.length + 8) / 8) - 1 := by
    intro x; omega
  simp only [addr] at last
  have pad := congrArg BitVec.toNat last
  rw [h.padding, size, h'.padding] at pad
  have len : b.length = b'.length := by omega
  apply List.ext_getElem len
  intro i hi hi'
  have he := copied i (by omega)
  rw [h.data i _ (List.getElem?_eq_getElem hi), h'.data i _ (List.getElem?_eq_getElem hi')] at he
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hn
  have hb := (b[i]).toNat_lt
  have hb' := (b'[i]).toNat_lt
  exact UInt8.toNat_inj.mp (by omega)

/-- Equal abstract strings have equal canonical payloads at distinct addresses. -/
theorem PaddedString.copied {c a a' b}
    (h : PaddedString c a b) (h' : PaddedString c a' b) :
    Reloc.Copied c c a a' (8 * ((b.length + 8) / 8)) := by
  intro i hi
  by_cases data : i < b.length
  · rw [h.data i b[i] (List.getElem?_eq_getElem data),
      h'.data i b[i] (List.getElem?_eq_getElem data)]
  · by_cases last : i = 8 * ((b.length + 8) / 8) - 1
    · subst i
      have positive : 0 < 8 * ((b.length + 8) / 8) := by omega
      have addr : ∀ x, x + (8 * ((b.length + 8) / 8) - 1) = x + 8 * ((b.length + 8) / 8) - 1 := by
        intro x; omega
      apply BitVec.eq_of_toNat_eq
      simp only [addr, h.padding, h'.padding]
    · rw [h.zeroPad i (by omega) (by omega), h'.zeroPad i (by omega) (by omega)]

/-- The finite word scan agrees exactly with equality of canonical strings. -/
theorem PaddedString.eq_iff_words {c a a' b b'}
    (h : PaddedString c a b) (h' : PaddedString c a' b') :
    b = b' ↔ (b.length + 8) / 8 = (b'.length + 8) / 8 ∧
      ∀ i, i < (b.length + 8) / 8 → word c (a' + 8 * i) = word c (a + 8 * i) := by
  constructor
  · intro same
    subst b'
    refine ⟨rfl, ?_⟩
    intro i hi
    exact Reloc.bytesT_congr ((h.copied h').mono (8 * i) 8 (by omega))
  · rintro ⟨size, words⟩
    exact h.eq_of_words h' size words

end OCaml.Vm.Primitives
