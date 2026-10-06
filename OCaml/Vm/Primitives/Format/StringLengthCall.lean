import OCaml.Vm.Primitives.Format.StringLength
import OCaml.Vm.Primitives.CamlMlStringLength

/-!
# `caml_string_length` as a call summary

The C helper `caml_string_length(s)` (used by `parse_format`) computes the
untagged byte length of an OCaml string from its header and padding byte, by
the same arithmetic as `caml_ml_string_length` without the tag. Its generated
block (`length_fast`, `--ocaml-format`) runs from any caller; the header and
padding windows come from the string's `StringGeometry` and `StringShape`.
-/

namespace OCaml.Vm.Primitives.Format.StringLength
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The untagged length from the header's word size and the padding byte. -/
theorem untagged (header : BitVec 64) (padding : BitVec 8) (n : Nat)
    (hs : header.toNat / 1024 = (n + 8) / 8)
    (hp : padding.toNat = 8 * ((n + 8) / 8) - 1 - n) :
    stringLast header - padding.setWidth 64 = BitVec.ofNat 64 n := by
  have last := stringLast_toNat header n hs
  have hb := padding.isLt
  have hh := header.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, last, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have small : 8 * ((n + 8) / 8) ≤ 2 ^ 61 := by
    have : (n + 8) / 8 ≤ header.toNat / 1024 := by omega
    have : header.toNat / 1024 < 2 ^ 54 := by omega
    omega
  rw [Nat.mod_eq_of_lt (a := padding.toNat) (by omega)]
  omega

/-- A one-byte total read is the byte map's entry. -/
theorem byte_getD (c : Config) (a : Nat) : byte c a = (c.σ.mem[a]?).getD 0 := by
  simp only [byte, bytesT]
  change (0#0).append ((c.σ.mem[a]?).getD 0) = _
  rw [BitVec.append]
  simp

/-- The registers `caml_string_length` writes. -/
def lengthWrites : List Nat := [10, 15]

/-- **`caml_string_length` on a placed string** of byte length `n` at value
address `a`: returns `n`, writes only `a0`/`a5` (both pinned), leaves memory
unchanged. -/
theorem string_length_call (c : Config) (ra : BitVec 64) {a n : Nat}
    (h : LeafInput ra c) (argument : gpr c 10 = some (BitVec.ofNat 64 a))
    (geometry : StringGeometry a n) (shape : StringShape c a n) :
    FnSummary 0x80013570#64 (fun d => d = c)
      (WriteRegistersPost lengthWrites [] c ra (BitVec.ofNat 64 n)
        [(10, BitVec.ofNat 64 n), (15, stringLast (word c (a - 8))), (1, ra)]) := by
  let R : Nat → BitVec 64 := fun k => if k = 1 then ra else BitVec.ofNat 64 a
  have regs : GHolds c.σ (length_input R) := ⟨h.raReg, argument, True.intro⟩
  have minus8 : R 10 + 18446744073709551608#64 = BitVec.ofNat 64 a - 8 := by
    simp only [R, BitVec.sub_eq_add_neg]; rfl
  have hw : bytesVal .ld (read8 c.σ.mem (R 10 + 18446744073709551608#64).toNat) = word c (a - 8) := by
    rw [read8_value, minus8, string_header_address geometry]; rfl
  have last : ∀ x : BitVec 64, x >>> 10 <<< 3 + 18446744073709551615#64 = stringLast x := by
    intro x; simp only [stringLast, BitVec.sub_eq_add_neg]; rfl
  have padAddr : R 10 + (bytesVal .ld (read8 c.σ.mem (R 10 + 18446744073709551608#64).toNat) >>> 10 <<< 3 +
      18446744073709551615#64) = BitVec.ofNat 64 a + stringLast (word c (a - 8)) := by
    rw [hw, last]; rfl
  have w0 : ReadWindow (R 10 + 18446744073709551608#64) 8 := by
    rw [minus8]; exact geometry.header_window
  have w1 : ReadWindow (R 10 + (bytesVal .ld (read8 c.σ.mem (R 10 + 18446744073709551608#64).toNat) >>> 10 <<< 3 +
      18446744073709551615#64)) 1 := by
    rw [padAddr]; exact geometry.padding_window shape.headerSize
  have S := length_fast c R h regs w0 w1
  apply S.weaken (fun _ e => e)
  intro after post
  have padByte : (c.σ.mem[(BitVec.ofNat 64 a + stringLast (word c (a - 8))).toNat]?).getD 0 =
      byte c (a + 8 * ((n + 8) / 8) - 1) := by
    rw [string_padding_address geometry shape.headerSize, byte_getD]
  have value : bytesVal .ld ((length_loads c.σ.mem R).getD 0 []) >>> 10 <<< 3 +
      (18446744073709551615#64 + -bytesVal .lbu ((length_loads c.σ.mem R).getD 1 [])) = BitVec.ofNat 64 n := by
    simp only [length_loads, List.getD_cons_zero, List.getD_cons_succ]
    rw [padAddr, padByte, hw, ← BitVec.add_assoc, last, ← BitVec.sub_eq_add_neg]
    simp only [bytesVal, zero_extend, Sail.BitVec.zeroExtend]
    exact untagged _ _ n shape.headerSize shape.padding
  have lastValue : bytesVal .ld ((length_loads c.σ.mem R).getD 0 []) >>> 10 <<< 3 + 18446744073709551615#64 =
      stringLast (word c (a - 8)) := by
    simp only [length_loads, List.getD_cons_zero]
    rw [hw, last]
  have call := post.toEffectPost
  rw [value] at call
  have regs' := post.regs
  simp only [length_regs] at regs'
  rw [value, lastValue] at regs'
  exact { call with
    pc := call.pc
    frame := fun r out noise => call.frame r (fun k hk => out k (by
      simpa only [lengthWrites, List.mem_cons, List.not_mem_nil, or_false] using hk)) noise
    regs := regs' }

end OCaml.Vm.Primitives.Format.StringLength
