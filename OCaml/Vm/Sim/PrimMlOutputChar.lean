import OCaml.Vm.Sim.PrimMlFlush
import OCaml.Vm.Primitives.Console.OutputChar

/-! `caml_ml_output_char` at a `C_CALL2` site: the model inversion (room in
the buffer, or a full buffer written out first) and the byte the machine
stores for the character argument. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- `caml_ml_output_char`'s model: a channel and an int argument, `putChar`
of its low byte, `Val_unit`. -/
theorem output_char_semantics {a b v : Val} {h h' : Heap} {w w' : World}
    (sem : primF1Impl "caml_ml_output_char" [a, b] h w = .ok v h' w') :
    ∃ id n, chanOf? h a = some id ∧ intArg? b = some n ∧
      putChar w id (n % 256).toNat.toUInt8 = some w' ∧ v = Val.unit ∧ h' = h := by
  cases hc : chanOf? h a with
  | none => simp [primF1Impl, hc] at sem
  | some id =>
    cases hn : intArg? b with
    | none => simp [primF1Impl, hc, hn] at sem
    | some n =>
      cases hp : putChar w id (n % 256).toNat.toUInt8 with
      | none => simp [primF1Impl, hc, hn, hp] at sem
      | some w'' =>
        simp [primF1Impl, hc, hn, hp] at sem
        obtain ⟨rfl, rfl, rfl⟩ := sem
        exact ⟨id, n, rfl, rfl, hp, rfl, rfl⟩

/-- The two outcomes of `putChar` on an open output channel. -/
inductive PutCharCase (w : World) (id : Nat) (b : UInt8) (c : Chan) : World → Prop where
  /-- room in the buffer: the byte appended -/
  | room (len : c.buf.length < ioBufferSize) :
      PutCharCase w id b c (w.setChan id { c with buf := c.buf ++ [b] })
  /-- a full buffer: written out, then the byte alone -/
  | full (len : ioBufferSize ≤ c.buf.length) (fits : offsetFits c c.buf.length = true) {w'' : World}
      (write : writeFd w c.fd c.buf = some w'') :
      PutCharCase w id b c (w''.setChan id { c with buf := [b], offset := c.offset + c.buf.length })

/-- Invert `putChar`. -/
theorem putChar_cases {w w' : World} {id : Nat} {b : UInt8} (h : putChar w id b = some w') :
    ∃ c, w.chans[id]? = some c ∧ 0 ≤ c.fd ∧ c.isOut = true ∧ PutCharCase w id b c w' := by
  unfold putChar at h
  cases hc : w.chans[id]? with
  | none => simp [hc] at h
  | some c =>
    simp [hc] at h
    obtain ⟨⟨fd0, out⟩, h⟩ := h
    refine ⟨c, rfl, fd0, out, ?_⟩
    split at h
    · rename_i full
      split at h
      · cases h
      · rename_i fits
        cases hw : writeFd w c.fd c.buf with
        | none => rw [hw] at h; cases h
        | some w'' =>
          rw [hw] at h
          simp only [Option.bind, Option.some.injEq] at h
          subst h
          exact .full full (by simpa using fits) hw
    · rename_i room
      simp only [Option.some.injEq] at h
      subst h
      exact .room (by omega)

/-- **The stored byte**: `sb` of the untagged character argument is its low
byte, the model's `(n % 256)`. -/
theorem char_byte (n : BitVec 63) :
    Vsa.Sim.sbData (Functions.shift_bits_right_arith (tag64 n) 1#6) =
      BitVec.ofNat 8 ((n.toInt % 256).toNat.toUInt8).toNat := by
  have low : Vsa.Sim.sbData (Functions.shift_bits_right_arith (tag64 n) 1#6) = n.setWidth 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h1 : Sail.BitVec.toNatInt (1#6) = 1 := by decide
    simp [h1, Vsa.Sim.sbData, Functions.shift_bits_right_arith, tag64, Sail.BitVec.extractLsb,
      BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend]
    have h8 : i < 8 := by omega
    simp [h8, show 1 + i < 64 by omega, show i < 63 by omega, show i ≤ 7 by omega, show i < 64 by omega]
  rw [low]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have byte : ((n.toInt % 256).toNat.toUInt8).toNat = (n.toInt % 256).toNat := by
    have lt : (n.toInt % 256).toNat < 256 := by omega
    rw [Nat.toUInt8, UInt8.toNat_ofNat']; omega
  rw [byte, BitVec.toInt_eq_toNat_cond]
  split <;> omega

end OCaml.Vm.Sim
