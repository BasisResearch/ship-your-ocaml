import OCaml.Vm.Primitives.StringAllocationArithmetic
import OCaml.Vm.Primitives.StringEncoding
import OCaml.Vm.Primitives.Write
import Vsa.Sim.WriteLogNF

namespace OCaml.Vm.Primitives.StringAllocation
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- Allocator-owned header and padding, before the caller copies the data. -/
structure StringShell (c : Config) (a n : Nat) : Prop where
  header : HeaderOk (word c (a - 8)) ((n + 8) / 8) 252
  padding : (byte c (a + 8 * ((n + 8) / 8) - 1)).toNat = 8 * ((n + 8) / 8) - 1 - n
  zeroPad : ∀ i, n ≤ i → i < 8 * ((n + 8) / 8) - 1 → byte c (a + i) = 0

/-- Canonical first-order effect of the string initialization stores. -/
def shellLog (a n : Nat) : List WEntry :=
  [(a - 8, 8, (stringWords (BitVec.ofNat 64 n) <<< 10) + 252#64),
   (a + 8 * ((n + 8) / 8) - 8, 8, 0),
   (a + 8 * ((n + 8) / 8) - 1, 1,
      paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n))]

/-- Read the header and padding directly from the initializer's finite log. -/
theorem shell_layout {c after : Config} {a n : Nat}
    (address : 8 ≤ a) (bound : n < 2^32)
    (memory : after.σ.mem = writeLog c.σ.mem (shellLog a n)) : StringShell after a n := by
  let span := 8 * ((n + 8) / 8)
  have positive : 8 ≤ span := by dsimp [span]; omega
  have headerOutside : OutLRange
      [(a + span - 8, 8, 0), (a + span - 1, 1,
        paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n))] (a - 8) 8 :=
    ⟨Or.inl (by omega), Or.inl (by omega), True.intro⟩
  constructor
  · change HeaderOk (bytesT after.σ.mem _ 8) _ _
    rw [memory]
    rw [show shellLog a n =
      [(a - 8, 8, (stringWords (BitVec.ofNat 64 n) <<< 10) + 252#64)] ++
      [(a + span - 8, 8, 0), (a + span - 1, 1,
        paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n))] from rfl,
      writeLog_append]
    rw [bytesT_writeLog_out _ headerOutside, word_writeLog]
    exact stringHeader_ok n bound
  · have pin := pin1_of_writeLog c.σ.mem
      [(a - 8, 8, (stringWords (BitVec.ofNat 64 n) <<< 10) + 252#64),
       (a + span - 8, 8, 0)] [] (a + span - 1)
      (paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n)) True.intro
    change (bytesT after.σ.mem _ 1).toNat = _
    rw [memory]
    simp only [bytesT, BitVec.append_eq, BitVec.toNat_append, BitVec.toNat_cast, BitVec.toNat_zero_length, Nat.zero_shiftLeft, Nat.zero_or]
    change (((writeLog c.σ.mem (shellLog a n))[a + span - 1]?).getD 0).toNat = _
    have pin' : (writeLog c.σ.mem (shellLog a n))[a + span - 1]? =
        some (sbData (paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n))) := pin
    rw [pin']
    change ((paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n)).extractLsb' 0 8).toNat = _
    rw [BitVec.extractLsb'_toNat, paddingWord_toNat n bound, Nat.shiftRight_zero]
    omega
  · intro i low high
    have k : i - (span - 8) < 8 := by dsimp [span] at *; omega
    have addr : a + span - 8 + (i - (span - 8)) = a + i := by dsimp [span] at *; omega
    have outside : OutLRange
        [(a + span - 1, 1, paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n))]
        (a + i) 1 := ⟨Or.inl (by dsimp [span] at *; omega), True.intro⟩
    change bytesT after.σ.mem (a + i) 1 = 0
    rw [memory]
    rw [show shellLog a n =
      [(a - 8, 8, (stringWords (BitVec.ofNat 64 n) <<< 10) + 252#64)] ++
      [(a + span - 8, 8, 0)] ++ [(a + span - 1, 1,
        paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n))] from rfl,
      writeLog_append, writeLog_append]
    rw [bytesT_writeLog_out _ outside, ← addr, ← bytesT_extract _ _ 8 _ 1 (by omega)]
    rw [word_writeLog]
    simp

/-- Filling the payload completes the abstract string object. -/
theorem StringShell.object {c a b pl cp} (shell : StringShell c a b.length)
    (data : ∀ i x, b[i]? = some x → byte c (a + i) = BitVec.ofNat 8 x.toNat) :
    ObjAt c pl cp a (.bytes b) := by
  have size : (Obj.bytes b).wosize = (b.length + 8) / 8 := by
    simp only [Obj.wosize]
    omega
  change HeaderOk _ _ _ ∧ _
  rw [size]
  exact ⟨shell.header, data, shell.padding⟩

/-- The same stores also establish the canonical padding used by equality. -/
theorem StringShell.padded {c a b} (shell : StringShell c a b.length)
    (data : ∀ i x, b[i]? = some x → byte c (a + i) = BitVec.ofNat 8 x.toNat) :
    PaddedString c a b := ⟨⟨shell.header.2, shell.padding⟩, data, shell.zeroPad⟩

end OCaml.Vm.Primitives.StringAllocation
