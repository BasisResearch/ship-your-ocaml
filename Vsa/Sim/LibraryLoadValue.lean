import Vsa.Sim.BlockMem
import Vsa.Sim.LibraryMemory

namespace Vsa.Sim
open Vsa.MemRepr LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem read64_bytes (m : Mem) (a p : Nat) (h : read64 m a = some p) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      m[a + 4]? = some b4 ∧ m[a + 5]? = some b5 ∧ m[a + 6]? = some b6 ∧ m[a + 7]? = some b7 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p := by
  simp only [read64, readLE, bind, Option.bind] at h
  match hb0 : m[a]?, hb1 : m[a + 1]?, hb2 : m[a + 2]?, hb3 : m[a + 3]?,
        hb4 : m[a + 4]?, hb5 : m[a + 5]?, hb6 : m[a + 6]?, hb7 : m[a + 7]? with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h
      have hk := Option.some.inj h
      omega
  | none, _, _, _, _, _, _, _ => rw [hb0] at h; exact absurd h (by simp)
  | some _, none, _, _, _, _, _, _ => rw [hb0, hb1] at h; exact absurd h (by simp)
  | some _, some _, none, _, _, _, _, _ => rw [hb0, hb1, hb2] at h; exact absurd h (by simp)
  | some _, some _, some _, none, _, _, _, _ => rw [hb0, hb1, hb2, hb3] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, none, _, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, none, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, none, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, some _, none =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h; exact absurd h (by simp)

theorem read64_lt_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) : q < 2^64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hq⟩ := read64_bytes mem a q h
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  omega

theorem ld_value_eq_read64 (mem : Mem) (a q : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : read64 mem a = some q)
    (e0 : mem[a]? = some b0) (e1 : mem[a+1]? = some b1) (e2 : mem[a+2]? = some b2)
    (e3 : mem[a+3]? = some b3) (e4 : mem[a+4]? = some b4) (e5 : mem[a+5]? = some b5)
    (e6 : mem[a+6]? = some b6) (e7 : mem[a+7]? = some b7) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, f0, f1, f2, f3, f4, f5, f6, f7, hq⟩ :=
    read64_bytes mem a q h
  have hb0 : b0 = c0 := by rw [e0] at f0; injection f0
  have hb1 : b1 = c1 := by rw [e1] at f1; injection f1
  have hb2 : b2 = c2 := by rw [e2] at f2; injection f2
  have hb3 : b3 = c3 := by rw [e3] at f3; injection f3
  have hb4 : b4 = c4 := by rw [e4] at f4; injection f4
  have hb5 : b5 = c5 := by rw [e5] at f5; injection f5
  have hb6 : b6 = c6 := by rw [e6] at f6; injection f6
  have hb7 : b7 = c7 := by rw [e7] at f7; injection f7
  subst hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [sext64_id]
  apply BitVec.eq_of_toNat_eq
  rw [word8_recon_env, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mem a q h), ← hq]

def execRetEpilogueWord (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a+1]?).getD 0, (m[a+2]?).getD 0,
   (m[a+3]?).getD 0, (m[a+4]?).getD 0, (m[a+5]?).getD 0,
   (m[a+6]?).getD 0, (m[a+7]?).getD 0]

theorem execRetEpilogueWord_value (m : Mem) (a : Nat) (value : BitVec 64)
    (h : read64 m a = some value.toNat) :
    bytesVal .ld (execRetEpilogueWord m a) = value := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, _⟩ :=
    read64_bytes m a value.toNat h
  simpa [execRetEpilogueWord, h0, h1, h2, h3, h4, h5, h6, h7, bytesVal] using
    ld_value_eq_read64 m a value.toNat b0 b1 b2 b3 b4 b5 b6 b7
      h h0 h1 h2 h3 h4 h5 h6 h7

end Vsa.Sim

namespace VsaIris.MallocFast
open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def wordOf (f : Nat → BitVec 8) (a : Nat) : List (BitVec 8) :=
  [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6), f (a + 7)]

theorem wordOf_value {f : Nat → BitVec 8} {a : Nat} {m : Std.ExtHashMap Nat (BitVec 8)} {v : BitVec 64}
    (him : ∀ k, k < 8 → m[a + k]? = some (f (a + k))) (hr : Vsa.MemRepr.read64 m a = some v.toNat) :
    bytesVal .ld (wordOf f a) = v := by
  have := execRetEpilogueWord_value m a v hr
  have e : execRetEpilogueWord m a = wordOf f a := by
    simp only [execRetEpilogueWord, wordOf]
    rw [show m[a]? = some (f a) by simpa using him 0 (by omega), him 1 (by omega), him 2 (by omega),
      him 3 (by omega), him 4 (by omega), him 5 (by omega), him 6 (by omega), him 7 (by omega)]
    rfl
  rwa [e] at this

theorem ult_iff (a b : BitVec 64) : zopz0zI_u a b = true ↔ a.toNat < b.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

theorem uge_iff (a b : BitVec 64) : zopz0zKzJ_u a b = true ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt]

end VsaIris.MallocFast
