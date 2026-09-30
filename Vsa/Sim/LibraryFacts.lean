import Vsa.Sim.DivSites2
import Vsa.Sim.StrcpySites
import Vsa.Sim.ValueSites
import Vsa.Sim.StrlenSpec
import Vsa.Sim.ExecuteStore

/-! Generic copy invariants extracted from syi 46b1eb8e StrcpySpec/SnprintfSpec5.
The byte-copy invariant has no function-address assumptions. -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
namespace Vsa.Sim
theorem getElem_insert_ne (mem : Std.ExtHashMap Nat (BitVec 8)) (i j : Nat) (v : BitVec 8)
    (hne : (j == i) = false) : (mem.insert j v)[i]? = mem[i]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]

theorem getElem_insert_self (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (v : BitVec 8) :
    (mem.insert i v)[i]? = some v := by
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by simp)]

theorem sext64_id (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

/- The 8-byte LE reconstruction equals the `toNat` of the assembled word
(same technique as `ValueTruthySpec.word8_toNat_recon`, inlined to avoid importing
that file). -/

theorem word8_recon_env (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/- The `ld` at a spill slot recovers the spilled value: sign-extending the LE
reassembly of the 8 `writeMap8 (sdData_val v)` bytes gives `v`. -/


structure CpyInv (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  copied : ∀ k, k < i → mem[(dst.toNat + k)]? = some (bs k)
  outside : ∀ a, (a < dst.toNat ∨ dst.toNat + len < a) → mem[a]? = m0[a]?
  src_intact : ∀ k, i ≤ k → k ≤ len → mem[(src.toNat + k)]? = m0[(src.toNat + k)]?

/- **Store preserves the copied-prefix invariant** (disjointness-only form,
shared with the `memmove` byte loop in `SnprintfSpec18`). Storing byte `bs i` at
`dst + i` (`i ≤ len`) re-establishes `CpyInv … (i+1)` for `mem.insert (dst+i) (bs i)`. -/

theorem cpyinv_store' (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hdisj : dst.toNat + len + 1 ≤ src.toNat ∨ src.toNat + len + 1 ≤ dst.toNat) (hi : i ≤ len)
    (hinv : CpyInv dst src len bs i m0 mem) :
    CpyInv dst src len bs (i + 1) m0 (mem.insert (dst.toNat + i) (bs i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hik : k = i
    · subst hik; simp only [beq_self_eq_true, if_true]
    · have hne : ((dst.toNat + i) == (dst.toNat + k)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
      exact hinv.copied k (by omega)
  · intro a ha
    rw [Std.ExtHashMap.getElem?_insert]
    have hne : ((dst.toNat + i) == a) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv.outside a ha
  · intro k hik hkn
    rw [Std.ExtHashMap.getElem?_insert]
    have hne : ((dst.toNat + i) == (src.toNat + k)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      rcases hdisj with hd | hd <;> omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv.src_intact k (by omega) hkn

/- `cpyinv_store` with the disjointness taken from `CpyRegions`. -/

theorem sub1_bv_sn5 (v : BitVec 64) (h1 : 1 ≤ v.toNat) :
    (v + sign_extend (m := 64) (0xfff#12)) = BitVec.ofNat 64 (v.toNat - 1) := by
  have hlt := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,
    show (sign_extend (m := 64) (0xfff#12) : BitVec 64).toNat = 2 ^ 64 - 1 from by decide,
    BitVec.toNat_ofNat]
  omega

/- Machine `umod` by 10 is `Nat` mod: `w % 10#64 = ofNat (w.toNat % 10)`. -/

theorem getElem?_writeMap8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 8)) (a : Nat) (ha : a < k ∨ k + 8 ≤ a) :
    (writeMap8 mem k d)[a]? = mem[a]? := by
  show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
    (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem stData_zext (b : BitVec 8) :
    stData 1 (zero_extend (m := 64) (b : BitVec (8*1))) = (b : BitVec (8*1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [stData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have hlt : (b : BitVec 8).toNat < 2^8 := b.isLt
  rw [BitVec.toNat_ofNat]
  generalize hE : ((((1:Nat) : Int) * 8 - 1).toNat - 0 + 1) = E
  have hE8 : E = 8 := by rw [← hE]; decide
  subst hE8
  have hp : (2:Nat)^(8*1) = 2^8 := by decide
  rw [hp, Nat.mod_eq_of_lt (show (b:BitVec 8).toNat < 2^64 from by omega),
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

/- `sbAddr (base + ofNat (i+1))` via the site's raw `+ sext 0xfff`: `= base + ofNat i`. -/

theorem sbAddr_succ_raw (base : BitVec 64) (i : Nat) :
    (base + BitVec.ofNat 64 (i + 1)) + sign_extend (m := 64) (0xfff#12) = base + BitVec.ofNat 64 i := by
  have := sbAddr_succ base i
  simpa only [sbAddr] using this

theorem word_toNat_recon (b0 b1 b2 b3 : BitVec 8) :
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt
  have h1 := b1.isLt
  have h2 := b2.isLt
  have h3 := b3.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem sext_word_small (w : BitVec (8 * 4)) (k : Nat) (hk : k < 128) (hw : w.toNat = k) :
    (sign_extend (m := 64) w : BitVec 64) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have hlt : w.toNat < 2 ^ 32 := w.isLt
  have hmsb : w.msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, hmsb, Bool.false_eq_true, if_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega), hw, Nat.mod_eq_of_lt (by omega)]

theorem getElem_writeMap4_0 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a]? = some (d.extractLsb' 0 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap4_1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 1]? = some (d.extractLsb' 8 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_self]

theorem getElem_writeMap4_2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 2]? = some (d.extractLsb' 16 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap4_3 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap4]
  rw [getElem_insert_self]

theorem getElem_writeMap8_0 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a]? = some (d.extractLsb' 0 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 1]? = some (d.extractLsb' 8 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 2]? = some (d.extractLsb' 16 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_3 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 4]? = some (d.extractLsb' 32 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_5 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 5]? = some (d.extractLsb' 40 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_6 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 6]? = some (d.extractLsb' 48 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_7 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 7]? = some (d.extractLsb' 56 8) := by
  simp only [writeMap8]
  rw [getElem_insert_self]

theorem getElem_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 k : Nat)
    (d : BitVec (8 * 8)) (hk : k < a8 ∨ a8 + 8 ≤ k) :
    (writeMap8 mem a8 d)[k]? = mem[k]? := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

theorem sp_sub64 (sp : BitVec 64) :
    (sp + sign_extend (m := 64) (0xfc0#12)) = sp - 64#64 := by
  have hs : (sign_extend (m := 64) (0xfc0#12) : BitVec 64) = -(64#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hn : (-(64#64) : BitVec 64).toNat = 2^64 - 64 := by decide
  have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
  rw [hn, h64]; have := sp.isLt; omega

/- `(sp - 64) + sext 0x040 = sp` (the epilogue `addi sp,sp,64` restore). -/

theorem sp_restore64 (sp : BitVec 64) :
    (sp - 64#64) + sign_extend (m := 64) (0x040#12) = sp := by
  have hs : (sign_extend (m := 64) (0x040#12) : BitVec 64) = 64#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
  rw [h64]; have := sp.isLt; omega

/- `(sp - 64).toNat = sp.toNat - 64` when `64 ≤ sp.toNat`. -/

theorem sp_sub64_toNat (sp : BitVec 64) (h : 64 ≤ sp.toNat) :
    (sp - 64#64).toNat = sp.toNat - 64 := by
  have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
  rw [BitVec.toNat_sub, h64]
  have := sp.isLt
  omega

theorem off_ed_00 (base : BitVec 64) :
    (base + sign_extend (m := 64) (0x000#12)).toNat = base.toNat := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

/- `base + sext 0x008 = base + 8` (no wrap). -/

theorem off_ed_28 (base : BitVec 64) (h : base.toNat + 40 < 2^64) :
    (base + sign_extend (m := 64) (0x028#12)).toNat = base.toNat + 40 := by
  have hs : (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 := by decide
  rw [BitVec.toNat_add, hs]; omega

/- `base + sext 0x030 = base + 48` (no wrap). -/

theorem off_ed_30 (base : BitVec 64) (h : base.toNat + 48 < 2^64) :
    (base + sign_extend (m := 64) (0x030#12)).toNat = base.toNat + 48 := by
  have hs : (sign_extend (m := 64) (0x030#12) : BitVec 64).toNat = 48 := by decide
  rw [BitVec.toNat_add, hs]; omega

/- `base + sext 0x038 = base + 56` (no wrap). -/

theorem off_ed_38 (base : BitVec 64) (h : base.toNat + 56 < 2^64) :
    (base + sign_extend (m := 64) (0x038#12)).toNat = base.toNat + 56 := by
  have hs : (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 := by decide
  rw [BitVec.toNat_add, hs]; omega

theorem sdData_toNat (v : BitVec 64) : (sdData_val v).toNat = v.toNat := by
  simp only [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftRight_zero]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have key : ∀ W : Nat, (2:Nat) ^ W = 2 ^ 64 → (BitVec.ofNat W v.toNat).toNat = v.toNat := by
    intro W hW; rw [BitVec.toNat_ofNat, hW, Nat.mod_eq_of_lt hv]
  exact key _ (by decide)

theorem sext_reassemble (v : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : b0 = (sdData_val v).extractLsb' 0 8) (h1 : b1 = (sdData_val v).extractLsb' 8 8)
    (h2 : b2 = (sdData_val v).extractLsb' 16 8) (h3 : b3 = (sdData_val v).extractLsb' 24 8)
    (h4 : b4 = (sdData_val v).extractLsb' 32 8) (h5 : b5 = (sdData_val v).extractLsb' 40 8)
    (h6 : b6 = (sdData_val v).extractLsb' 48 8) (h7 : b7 = (sdData_val v).extractLsb' 56 8) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = v := by
  rw [sext64_id]
  apply BitVec.eq_of_toNat_eq
  rw [word8_recon_env]
  subst h0 h1 h2 h3 h4 h5 h6 h7
  have hv : (sdData_val v).toNat = v.toNat := sdData_toNat v
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, hv]
  have := v.isLt
  omega

/- `mv rd,rs` folds `v + sext 0 = v`. -/

theorem getElem_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 k : Nat)
    (d : BitVec (8 * 4)) (hk : k < a4 ∨ a4 + 4 ≤ k) :
    (writeMap4 mem a4 d)[k]? = mem[k]? := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

end Vsa.Sim
