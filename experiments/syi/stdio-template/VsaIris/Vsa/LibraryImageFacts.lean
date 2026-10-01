import VsaIris.Vsa.SymData
import VsaIris.Vsa.SymHavoc
import VsaIris.Vsa.LibraryStepTac
import VsaIris.Vsa.BvLits
namespace VsaIris.Interp
open Vsa.MemRepr Vsa.Sim VsaIris.Sym VsaIris.MallocFast
def imgLE (img : Nat → BitVec 8) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (img a).toNat + 256 * imgLE img (a + 1) n

def imgW (img : Nat → BitVec 8) (a : Nat) : BitVec 64 := BitVec.ofNat 64 (imgLE img a 8)

theorem imgLE_lt (img : Nat → BitVec 8) (a : Nat) : ∀ n, imgLE img a n < 256 ^ n
  | 0 => by simp [imgLE]
  | n + 1 => by
    have := imgLE_lt img (a + 1) n
    have hb := (img a).isLt
    simp only [imgLE, Nat.pow_succ]
    omega

theorem imgW_toNat (img : Nat → BitVec 8) (a : Nat) : (imgW img a).toNat = imgLE img a 8 := by
  unfold imgW
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using imgLE_lt img a 8)]

def memImg (m : Mem) : Nat → BitVec 8 := fun k => (m[k]?).getD 0

theorem memImg_eq {m : Mem} {k : Nat} {b : BitVec 8} (h : m[k]? = some b) :
    memImg m k = b := by simp [memImg, h]

theorem readLE_succ {m : Mem} {n a v : Nat} (h : readLE m a (n + 1) = some v) :
    ∃ b rest, m[a]? = some b ∧ readLE m (a + 1) n = some rest ∧ v = b.toNat + 256 * rest := by
  have h' : (m[a]?).bind
      (fun b => (readLE m (a + 1) n).bind (fun rest => some (b.toNat + 256 * rest))) = some v := h
  simp only [Option.bind_eq_some_iff] at h'
  obtain ⟨b, hb, rest, hr, hv⟩ := h'
  exact ⟨b, rest, hb, hr, (Option.some.inj hv).symm⟩

theorem readLE_memImg {m : Mem} : ∀ {n a v : Nat}, readLE m a n = some v →
    imgLE (memImg m) a n = v
  | 0, _, _, h => by simpa [imgLE] using Option.some.inj h
  | n + 1, a, v, h => by
    obtain ⟨b, rest, hb, hrest, hv⟩ := readLE_succ h
    rw [imgLE, memImg_eq hb, readLE_memImg (m := m) (n := n) (a := a + 1) hrest, hv]

theorem imgLE_inj {f g : Nat → BitVec 8} :
    ∀ {n a : Nat}, imgLE f a n = imgLE g a n → ∀ j, j < n → f (a + j) = g (a + j)
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, a, h, j, hj => by
    simp only [imgLE] at h
    have hf := (f a).isLt; have hg := (g a).isLt
    have h0 : (f a).toNat = (g a).toNat := by omega
    have h1 : imgLE f (a + 1) n = imgLE g (a + 1) n := by omega
    rcases j with _ | j
    · exact BitVec.eq_of_toNat_eq h0
    · have := imgLE_inj h1 j (by omega)
      rwa [show a + 1 + j = a + (j + 1) by omega] at this

theorem imgLE_imgM_store (Mt : Mem) (a : Nat) (w : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 8, w)])) a 8 = w.toNat :=
  readLE_memImg (read64_store_hit Mt a w)

theorem imgM_store_img {Mt : Mem} {a : Nat} {img : Nat → BitVec 8} {j : Nat} (hj : j < 8) :
    imgM (writeLog Mt [(a, 8, imgW img a)]) (a + j) = img (a + j) := by
  refine imgLE_inj (n := 8) ?_ j hj
  rw [imgLE_imgM_store, imgW_toNat]

theorem bytesAt8 (f : Nat → BitVec 8) (a : Nat) :
    bytesAt f a 8 = [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6),
      f (a + 7)] := rfl

theorem toNat_append8 (f : Nat → BitVec 8) (a : Nat) :
    (((((((((f (a + 7)).append (f (a + 6))).append (f (a + 5))).append (f (a + 4))).append
      (f (a + 3))).append (f (a + 2))).append (f (a + 1))).append (f a)) : BitVec (8 * 8)).toNat =
      imgLE f a 8 := by
  simp only [BitVec.append_eq, BitVec.toNat_append, imgLE]
  have h0 := (f a).isLt; have h1 := (f (a + 1)).isLt; have h2 := (f (a + 2)).isLt
  have h3 := (f (a + 3)).isLt; have h4 := (f (a + 4)).isLt; have h5 := (f (a + 5)).isLt
  have h6 := (f (a + 6)).isLt; have h7 := (f (a + 7)).isLt
  simp only [show a + 1 + 1 = a + 2 by omega, show a + 2 + 1 = a + 3 by omega,
    show a + 3 + 1 = a + 4 by omega, show a + 4 + 1 = a + 5 by omega,
    show a + 5 + 1 = a + 6 by omega, show a + 6 + 1 = a + 7 by omega]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem ldvf_ld_imgLE {f : Nat → BitVec 8} {a k : Nat} (h : imgLE f a 8 = k) :
    ldvf .ld f a = BitVec.ofNat 64 k := by
  have hw := toNat_append8 f a
  rw [h] at hw
  simp only [ldvf, bytesAt8, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  have hk : k < 2 ^ 64 := by have := imgLE_lt f a 8; omega
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, ← hw]
  exact congrArg BitVec.toNat (BitVec.signExtend_eq _)

theorem sext32_ofNat_toInt {a : Nat} (h : a < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a))).toInt = a := by
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  have e : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a)).toNat = a := by
    simp [BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]; omega
  rw [BitVec.toInt_eq_toNat_cond, e]; simp; omega

theorem ofNat_toInt_small {a : Nat} (h : a < 2 ^ 31) : (BitVec.ofNat 64 a).toInt = a := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

theorem sext32_ofNat_eq {a : Nat} (h : a < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a)) = BitVec.ofNat 64 a :=
  BitVec.eq_of_toInt_eq (by rw [sext32_ofNat_toInt h, ofNat_toInt_small h])

end VsaIris.Interp
namespace VsaIris.VsaHeap
theorem toNat_and_m8 (x : BitVec 64) : (x &&& 18446744073709551608#64).toNat = x.toNat / 8 * 8 := by
  rw [show (18446744073709551608#64 : BitVec 64) = BitVec.allOnes 64 <<< 3 by decide,
    VsaIris.MallocFast.and_high_toNat x 3 (by decide)]

end VsaIris.VsaHeap
