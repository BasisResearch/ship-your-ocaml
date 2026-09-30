import Vsa.Sim.LibraryFacts
import Vsa.Sim.Code.__ssprint_r

/-! Code-frame section extracted from syi 46b1eb8e SnprintfSpec9. -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim.Code (__ssprint_rLoaded)
namespace Vsa.Sim

theorem getElem?_insert_offcode_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : k < 0x8000e908 ∨ 0x8000e9f8 ≤ k) (a : Nat)
    (ha : 0x8000e908 ≤ a) (ha' : a < 0x8000e9f8) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- `__ssprint_rLoaded` survives a single insert disjoint from the code region. -/
theorem ssprint_insert_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : k < 0x8000e908 ∨ 0x8000e9f8 ≤ k) (h : __ssprint_rLoaded mem) :
    __ssprint_rLoaded (mem.insert k v) := by
  unfold __ssprint_rLoaded Vsa.Sim.Code.__ssprint_rChunk0 Vsa.Sim.Code.__ssprint_rChunk1
    Vsa.Sim.Code.__ssprint_rChunk2 Vsa.Sim.Code.__ssprint_rChunk3 at h ⊢
  simp (disch := omega) only [getElem?_insert_offcode_ss mem k v hk]
  exact h

/-- `__ssprint_rLoaded` survives a disjoint 8-byte `writeMap8` (eight inserts). -/
theorem ssprint_writeMap8_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : a + 8 ≤ 0x8000e908 ∨ 0x8000e9f8 ≤ a)
    (h : __ssprint_rLoaded mem) : __ssprint_rLoaded (writeMap8 mem a d) :=
  ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega) h)))))))

/-- `__ssprint_rLoaded` survives a disjoint 4-byte `writeMap4` (four inserts). -/
theorem ssprint_writeMap4_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 4)) (ha : a + 4 ≤ 0x8000e908 ∨ 0x8000e9f8 ≤ a)
    (h : __ssprint_rLoaded mem) : __ssprint_rLoaded (writeMap4 mem a d) :=
  ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega) h)))

end Vsa.Sim
