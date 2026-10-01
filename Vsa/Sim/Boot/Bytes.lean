import Vsa.Sim.Boot.Image
import Vsa.Sim.RamReadBytes

/-! Total byte reads through a certified memory view. -/
namespace Vsa.Sim.Boot

/-- The same little-endian total read as `bytesT`, on a functional view. -/
def viewBytes (v : Nat → Option (BitVec 8)) (a : Nat) : (w : Nat) → BitVec (8 * w)
  | 0 => 0#0
  | w + 1 => ((viewBytes v (a + 1) w).append ((v a).getD 0)).cast (by omega)

/-- Read projection, independent of the size or construction of the memory map. -/
theorem bytesT_view {m : Std.ExtHashMap Nat (BitVec 8)} {v : Nat → Option (BitVec 8)}
    (h : ∀ x, m[x]? = v x) (a w : Nat) : bytesT m a w = viewBytes v a w := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih => simp only [bytesT, viewBytes, h, ih]

/-- A checked packed log supplies all total reads from its compact final view. -/
theorem observedMem_bytes {initial : Vsa.MemRepr.Mem} {L : PackedLog} {t : RunTree}
    (h : LogOk L t) (a w : Nat) :
    bytesT (observedMem initial L) a w = viewBytes (logView t (fun x => initial[x]?)) a w :=
  bytesT_view (observedMem_get h) a w

end Vsa.Sim.Boot
