import Vsa.Sim.Boot.Image
import Vsa.Sim.RamReadBytes
import Vsa.Densify.Resp

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

/-- An explicitly stored byte is independent of the initial memory. -/
theorem logView_eq_of_present {t : RunTree} {x : Nat}
    (h : (t.fin x).isSome = true) (initial : Nat → Option (BitVec 8)) :
    logView t initial x = logView t (fun _ => none) x := by
  cases hf : t.fin x with
  | none => simp [hf] at h
  | some v => simp [logView, hf]

/-- Local equality of views is enough for a total read. -/
theorem viewBytes_congr {v v' : Nat → Option (BitVec 8)} {a w : Nat}
    (h : ∀ i, i < w → v (a + i) = v' (a + i)) :
    viewBytes v a w = viewBytes v' a w := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    have first := h 0 (by omega)
    simp only [Nat.add_zero] at first
    have rest : viewBytes v (a + 1) w = viewBytes v' (a + 1) w :=
      ih (fun i hi => by simpa only [Nat.add_assoc, Nat.add_comm 1] using h (i + 1) (by omega))
    simp only [viewBytes, first, rest]

/-- A read wholly covered by final stores has no initial-memory premise. -/
theorem observedMem_bytes_stored {initial : Vsa.MemRepr.Mem} {L : PackedLog}
    {t : RunTree} (h : LogOk L t) {a w : Nat}
    (stored : ∀ i : Fin w, (t.fin (a + i)).isSome = true) :
    bytesT (observedMem initial L) a w = viewBytes (logView t (fun _ => none)) a w := by
  rw [observedMem_bytes h]
  exact viewBytes_congr fun i hi => logView_eq_of_present (stored ⟨i, hi⟩) _

/-- Total reads depend only on the model's zero-equivalence of memories. -/
theorem bytesT_memEqv {m m' : Vsa.MemRepr.Mem} (h : Vsa.Densify.MemEqv m m')
    (a w : Nat) : bytesT m a w = bytesT m' a w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bytesT _ _ _ _ hk, getLsbD_bytesT _ _ _ _ hk]
  exact congrArg (fun b => b.getLsbD (k % 8)) (h (a + k / 8))

end Vsa.Sim.Boot
