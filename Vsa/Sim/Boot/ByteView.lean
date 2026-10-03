import Vsa.Machine
namespace Vsa.Sim.Boot
/-- A byte array represented by a bounded view; proofs observe it without materializing it. -/
def bytesOfView (n : Nat) (byte : Nat → BitVec 8) : ByteArray :=
  ⟨Array.ofFn (fun i : Fin n => UInt8.ofBitVec (byte i))⟩
@[simp] theorem bytesOfView_size (n : Nat) (byte : Nat → BitVec 8) :
    (bytesOfView n byte).size = n := by simp [bytesOfView, ByteArray.size]
@[simp] theorem bytesOfView_get (n : Nat) (byte : Nat → BitVec 8) (i : Nat) (hi : i < n) :
    (bytesOfView n byte)[i]'(by simpa using hi) = UInt8.ofBitVec (byte i) := by
  simp [bytesOfView, ByteArray.getElem_eq_getElem_data]
/-- Slicing a bounded byte view is another bounded view, with no array evaluation. -/
theorem bytesOfView_extract (n : Nat) (byte : Nat → BitVec 8) (base len : Nat)
    (bound : base + len ≤ n) :
    (bytesOfView n byte).extract base (base + len) = bytesOfView len (fun i => byte (base + i)) := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, ByteArray.size_extract, bytesOfView_size]
    omega
  · intro i hi hj
    have ilen : i < len := by simpa only [ByteArray.size_data, bytesOfView_size] using hj
    have inside : base + i < n := by omega
    change ((bytesOfView n byte).extract base (base + len))[i] =
      (bytesOfView len (fun j => byte (base + j)))[i]
    rw [ByteArray.getElem_extract, bytesOfView_get n byte (base + i) inside,
      bytesOfView_get len _ i ilen]
end Vsa.Sim.Boot
