import Vsa.Machine
import Vsa.Sim.Boot.Image
open Vsa.MemRepr
namespace Vsa.Sim.Boot
/-- The byte-array loader used inside the frozen emulator's initializeMemory. -/
def loadPiece (mem : Mem) (base : Nat) (body : Array UInt8) : Mem :=
  (Array.zip (Array.range' base body.size) body).foldl (fun mem (addr, byte) =>
    if mem.contains addr then panic s!"Address {addr} is already written to!"
    else mem.insert addr byte.toBitVec) mem

theorem zip_push_both {α β : Type} (xs : Array α) (ys : Array β)
    (x : α) (y : β) (size : xs.size = ys.size) :
    (xs.push x).zip (ys.push y) = (xs.zip ys).push (x, y) := by
  simp only [← Array.append_singleton, Array.zip]
  rw [Array.zipWith_append size]
  simp

theorem array_push_induction {α : Type} (P : Array α → Prop) (nil : P #[])
    (push : ∀ xs x, P xs → P (xs.push x)) (xs : Array α) : P xs := by
  have aux (ys : List α) : P ys.reverse.toArray := by
    induction ys with
    | nil => exact nil
    | cons y ys ih => simpa using push ys.reverse.toArray y ih
  simpa using aux xs.toList.reverse

/-- A nonoverlapping loader piece agrees with the existing abstract range writer. -/
theorem loadPiece_eq (m : Mem) (base : Nat) (byte : Nat → BitVec 8) (body : Array UInt8)
    (empty : ∀ i < body.size, m[base + i]? = none)
    (bytes : ∀ i (hi : i < body.size), body[i].toBitVec = byte (base + i)) :
    loadPiece m base body = insertRange m base byte body.size := by
  revert empty bytes
  induction body using array_push_induction with
  | nil => intro _ _; simp [loadPiece, insertRange]
  | push arr b ih =>
      intro empty bytes
      have oldEmpty : ∀ i < arr.size, m[base + i]? = none := by
        intro i hi; exact empty i (by simpa using Nat.lt_succ_of_lt hi)
      have oldBytes : ∀ i (hi : i < arr.size), arr[i].toBitVec = byte (base + i) := by
        intro i hi
        simpa only [Array.getElem_push_lt hi] using bytes i (by simpa using Nat.lt_succ_of_lt hi)
      have old := ih oldEmpty oldBytes
      change loadPiece m base (arr.push b) = _
      simp only [loadPiece, Array.size_push, Array.range'_1_concat, Array.append_singleton,
        zip_push_both (Array.range' base arr.size) arr (base + arr.size) b (by simp), Array.foldl_push']
      change (if (loadPiece m base arr).contains (base + arr.size) then _ else _) = _
      rw [old]
      have absent : (insertRange m base byte arr.size).contains (base + arr.size) = false := by
        rw [Std.ExtHashMap.contains_eq_isSome_getElem?, insertRange_get]
        simp [empty arr.size (by simp)]
      rw [absent]
      simp only [Bool.false_eq_true, ite_false, insertRange]
      congr 1
      simpa using bytes arr.size (by simp)
end Vsa.Sim.Boot
