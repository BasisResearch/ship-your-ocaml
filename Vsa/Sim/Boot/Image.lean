import Vsa.Sim.Boot.Log

namespace Vsa.Sim.Boot

open Vsa.MemRepr

def insertRange (m : Mem) (base : Nat) (byte : Nat → BitVec 8) : Nat → Mem
  | 0 => m
  | n + 1 => (insertRange m base byte n).insert (base + n) (byte (base + n))

theorem insertRange_get (m : Mem) (base : Nat) (byte : Nat → BitVec 8) (n x : Nat) :
    (insertRange m base byte n)[x]? =
      if base ≤ x ∧ x < base + n then some (byte x) else m[x]? := by
  induction n with
  | zero => simp [insertRange]; omega
  | succ n ih =>
    rw [insertRange, Std.ExtHashMap.getElem?_insert, ih]
    by_cases h : base + n = x
    · subst h; simp
    · simp only [beq_iff_eq, h, ↓reduceIte]
      split <;> split <;> first | rfl | omega

def inPieces (pieces : List (Nat × Nat)) (x : Nat) : Bool :=
  pieces.any fun p => decide (p.1 ≤ x ∧ x < p.1 + p.2)

def loaderMem (pieces : List (Nat × Nat)) (byte : Nat → BitVec 8) : Mem :=
  pieces.foldl (fun m p => insertRange m p.1 byte p.2) ∅

private theorem foldl_insertRange_get (pieces : List (Nat × Nat)) (byte : Nat → BitVec 8)
    (m : Mem) (x : Nat) :
    (pieces.foldl (fun m p => insertRange m p.1 byte p.2) m)[x]? =
      if inPieces pieces x then some (byte x) else m[x]? := by
  induction pieces generalizing m with
  | nil => simp [inPieces]
  | cons p ps ih =>
    rw [List.foldl_cons, ih, insertRange_get]
    simp only [inPieces, List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hp : p.1 ≤ x ∧ x < p.1 + p.2
    · simp [hp]
    · simp only [hp, false_or, ↓reduceIte]

theorem loaderMem_get (pieces : List (Nat × Nat)) (byte : Nat → BitVec 8) (x : Nat) :
    (loaderMem pieces byte)[x]? = if inPieces pieces x then some (byte x) else none := by
  rw [loaderMem, foldl_insertRange_get]
  simp

/-- Apply an ordered trace candidate to the loader memory. This definition
makes no execution or reachability claim. -/
def observedMem (initial : Mem) (L : PackedLog) : Mem := writeLog initial L.log

theorem observedMem_get {initial : Mem} {L : PackedLog} {t : RunTree}
    (h : LogOk L t) (x : Nat) :
    (observedMem initial L)[x]? = logView t (fun a => initial[a]?) x :=
  writeLog_view h initial x

end Vsa.Sim.Boot
