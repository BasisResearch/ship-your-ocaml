import Vsa.MemRepr

namespace Vsa.Sim



def physSize (n : Nat) : Nat := max 32 (16 * ((n + 8 + 15) / 16))

theorem physSize_mono {m n : Nat} (h : m ≤ n) : physSize m ≤ physSize n := by
  unfold physSize
  omega

theorem physSize_min (n : Nat) : 32 ≤ physSize n := Nat.le_max_left _ _

def physTotal (exts : List (Nat × Nat)) : Nat :=
  (exts.map (fun e => physSize e.2)).sum

def roundUp16 (n : Nat) : Nat := (n + 15) / 16 * 16

end Vsa.Sim
