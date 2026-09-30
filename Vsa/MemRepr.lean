import Vsa.Machine

namespace Vsa.MemRepr


abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

def readLE (m : Mem) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => do
    let b ← m[a]?
    let rest ← readLE m (a + 1) k
    pure (b.toNat + 256 * rest)

def read32 (m : Mem) (a : Nat) : Option Nat := readLE m a 4

def read64 (m : Mem) (a : Nat) : Option Nat := readLE m a 8

def readI64 (m : Mem) (a : Nat) : Option Int :=
  (read64 m a).map fun n => (BitVec.ofNat 64 n).toInt

inductive CStr (m : Mem) : Nat → List Char → Prop where
  | nil {a : Nat} : m[a]? = some 0 → CStr m a []
  | cons {a : Nat} {b : BitVec 8} {cs : List Char} :
    m[a]? = some b → b ≠ 0 → b.toNat < 128 →
    CStr m (a + 1) cs →
    CStr m a (Char.ofNat b.toNat :: cs)

def CString (m : Mem) (a : Nat) (s : String) : Prop :=
  ∃ cs, CStr m a cs ∧ s = String.ofList cs

end Vsa.MemRepr
