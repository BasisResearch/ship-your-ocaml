import Vsa.MemRepr
namespace VsaIris.Stdio

def InRange (lo hi a : Nat) : Prop := lo ≤ a ∧ a < hi

-- Generated from the relocated stdio objects; errno remains separate.
def stdioFoot (a : Nat) : Prop :=
  STDIO_RANGES

end VsaIris.Stdio
