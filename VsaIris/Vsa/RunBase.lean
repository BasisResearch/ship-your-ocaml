import Vsa.Alloc
import Vsa.MemRepr
import VsaIris.LocalRun

namespace VsaIris.MallocFast

open Vsa.MemRepr

def imgM (m : Mem) (a : Nat) : BitVec 8 := (m[a]?).getD 0

abbrev gpV : BitVec 64 := Vsa.Sim.LibraryLayout.gpV

abbrev roR : List (Nat × BitVec 64) := [(gp, gpV)]

end VsaIris.MallocFast
