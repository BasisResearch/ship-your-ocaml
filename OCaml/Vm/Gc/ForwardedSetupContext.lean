import OCaml.Vm.Gc.ForwardedInitial
import OCaml.Vm.Gc.ForwardedMemory
import OCaml.Vm.Gc.ScanSetup

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Register map established by the suffix setup block. -/
def setupResult (R : Nat → BitVec 64) (a b n : Nat) : BitVec 64 :=
  if n = 8 then scanPtr a 1 else if n = 9 then 1#64
  else if n = 18 then BitVec.ofNat 64 b - BitVec.ofNat 64 a
  else if n = 19 then BitVec.ofNat 64 b else R n

def setupCarried (R : Nat → BitVec 64) : GRegs :=
  [(2,R 2),(1,R 1),(20,R 20),(21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

theorem setup_registers {R a b count before after}
    (post : FieldCopy.SetupPost a b count before after)
    (holds : GHolds before.σ (setupCarried R)) :
    GHolds after.σ (carried (cursor (setupResult R a b) a 1 1)) := by
  have saved : GHolds after.σ (setupCarried R) := by
    apply gholds_of_frame (post.machine.frame_subset FieldCopy.setup_written) (setupCarried R)
      (by change KeysOK [2,1,20,21,22,23,24,25]; decide) ?_ ?_ holds
    · change ∀ n ∈ [2,1,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · change ∀ n ∈ [2,1,20,21,22,23,24,25], ∀ m ∈ [8,9,10,11,15,18], (gprReg m == gprReg n) = false
      decide
  exact ⟨gholds_lookup _ saved rfl, gholds_lookup _ post.scan.registers rfl,
    gholds_lookup _ post.scan.registers rfl, gholds_lookup _ saved rfl,
    gholds_lookup _ post.scan.registers rfl, gholds_lookup _ post.scan.registers rfl,
    gholds_lookup _ saved rfl, gholds_lookup _ saved rfl, gholds_lookup _ saved rfl,
    gholds_lookup _ saved rfl, gholds_lookup _ saved rfl, gholds_lookup _ saved rfl, True.intro⟩

/-- Actual suffix setup supplies the full initial forwarded-loop invariant. -/
theorem setup_initial {R domain a b count before after expected}
    (post : FieldCopy.SetupPost a b count before after)
    (data : LoopData (setupResult R a b) domain a b count 1 before expected)
    (holds : GHolds before.σ (setupCarried R))
    (code : Code.Caml_oldify_oneLoaded before.σ.mem) :
    LoopAt (setupResult R a b) a b count 1 after expected 1 after :=
  LoopAt.initial (data.memory_eq post.memory) post.scan.good post.scan.minstret post.scan.tick
    post.scan.code (post.memory ▸ code) post.scan.upper post.scan.pc (setup_registers post holds)

end OCaml.Vm.Gc.ForwardedField
