import OCaml.Vm.Gc.CopyProgress

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- One shared invariant update for either concrete verbatim-copy route.
The write-set parameter preserves each route's precise native frame. -/
theorem ScanAtWith.advance {writes a b count start initial i c d}
    (h : ScanAtWith writes a b count start initial i c)
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (bound : i < count)
    (post : CopyEffect writes (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 i) c d) :
    ScanAtWith writes a b count start initial (i + 1) d := by
  have source : word c (a + 8 * i) = word initial (a + 8 * i) := by
    apply word_frame h.memory
    have separate := geometry.separate
    omega
  have sameHeader : word c (b - 8) = word initial (b - 8) := by
    apply word_frame h.memory
    exact Or.inl (by have lower := geometry.targetRange.lower; omega)
  exact h.advance_progress bound (post.progress geometry h.lower bound
    (sameHeader ▸ header) (fun _ h => h) source)

end OCaml.Vm.Gc.FieldCopy
