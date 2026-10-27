import OCaml.Vm.Primitives.ByteCopyLog

namespace OCaml.Vm.Primitives.StringCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris

/-- The shared native allocation/copy post supplies the complete represented
byte object, including initialized bytes, header and canonical padding. -/
theorem CopyPostAt.object {log dst live ra sp a g before after pl cp} {b : List UInt8}
    (post : CopyPostAt log dst live ra sp a b.length g before after)
    (source : ∀ i x, b[i]? = some x → g (a + i) = BitVec.ofNat 8 x.toNat) :
    ObjAt after pl cp dst.toNat (.bytes b) := by
  apply post.shell.object
  intro i x hi
  exact (post.bytes i (List.getElem?_eq_some_iff.mp hi).1).trans (source i x hi)

/-- The same native post supplies the canonical equality representation. -/
theorem CopyPostAt.padded {log dst live ra sp a g before after} {b : List UInt8}
    (post : CopyPostAt log dst live ra sp a b.length g before after)
    (source : ∀ i x, b[i]? = some x → g (a + i) = BitVec.ofNat 8 x.toNat) :
    PaddedString after dst.toNat b := by
  apply post.shell.padded
  intro i x hi
  exact (post.bytes i (List.getElem?_eq_some_iff.mp hi).1).trans (source i x hi)

/-- Caller-owned source bytes survive the whole allocation/copy when the
explicit stores and destination are separated from that source. -/
theorem CopyPostAt.source {log dst live ra sp a len g before after}
    (post : CopyPostAt log dst live ra sp a len g before after)
    (allocationOutside : ∀ i, i < len → OutL log (a + i))
    (copyOutside : ∀ i, i < len → ¬ InExt (dst.toNat, len) (a + i)) :
    ∀ i, i < len → byte after (a + i) = byte before (a + i) := by
  intro i hi
  rw [post.memory _ (copyOutside i hi), writeLog_out _ _ _ (allocationOutside i hi), byte_total]

end OCaml.Vm.Primitives.StringCopy
