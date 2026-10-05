import OCaml.Vm.Primitives.DoubleLayout

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- Two adjacent scalar stores initialize an OCaml pair's payload. -/
def pairLog (pointer first second : BitVec 64) : List WEntry :=
  [(pointer.toNat, 8, first), ((pointer + 8#64).toNat, 8, second)]

/-- Readback of the two fields, with later writes separated explicitly. -/
theorem pairLog_fields {before after : Config} {prefix tail : List WEntry} {pointer first second : BitVec 64}
    (memory : after.σ.mem = writeLog before.σ.mem (prefix ++ pairLog pointer first second ++ tail))
    (window : WriteWindow pointer 8)
    (outsideFirst : OutLRange tail pointer.toNat 8)
    (outsideSecond : OutLRange tail (pointer.toNat + 8) 8) :
    word after pointer.toNat = first ∧ word after (pointer.toNat + 8) = second := by
  have address := DoubleAllocation.field_address window
  have firstFrame : OutLRange [((pointer + 8#64).toNat, 8, second)] pointer.toNat 8 :=
    ⟨Or.inl (by rw [address]), True.intro⟩
  constructor
  · change bytesT after.σ.mem _ 8 = _
    rw [memory, writeLog_append, bytesT_writeLog_out _ outsideFirst, writeLog_append]
    change bytesT (writeLog (writeLog (writeLog before.σ.mem prefix)
      [(pointer.toNat, 8, first)]) [((pointer + 8#64).toNat, 8, second)]) pointer.toNat 8 = first
    rw [bytesT_writeLog_out _ firstFrame]
    exact word_writeLog _ _ _
  · change bytesT after.σ.mem _ 8 = _
    rw [memory, writeLog_append, bytesT_writeLog_out _ outsideSecond, writeLog_append]
    change bytesT (writeLog (writeLog (writeLog before.σ.mem prefix)
      [(pointer.toNat, 8, first)]) [((pointer + 8#64).toNat, 8, second)]) (pointer.toNat + 8) 8 = second
    rw [address]
    exact word_writeLog _ _ _

end OCaml.Vm.Primitives
