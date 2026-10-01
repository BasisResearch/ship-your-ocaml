import OCaml.Vm.Primitives.DoubleFast
import OCaml.Vm.Primitives.Allocation

namespace OCaml.Vm.Primitives.DoubleAllocation
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- The allocated header's RAM bound rules out address wrap at field zero. -/
theorem field_address {header : BitVec 64} (window : WriteWindow header 8) :
    (header + 8#64).toNat = header.toNat + 8 := by
  rw [BitVec.toNat_add]
  change (header.toNat + 8) % 18446744073709551616 = header.toNat + 8
  apply Nat.mod_eq_of_lt
  have bound := window.upper
  omega

/-- The first-order nursery write log contains a correctly tagged double
header and its unchanged 64-bit payload. -/
theorem double_layout {c after : Config} {domain young bits : BitVec 64} {pl : Place} {cp : ChanPlace}
    (window : WriteWindow (young - 16#64) 8)
    (memory : after.σ.mem = writeLog c.σ.mem (allocationLog domain young bits)) :
    ObjAt after pl cp ((young - 16#64).toNat + 8) (.double bits) := by
  have addr := field_address window
  have separate : OutLRange [((young - 16#64 + 8#64).toNat, 8, bits)] (young - 16#64).toNat 8 :=
    ⟨Or.inl (by rw [addr]; exact Nat.le_refl _), True.intro⟩
  have header : word after (young - 16#64).toNat = 1277#64 := by
    change bytesT after.σ.mem _ 8 = _
    rw [memory, allocationLog, initializeLog, writeLog_append, writeLog_append]
    rw [bytesT_writeLog_out _ separate]
    exact word_writeLog _ _ _
  have data : word after ((young - 16#64).toNat + 8) = bits := by
    change bytesT after.σ.mem _ 8 = _
    rw [memory, allocationLog, initializeLog, writeLog_append, writeLog_append, addr]
    exact word_writeLog _ _ _
  change HeaderOk (word after ((young - 16#64).toNat + 8 - 8)) 1 doubleTag ∧ _
  rw [Nat.add_sub_cancel, header]
  exact ⟨by unfold HeaderOk doubleTag; decide, data⟩

end OCaml.Vm.Primitives.DoubleAllocation
