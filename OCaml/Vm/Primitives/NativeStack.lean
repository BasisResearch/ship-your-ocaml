import OCaml.Vm.Primitives.Write

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- One saved return address in the wrapper's native stack frame. -/
def savedRaLog (sp ra : BitVec 64) : List WEntry := [((sp - 8#64).toNat, 8, ra)]

def savedRaWindows (sp : BitVec 64) : List W := [⟨(sp - 8#64).toNat, (sp - 8#64).toNat + 8⟩]

theorem native_save_address (sp : BitVec 64) : sp - 16#64 + 8#64 = sp - 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub]
  change ((18446744073709551616 - 16 + sp.toNat) % 18446744073709551616 + 8) %
    18446744073709551616 = (18446744073709551616 - 8 + sp.toNat) % 18446744073709551616
  have bound := sp.isLt
  omega

theorem savedRa_log_in (sp ra : BitVec 64) : LogInW (savedRaWindows sp) (savedRaLog sp ra) := by
  simp [savedRaWindows, savedRaLog, LogInW, InsideW]

theorem savedRa_value (c : Config) (sp ra : BitVec 64) :
    bytesT (writeLog c.σ.mem (savedRaLog sp ra)) (sp - 8#64).toNat 8 = ra :=
  word_writeLog c.σ.mem (sp - 8#64).toNat ra

end OCaml.Vm.Primitives
