import Vsa.Sim.ExecuteAlu

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace Vsa.Sim

/-- One comparison family for the reflected signed and unsigned instructions. -/
def compareOp (unsigned : Bool) : rop := if unsigned then .SLTU else .SLT

def compareValue (unsigned : Bool) (a b : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (if unsigned then zopz0zI_u a b else zopz0zI_s a b))

/-- Both comparisons share the same register effect and frame argument;
only the existing Sail execution equation differs. -/
theorem execute_compare_char (unsigned : Bool) (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (compareValue unsigned v1 v2)).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, compareOp unsigned))).run σ =
      .ok RETIRE_SUCCESS σ' := by
  cases unsigned with
  | false => exact execute_rtype_slt_char rs2 rs1 rd v1 v2 σ σ' hrs1 hrs2 hwr
  | true => exact execute_rtype_sltu_char rs2 rs1 rd v1 v2 σ σ' hrs1 hrs2 hwr

end Vsa.Sim
