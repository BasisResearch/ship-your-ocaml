import OCaml.Vm.Sim.SignedDivisionState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Every internal return cut, or the original return, is four-byte aligned. -/
theorem division_return_aligned (kind : DivisionKind) (x y ra : BitVec 64)
    (aligned : ra.toNat % 4 = 0) : (divisionReturn kind x y ra).toNat % 4 = 0 := by
  cases kind <;> simp only [divisionReturn] <;> split <;> first | exact aligned | decide

/-- A nonnegative nonzero divisor takes libgcc's strict-positive branch. -/
theorem division_positive_guard {y : BitVec 64} (nonzero : y ≠ 0) (positive : y.msb = false) :
    (0#64).slt y = true := by
  have bound : 0 < y.toNat := by
    have ne : y.toNat ≠ 0 := by
      intro zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact zero
    omega
  rw [BitVec.slt_eq_decide, BitVec.toInt_zero, BitVec.toInt_eq_toNat_of_msb positive]
  simpa only [decide_eq_true_eq] using (show (0 : Int) < (y.toNat : Int) by omega)

/-- One observation adapter for all eight generated normalization paths.
Only register values and the actual native frame differ between sign cases. -/
theorem division_prepared {kind : DivisionKind} {before after : Config} {x y ra : BitVec 64}
    (input : SignedDivisionInput x y ra before)
    (good : GoodState after.σ) (tick : after.tick < 2)
    (pc : pcOf after = some 0x800372a0#64)
    (ret : gpr after 1 = some (divisionReturn kind x y ra))
    (left : gpr after 10 = some (divisionMagnitude x))
    (right : gpr after 11 = some (divisionMagnitude y))
    (saved : kind = .remainder ∨ divisionNegative kind x y = true → gpr after 5 = some ra)
    (memory : after.σ.mem = before.σ.mem)
    (frame : StepFrameOut divisionPrefixWrites before.σ after.σ) :
    SignedDivisionPrepared kind before x y ra after := by
  refine {
    good := good, image := ?_, minstret := good.minstret,
    raReg := ret, aligned := division_return_aligned kind x y ra input.aligned, tick := tick,
    left := left, right := right,
    nonzero := division_magnitude_nonzero input.nonzero, pc := pc, returnAligned := input.aligned, savedReturn := saved,
    memory := memory, frame := frame }
  exact image_of_writeLog (log := []) input.image ⟨trivial, trivial⟩ memory

end OCaml.Vm.Sim
