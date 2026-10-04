import OCaml.Vm.Sim.Udivdi3
import OCaml.Vm.Sim.FramePins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

inductive DivisionKind where
  | quotient | remainder
  deriving DecidableEq

def divisionMagnitude {w : Nat} (x : BitVec w) : BitVec w := if x.msb then -x else x

def divisionNegative {w : Nat} (kind : DivisionKind) (x y : BitVec w) : Bool :=
  match kind with
  | .quotient => x.msb != y.msb
  | .remainder => x.msb

def divisionResult {w : Nat} (kind : DivisionKind) (x y : BitVec w) : BitVec w :=
  match kind with
  | .quotient => x.sdiv y
  | .remainder => x.srem y

def divisionUnsigned {w : Nat} (kind : DivisionKind) (x y : BitVec w) : BitVec w :=
  match kind with
  | .quotient => divisionMagnitude x / divisionMagnitude y
  | .remainder => divisionMagnitude x % divisionMagnitude y

def divisionReturn (kind : DivisionKind) (x y ra : BitVec 64) : BitVec 64 :=
  match kind with
  | .quotient => if divisionNegative kind x y then 0x80037314#64 else ra
  | .remainder => if divisionNegative kind x y then 0x80037344#64 else 0x8003732c#64

def divisionPrefixWrites : List Register := [Register.x1, Register.x5, Register.x10, Register.x11] ++ noiseRegs

def divisionWrites : List Register :=
  [Register.x1, Register.x5, Register.x10, Register.x11, Register.x12, Register.x13] ++ noiseRegs

/-- Nonzero signed operands use the common binary-library entry contract. -/
structure SignedDivisionInput (x y ra : BitVec 64) (c : Config) : Prop
    extends BinaryLibInput x y ra c where
  nonzero : y ≠ 0

/-- Exact native normalization boundary before the shared unsigned core. -/
structure SignedDivisionPrepared (kind : DivisionKind) (before : Config) (x y ra : BitVec 64)
    (after : Config) : Prop
    extends Udivdi3Input (divisionMagnitude x) (divisionMagnitude y) (divisionReturn kind x y ra) after where
  pc : pcOf after = some 0x800372a0#64
  returnAligned : ra.toNat % 4 = 0
  savedReturn : kind = .remainder ∨ divisionNegative kind x y = true → gpr after 5 = some ra
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut divisionPrefixWrites before.σ after.σ

/-- A signed wrapper's complete return observations. -/
structure SignedDivisionPost (before : Config) (ra value : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut divisionWrites before.σ after.σ

/-- The absolute divisor is nonzero even for the most-negative native word. -/
theorem division_magnitude_nonzero {x : BitVec 64} (nonzero : x ≠ 0) : divisionMagnitude x ≠ 0 := by
  unfold divisionMagnitude
  split
  · intro zero
    apply nonzero
    have h := congrArg Neg.neg zero
    simpa only [BitVec.neg_neg, show -(0 : BitVec 64) = 0 from rfl] using h
  · exact nonzero

/-- Both signed operations reuse the unsigned core and their respective sign fixup. -/
theorem division_result_sign {w : Nat} (kind : DivisionKind) (x y : BitVec w) :
    divisionResult kind x y =
      if divisionNegative kind x y then -(divisionUnsigned kind x y) else divisionUnsigned kind x y := by
  cases kind <;> cases hx : x.msb <;> cases hy : y.msb <;>
    simp [divisionResult, divisionNegative, divisionUnsigned, divisionMagnitude, BitVec.sdiv_eq, BitVec.srem_eq, hx, hy]

end OCaml.Vm.Sim
