import OCaml.Vm.Gc.CustomMem

/-! Exact integer targets for round-to-nearest/ties-to-even positive binary64
resource arithmetic in this finite G1 path. Native __floatundidf/__divdf3/
__adddf3/__gedf2 execution is still owed by CustomMemCall; these definitions
and finite facts do not constitute those machine summaries. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false

/-- Exact parameter arithmetic at the observed input values. The minor
ratio divides bytes by 100 before multiplying, as in custom.c. This does not
assert the native helper executions. -/
theorem custom_resource_parameters :
    min channelMem.toNat 8192 = 8192 ∧ channelMem.toNat - 8192 = 57424 ∧
    (0x1f000 * 8 / 150) * 44 = 297968 ∧
    (0x40000 * 8 / 100) * 100 = 2097100 := by decide +kernel

/-- Integer quotient rounded to nearest, with ties to even. -/
def roundEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if den < 2 * r ∨ (den = 2 * r ∧ q % 2 = 1) then q + 1 else q

/-- Positive normal binary64 target for the small nonnegative rationals used
below. The zero case is positive zero; all used exponents are checked below. -/
def resourceRound (num den : Nat) : Nat :=
  if num = 0 then 0 else
  let k := den.log2 - num.log2
  let k := if num * 2 ^ k < den then k + 1 else k
  (1022 - k) * 2 ^ 52 + roundEven (num * 2 ^ (52 + k)) den

/-- Add a rounded ratio to an existing positive normal target; the existing
word is decoded as an exact dyadic rational before the next rounding. -/
def resourceAdd (bits num den : Nat) : Nat :=
  if bits = 0 then resourceRound num den else
  let exponent := bits / 2 ^ 52
  let mantissa := bits % 2 ^ 52 + 2 ^ 52
  let scale := 2 ^ (1075 - exponent)
  resourceRound (mantissa * den + num * scale) (scale * den)

/-- The ratios are rounded before addition, just as the actual soft-double
call sequence does. Integer casts of these small operands are exact. -/
def resourceNext (bits num den : Nat) : Nat :=
  let ratio := resourceRound num den
  let exponent := ratio / 2 ^ 52
  resourceAdd bits (ratio % 2 ^ 52 + 2 ^ 52) (2 ^ (1075 - exponent))

def majorResourceBits : Nat → Nat
  | 0 => 0
  | n + 1 => resourceNext (majorResourceBits n) 57424 297968

def minorResourceBits : Nat → Nat
  | 0 => 0
  | n + 1 => resourceNext (minorResourceBits n) 8192 2097100

/-- Kernel-checked finite target bounds. Bit order equals numeric order for
these positive normal encodings; no native comparison execution is asserted. -/
theorem resource_targets_below_one : ∀ n : Fin 6,
    majorResourceBits n.val < 0x3ff0000000000000 ∧
    minorResourceBits n.val < 0x3ff0000000000000 := by decide +kernel

/-- The sixth major target crosses one; this is separate from native code. -/
theorem resource_target_six : 0x3ff0000000000000 < majorResourceBits 6 := by decide +kernel

end OCaml.Vm.Gc
