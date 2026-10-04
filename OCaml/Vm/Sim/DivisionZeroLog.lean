import OCaml.Vm.Sim.DivisionZeroNative
import OCaml.Vm.Sim.DivisionRaisePayload

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- A valid RAM exception-bucket store cannot wrap the domain pointer. -/
theorem raise_bucket_address {domain : BitVec 64} (space : WriteWindow (raiseBucket domain) 8) :
    (raiseBucket domain).toNat = domain.toNat + Layout.off_exn_bucket := by
  have lower := space.lower
  have bound := domain.isLt
  simp only [raiseBucket, BitVec.toNat_add, BitVec.toNat_ofNat, Layout.off_exn_bucket] at lower ⊢
  omega

def divisionZeroBeforeBucket (code sp env domain nativeSp value : BitVec 64) : List WEntry :=
  (divisionZeroSetupLog code sp env domain ++ raiseZeroLog nativeSp 0x80003cb0#64) ++
    raisePendingLog (raiseZeroStack nativeSp) 0x8000d1f8#64 value

/-- The complete interpreter/runtime log ends with the natural-address exception publication. -/
theorem division_zero_bucket_log {code sp env domain nativeSp value : BitVec 64} {c : Config}
    (domainWord : word c Layout.sym_Caml_state = domain)
    (space : WriteWindow (raiseBucket domain) 8) :
    divisionZeroNativeLog code sp env domain nativeSp value =
      divisionZeroBeforeBucket code sp env domain nativeSp value ++
        [((word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket, 8, value)] := by
  simp only [divisionZeroNativeLog, raiseZeroFullLog, raiseNativeLog, raiseBucketLog,
    divisionZeroBeforeBucket, List.append_assoc, raise_bucket_address space, domainWord]

/-- Read back the exception after the entire native zero path. -/
theorem division_zero_exception_word {code sp env domain nativeSp value : BitVec 64} {c : Config}
    (domainWord : word c Layout.sym_Caml_state = domain)
    (space : WriteWindow (raiseBucket domain) 8) :
    word (nativeMemoryView c (divisionZeroNativeLog code sp env domain nativeSp value))
      ((word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket) = value :=
  native_memory_last_word (division_zero_bucket_log domainWord space)

end OCaml.Vm.Sim
