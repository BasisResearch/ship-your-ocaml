import OCaml.Vm.Primitives.StringCopyObservations
import Vsa.Sim.MemcpySpec

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Canonical byte-store log representing memcpy's total observations.
It models the memory effect, independently of memcpy's actual word stores. -/
def byteCopyLog (dst len : Nat) (bytes : Nat → BitVec 8) : List WEntry :=
  (List.range len).map fun i => (dst + i, 1, zero_extend (m := 64) (bytes i))

theorem byteCopyLog_succ (dst len : Nat) (bytes : Nat → BitVec 8) :
    byteCopyLog dst (len + 1) bytes = byteCopyLog dst len bytes ++
      [(dst + len, 1, zero_extend (m := 64) (bytes len))] := by
  simp [byteCopyLog, List.range_succ]

theorem byte_store_log (mem : Std.ExtHashMap Nat (BitVec 8)) (dst : Nat) (b : BitVec 8) :
    writeLog mem [(dst, 1, zero_extend (m := 64) b)] = mem.insert dst b := by
  simp [writeLog, applyW, sbData_zext]

/-- Readback of a finite byte-store log, proved by its list construction. -/
theorem byteCopyLog_observe (mem : Std.ExtHashMap Nat (BitVec 8)) (dst len : Nat)
    (bytes : Nat → BitVec 8) (x : Nat) :
    ((writeLog mem (byteCopyLog dst len bytes))[x]?).getD 0 =
      if dst ≤ x ∧ x < dst + len then bytes (x - dst) else (mem[x]?).getD 0 := by
  induction len with
  | zero =>
    have empty : ¬ (dst ≤ x ∧ x < dst + 0) := by omega
    rw [if_neg empty]
    rfl
  | succ len ih =>
    rw [byteCopyLog_succ, writeLog_append, byte_store_log, Std.ExtHashMap.getElem?_insert]
    by_cases last : dst + len = x
    · subst x
      simp [show dst ≤ dst + len ∧ dst + len < dst + (len + 1) by omega]
    · simp only [beq_iff_eq, if_neg last, ih]
      by_cases inside : dst ≤ x ∧ x < dst + len
      · rw [if_pos inside, if_pos (by omega)]
      · rw [if_neg inside, if_neg (by omega)]

namespace StringCopy

def completeLog (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young : BitVec 64) : List WEntry :=
  allocationLog ra sp a len domain young ++
    byteCopyLog (resultWord young len).toNat len (fun i => g (a + i))

/-- Full copy effects as equality of total byte observations with a finite
canonical log. No claim is made about which bytes were initially present. -/
theorem CopyPost.observed_log {live ra sp a len g domain young before after}
    (post : CopyPost live ra sp a len g domain young before after) :
    Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (completeLog ra sp a len g domain young)) := by
  intro x
  change (after.σ.mem[x]?).getD 0 = ((writeLog before.σ.mem (completeLog ra sp a len g domain young))[x]?).getD 0
  rw [completeLog, writeLog_append, byteCopyLog_observe]
  simpa only [byte_total, copyMemory] using post.memory_complete x

end StringCopy
end OCaml.Vm.Primitives
