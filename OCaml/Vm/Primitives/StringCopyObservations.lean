import OCaml.Vm.Primitives.StringCopyMachine

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim VsaIris

/-- Footprint only: the final entry describes memcpy's payload extent; its
value is irrelevant and is never asserted to be an actual scalar store. -/
def copyFootprint (ra sp : BitVec 64) (a len : Nat) (domain young : BitVec 64) : List WEntry :=
  allocationLog ra sp a len domain young ++ [((resultWord young len).toNat, len, 0)]

/-- Fully determined byte observations after the allocation and copy. -/
def copyMemory (before : Config) (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young : BitVec 64) (x : Nat) : BitVec 8 :=
  if (resultWord young len).toNat ≤ x ∧ x < (resultWord young len).toNat + len then g (a + (x - (resultWord young len).toNat))
  else ((writeLog before.σ.mem (allocationLog ra sp a len domain young))[x]?).getD 0

/-- Split a footprint independently of the values written in either part. -/
theorem outL_append_iff (left right : List WEntry) (x : Nat) :
    OutL (left ++ right) x ↔ OutL left x ∧ OutL right x := by
  induction left with
  | nil => simp [OutL]
  | cons entry rest ih => simp only [List.cons_append, OutL, ih, and_assoc]

theorem CopyPost.footprint {live ra sp a len g domain young before after}
    (post : CopyPost live ra sp a len g domain young before after) :
    ∀ x, OutL (copyFootprint ra sp a len domain young) x → byte after x = byte before x := by
  intro x outside
  obtain ⟨allocation, copied⟩ := (outL_append_iff (allocationLog ra sp a len domain young)
    [((resultWord young len).toNat, len, 0)] x).mp outside
  have notCopied : ¬ InExt ((resultWord young len).toNat, len) x := by
    obtain ⟨either, _⟩ := copied
    change x < (resultWord young len).toNat ∨ (resultWord young len).toNat + len ≤ x at either
    intro inside
    obtain ⟨low, high⟩ := inside
    rcases either with low' | high' <;> omega
  rw [post.memory x notCopied, writeLog_out _ _ _ allocation, byte_total]

theorem CopyPost.memory_complete {live ra sp a len g domain young before after}
    (post : CopyPost live ra sp a len g domain young before after) :
    ∀ x, byte after x = copyMemory before ra sp a len g domain young x := by
  intro x
  by_cases owned : InExt ((resultWord young len).toNat, len) x
  · have owned' : (resultWord young len).toNat ≤ x ∧ x < (resultWord young len).toNat + len := owned
    rw [copyMemory, if_pos owned']
    obtain ⟨low, high⟩ := owned
    have address : (resultWord young len).toNat + (x - (resultWord young len).toNat) = x := by omega
    simpa only [address] using post.bytes (x - (resultWord young len).toNat) (by omega)
  · have owned' : ¬ ((resultWord young len).toNat ≤ x ∧ x < (resultWord young len).toNat + len) := owned
    rw [copyMemory, if_neg owned']
    exact post.memory x owned

end OCaml.Vm.Primitives.StringCopy
