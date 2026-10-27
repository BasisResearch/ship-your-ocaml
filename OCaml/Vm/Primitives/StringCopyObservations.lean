import OCaml.Vm.Primitives.StringCopyMachine

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim VsaIris

/-- Complete byte view shared by the scanned and explicit-length producers. -/
def copyMemoryAt (log : List WEntry) (dst : BitVec 64) (before : Config)
    (a len : Nat) (g : Nat → BitVec 8) (x : Nat) : BitVec 8 :=
  if dst.toNat ≤ x ∧ x < dst.toNat + len then g (a + (x - dst.toNat))
  else ((writeLog before.σ.mem log)[x]?).getD 0

/-- Footprint only: the final entry describes memcpy's payload extent; its
value is irrelevant and is never asserted to be an actual scalar store. -/
def copyFootprint (ra sp : BitVec 64) (a len : Nat) (domain young : BitVec 64) : List WEntry :=
  allocationLog ra sp a len domain young ++ [((resultWord young len).toNat, len, 0)]

/-- Fully determined byte observations after the allocation and copy. -/
def copyMemory (before : Config) (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young : BitVec 64) (x : Nat) : BitVec 8 :=
  copyMemoryAt (allocationLog ra sp a len domain young) (resultWord young len) before a len g x

/-- Split a footprint independently of the values written in either part. -/
theorem outL_append_iff (left right : List WEntry) (x : Nat) :
    OutL (left ++ right) x ↔ OutL left x ∧ OutL right x := by
  induction left with
  | nil => simp [OutL]
  | cons entry rest ih => simp only [List.cons_append, OutL, ih, and_assoc]

theorem CopyPostAt.footprint {log dst live ra sp a len g before after}
    (post : CopyPostAt log dst live ra sp a len g before after) :
    ∀ x, OutL (log ++ [(dst.toNat, len, 0)]) x → byte after x = byte before x := by
  intro x outside
  obtain ⟨allocation, copied⟩ := (outL_append_iff log
    [(dst.toNat, len, 0)] x).mp outside
  have notCopied : ¬ InExt (dst.toNat, len) x := by
    obtain ⟨either, _⟩ := copied
    change x < dst.toNat ∨ dst.toNat + len ≤ x at either
    intro inside
    obtain ⟨low, high⟩ := inside
    rcases either with low' | high' <;> omega
  rw [post.memory x notCopied, writeLog_out _ _ _ allocation, byte_total]

theorem CopyPostAt.memory_complete {log dst live ra sp a len g before after}
    (post : CopyPostAt log dst live ra sp a len g before after) :
    ∀ x, byte after x = copyMemoryAt log dst before a len g x := by
  intro x
  by_cases owned : InExt (dst.toNat, len) x
  · have owned' : dst.toNat ≤ x ∧ x < dst.toNat + len := owned
    rw [copyMemoryAt, if_pos owned']
    obtain ⟨low, high⟩ := owned
    have address : dst.toNat + (x - dst.toNat) = x := by omega
    simpa only [address] using post.bytes (x - dst.toNat) (by omega)
  · have owned' : ¬ (dst.toNat ≤ x ∧ x < dst.toNat + len) := owned
    rw [copyMemoryAt, if_neg owned']
    exact post.memory x owned

theorem CopyPost.footprint {live ra sp a len g domain young before after}
    (post : CopyPost live ra sp a len g domain young before after) :
    ∀ x, OutL (copyFootprint ra sp a len domain young) x → byte after x = byte before x :=
  CopyPostAt.footprint post

theorem CopyPost.memory_complete {live ra sp a len g domain young before after}
    (post : CopyPost live ra sp a len g domain young before after) :
    ∀ x, byte after x = copyMemory before ra sp a len g domain young x :=
  CopyPostAt.memory_complete post

end OCaml.Vm.Primitives.StringCopy
