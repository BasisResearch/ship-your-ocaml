import VsaIris.Vsa.Sbrk
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The first sbrk call starts with a zero break. The usual library geometry
is stated on the single initialization store performed by the source. -/
structure SbrkBootPre (S : Nat → Prop) (R : Nat → BitVec 64) (m : Mem) (size : Nat) : Prop where
  zero : read64 m brkAddr = some 0
  ready : SbrkPre S R (writeLog m [(brkAddr, 8, BitVec.ofNat 64 heapStart)]) heapStart size
  room : heapStart + size ≤ heapEnd

/-- The allocator's first successful morecore call uses generated instruction
steps, with no initialized-arena premise. -/
theorem sbrk_r_boot {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ allocText, live p.1) {R : Nat → BitVec 64} {Mt : Mem} {size : Nat}
    (P : SbrkBootPre S R Mt size)
    (next : ∀ R' Mt', SbrkPost R R' Mt Mt' (heapStart + size) →
      R' 10 = BitVec.ofNat 64 heapStart → AW live S Q (R 1) R' Mt') :
    AW live S Q 0x80042454#64 R Mt := by
  have hbrk := P.zero
  have hlo := P.ready.sp_lo
  have hhi := P.ready.sp_hi
  have hal := P.ready.sp_al
  have hra := P.ready.ra_al
  have ho1 := P.ready.off1
  have ho2 := P.ready.off2
  have hsize := P.ready.a1
  have room := P.room
  have own := P.ready
  unfold Vsa.Sim.tohostAddr Vsa.Sim.LibraryLayout.tohostAddr at hlo
  unfold heapStart heapEnd at room
  unfold brkAddr at hbrk
  sx_run [16] hlive at 0x80001c90
  simp (disch := decide) only [ldv_at hbrk]
  sx_run [20] hlive at 0x80001cd0
  have sum : (BitVec.ofNat 64 heapStart + R 11).toNat = heapStart + size := by
    rw [BitVec.toNat_add, hsize]
    change (heapStart + size) % 2^64 = heapStart + size
    apply Nat.mod_eq_of_lt
    unfold heapStart
    omega
  refine st_80001cd0 hlive (fun _ => ?_) (fun bad => ?_)
  · sx_run [30] hlive
    refine next _ _ ⟨?_, ?_, ?_, ?_⟩ ?_
    · intro x h10 h14 h15
      by_cases h1 : x = 1
      · subst h1; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      by_cases h2 : x = 2
      · subst h2; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        apply BitVec.eq_of_toNat_eq; sx_addr
      by_cases h8 : x = 8
      · subst h8; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      simp only [upd_apply, h1, h2, h8, h10, h14, h15, ite_false]
    · unfold brkAddr
      rw [read64_store_hit]
      exact congrArg some sum
    · intro a ha
      unfold SbrkW brkAddr at ha
      rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
        simp only [OutL, and_true] <;> sx_addr
    · intro a h
      exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
        (writeLog_present _ _ _ (writeLog_present _ _ _ h))))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rfl
  · exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at bad
    change ¬ (BitVec.ofNat 64 heapStart + R 11).toNat ≤ heapEnd at bad
    rw [sum] at bad
    exact bad P.room
end OCaml.Vm.Boot.Startup
