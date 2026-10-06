import OCaml.Vm.Primitives.Word32Access
import OCaml.Vm.Primitives.AccessPlan

/-! Access plans of blocks whose loads follow their own stores: the loads read
the caller's memory when they miss the block's store log, so a generated
wrapper checks every access against the caller's memory (`AccessPure`) and
each load's address against the log (`LoadMiss`), never a chain of stores. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

def IsStore (k : MKind) : Bool :=
  match k with
  | .sw | .sd | .sb | .sh => true
  | _ => false

theorem stepMemM_store {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} (kind : IsStore a.kind = true) :
    stepMemM m a L = writeLog m [wentryM a L] := by
  unfold stepMemM
  split <;> first | rfl | simp [IsStore, *] at kind

theorem stepMemM_skip {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} (kind : IsStore a.kind = false) :
    stepMemM m a L = m := by
  unfold stepMemM
  split <;> first | rfl | simp [IsStore, *] at kind

/-! ## Access plans whose loads read the caller's memory -/

def IsLoad (k : MKind) : Bool :=
  match k with
  | .lw | .lwu | .ld | .lbu | .lh | .lhu => true
  | _ => false

/-- Every access of a block, checked against the caller's memory `m`. -/
def AccessPure (m : Std.ExtHashMap Nat (BitVec 8)) : GRegs → List (List (BitVec 8)) → List MInstr → Prop
  | _, _, [] => True
  | L, loads, a :: rest =>
    MemFacts m L (loads.headD []) a ∧ AccessPure m (stepGM a L (loads.headD [])) (stepLdsM a.kind loads) rest

/-- Every load of a block misses the store log `log`. -/
def LoadMiss (log : List WEntry) : GRegs → List (List (BitVec 8)) → List MInstr → Prop
  | _, _, [] => True
  | L, loads, a :: rest =>
    (IsLoad a.kind = true → OutLRange log (eaddrM a L).toNat (widthOfM a.kind)) ∧
    LoadMiss log (stepGM a L (loads.headD [])) (stepLdsM a.kind loads) rest

theorem outLRange_prefix {log rest : List WEntry} {x n : Nat} (h : OutLRange (log ++ rest) x n) :
    OutLRange log x n := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨h.1, ih h.2⟩

theorem outLRange_of_eaddr {log : List WEntry} {a : MInstr} {L : GRegs} {x : BitVec 64} {n : Nat}
    (e : eaddrM a L = x) (h : OutLRange log x.toNat n) : OutLRange log (eaddrM a L).toNat n := e ▸ h

theorem memFacts_writeLog {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {bs : List (BitVec 8)} {a : MInstr}
    {log : List WEntry} (h : MemFacts m L bs a)
    (miss : IsLoad a.kind = true → OutLRange log (eaddrM a L).toNat (widthOfM a.kind)) :
    MemFacts (writeLog m log) L bs a := by
  have same : ∀ i, i < widthOfM a.kind → IsLoad a.kind = true →
      ((writeLog m log)[(eaddrM a L).toNat + i]?).getD 0 = (m[(eaddrM a L).toNat + i]?).getD 0 :=
    fun i hi hl => by rw [writeLog_out _ _ _ (outL_of_range (miss hl) (by omega) (by omega))]
  unfold MemFacts at *
  cases hk : a.kind <;> simp only [hk] at h ⊢ <;> try exact h
  · exact ⟨h.1, lpins4_writeLog h.2 (by simpa [hk, widthOfM] using miss (by simp [IsLoad, hk]))⟩
  · exact ⟨h.1, lpins4_writeLog h.2 (by simpa [hk, widthOfM] using miss (by simp [IsLoad, hk]))⟩
  · exact ⟨h.1, lpins8_writeLog h.2 (by simpa [hk, widthOfM] using miss (by simp [IsLoad, hk]))⟩
  · refine ⟨h.1, ?_⟩
    have := same 0 (by simp [hk, widthOfM]) (by simp [IsLoad, hk])
    simp only [Nat.add_zero] at this; rw [this]; exact h.2
  · refine ⟨h.1, ?_, ?_⟩
    · have := same 0 (by simp [hk, widthOfM]) (by simp [IsLoad, hk])
      simp only [Nat.add_zero] at this; rw [this]; exact h.2.1
    · rw [same 1 (by simp [hk, widthOfM]) (by simp [IsLoad, hk])]; exact h.2.2
  · refine ⟨h.1, ?_, ?_⟩
    · have := same 0 (by simp [hk, widthOfM]) (by simp [IsLoad, hk])
      simp only [Nat.add_zero] at this; rw [this]; exact h.2.1
    · rw [same 1 (by simp [hk, widthOfM]) (by simp [IsLoad, hk])]; exact h.2.2

theorem accessPlan_of_miss {m : Std.ExtHashMap Nat (BitVec 8)} :
    ∀ (body : List MInstr) (L : GRegs) (loads : List (List (BitVec 8))) (log0 : List WEntry),
    AccessPure m L loads body → LoadMiss (log0 ++ wlogM body L loads) L loads body →
    AccessPlan (writeLog m log0) L loads body
  | [], _, _, _, _, _ => trivial
  | a :: rest, L, loads, log0, ⟨facts, pure⟩, ⟨miss, misses⟩ => by
    refine ⟨memFacts_writeLog facts fun hl => outLRange_prefix (miss hl), ?_⟩
    by_cases st : IsStore a.kind = true
    · rw [stepMemM_store st, show writeLog (writeLog m log0) [wentryM a L] = writeLog m (log0 ++ [wentryM a L]) by
        simp [writeLog, List.foldl_append]]
      have wl : wlogM (a :: rest) L loads = wentryM a L :: wlogM rest L loads := by
        simp only [wlogM]; split <;> simp_all [IsStore]
      have ls : stepLdsM a.kind loads = loads := by
        unfold stepLdsM; split <;> simp_all [IsStore]
      have gs : stepGM a L (loads.headD []) = L := by
        unfold stepGM; split <;> simp_all [IsStore]
      rw [wl] at misses miss
      rw [gs, ls] at misses pure ⊢
      exact accessPlan_of_miss rest L loads _ pure (by simpa using misses)
    · rw [stepMemM_skip (by simpa using st)]
      have wl : wlogM (a :: rest) L loads = wlogM rest (stepGM a L (loads.headD [])) (stepLdsM a.kind loads) := by
        simp only [wlogM]; split <;> simp_all [IsStore]
      rw [wl] at misses
      exact accessPlan_of_miss rest _ _ log0 pure misses

/-- A block's access plan from accesses against the caller's memory, when
every load misses the block's own stores. -/
theorem accessPlan_of_pure {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {loads : List (List (BitVec 8))}
    {body : List MInstr} (pure : AccessPure m L loads body) (miss : LoadMiss (wlogM body L loads) L loads body) :
    AccessPlan m L loads body :=
  accessPlan_of_miss body L loads [] pure miss

end OCaml.Vm.Primitives
