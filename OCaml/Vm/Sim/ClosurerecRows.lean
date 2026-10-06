import OCaml.Vm.Sim.MakeblockNRows
import OCaml.Vm.Sim.Closurerec
import OCaml.Vm.Sim.SwitchRows

/-!
# CLOSUREREC from the loop head

CLOSUREREC takes a variable operand list (function count, capture count, one
offset per function), so its row decodes all operands directly.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem option_mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | x :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [option_mapM_length hys]

/-- A continuing CLOSUREREC had valid counts, all its captures, and targets. -/
theorem closurerec_shape {P : Prog} {s s' : St} {nf nv : Int} {ofss : List Int}
    (step : stepI P s ⟨.CLOSUREREC, nf :: nv :: ofss⟩ = .next s') :
    0 ≤ nf ∧ 0 ≤ nv ∧ 0 < nf.toNat ∧ ofss.length = nf.toNat ∧ nv.toNat - 1 ≤ s.stack.length ∧
      ∃ dest targets, ofss.mapM (fun o => target s.pc 2 o) = some (dest :: targets) ∧
        nf.toNat = targets.length + 1 := by
  have neg : ¬ (nf < 0 ∨ nv < 0) := Res.guard_ok step
  simp only [stepI] at step
  simp only [neg, ite_false] at step
  split at step
  · simp at step
  · rename_i valid
    split at step <;> split at step
    all_goals first
      | (simp at step; done)
      | (rename_i enough
         unfold opt at step
         split at step
         · rename_i cs hm
           have len := option_mapM_length hm
           cases cs with
           | nil => simp only [List.length_nil] at len; omega
           | cons dest targets =>
             try simp only [List.length_cons] at enough
             exact ⟨by omega, by omega, by omega, by omega, by omega, dest, targets, hm,
               by simp only [List.length_cons] at len; omega⟩
         · simp at step)

theorem closurerecObject_wosize {s : St} {count dest : Nat} {targets : List Nat}
    (bound : count - 1 ≤ s.stack.length) :
    (closurerecObject s count (dest :: targets)).wosize = closurerecSize (targets.length + 1) count := by
  simp only [closurerecObject, Obj.wosize, List.length_append, closurerec_function_values_length,
    closurerecSize, closureCaptures]
  split <;> simp <;> omega

/-- The stores after the reservation: header, captures, first-function and
infix metadata, and the pushed function pointers. -/
def closurerecBodyLog (c : Config) (pl : Place) (sp count dest a : Nat) (accu : BitVec 64)
    (targets : List Nat) : List WEntry :=
  closurerecHeaderLog a (targets.length + 1) count ++
    (valueLog (closurerecCaptureBase a (targets.length + 1)) (closureWords c sp count accu) ++
      (closurerecFirstLog pl sp (targets.length + 1) count dest a ++
        (infixGroups pl a (closurerecStackStart sp count) targets).flatten))

theorem closurerecFullLog_eq (c : Config) (pl : Place) (sp count dest a domain : Nat) (accu : BitVec 64)
    (targets : List Nat) :
    closurerecFullLog c pl sp count dest a domain accu targets =
      closurePushLog sp count accu ++ (grabReserveLog domain a ++ closurerecBodyLog c pl sp count dest a accu targets) := by
  simp only [closurerecFullLog, closurerecReadyLog, closurerecSetupLog, closurerecBodyLog, List.append_assoc]

/-- The VM-stack window CLOSUREREC writes: the consumed captures (and the
pushed accumulator) down to the lowest pushed infix pointer or the pushed
accumulator, whichever is lower. -/
def closurerecStackW (sp count functions : Nat) : W :=
  ⟨min (closurerecStackStart sp count - 8 * (functions - 1)) (sp - 8), sp + 8 * (count - 1)⟩

/-- The reserved block of a recursive closure. -/
def closurerecBlockW (a functions count : Nat) : W :=
  ⟨a - 8, a + 8 * closurerecSize functions count⟩

section Pieces
variable {c : Config} {pl : Place} {sp count dest a : Nat} {accu : BitVec 64} {targets : List Nat}

theorem closurerecHeaderLog_in (room : 8 ≤ a) :
    LogInW [closurerecBlockW a (targets.length + 1) count]
      (closurerecHeaderLog a (targets.length + 1) count) :=
  ⟨Or.inl ⟨by simp only [closurerecBlockW, closurerecSize]; omega,
    by simp only [closurerecBlockW, closurerecSize]; omega⟩, trivial⟩

theorem closurerecCaptures_in (room : 8 ≤ a) :
    LogInW [closurerecBlockW a (targets.length + 1) count]
      (valueLog (closurerecCaptureBase a (targets.length + 1)) (closureWords c sp count accu)) := by
  have wordsLen := closureWords_length (c := c) (sp := sp) (count := count) (accu := accu)
  apply log_in_windows_of_mem
  intro e member
  have h := logInW_mem (value_log_in (closurerecCaptureBase a (targets.length + 1)) (closureWords c sp count accu)) member
  rcases h with h | h
  · refine Or.inl ⟨?_, ?_⟩ <;> simp only [closurerecBlockW, closurerecSize, closurerecCaptureBase] at h ⊢ <;>
      rw [wordsLen] at h <;> omega
  · exact False.elim h

theorem closurerecFirstLog_in (room : 8 ≤ a) (tailRoom : 8 ≤ sp + 8 * (count - 1)) :
    LogInW [closurerecBlockW a (targets.length + 1) count, closurerecStackW sp count (targets.length + 1)]
      (closurerecFirstLog pl sp (targets.length + 1) count dest a) := by
  have start : closurerecStackStart sp count + 8 = sp + 8 * (count - 1) := by
    unfold closurerecStackStart; omega
  exact ⟨Or.inr (Or.inl ⟨by simp only [closurerecStackW]; omega, by simp only [closurerecStackW]; omega⟩),
    Or.inl ⟨by simp only [closurerecBlockW, closurerecSize]; omega, by simp only [closurerecBlockW, closurerecSize]; omega⟩,
    Or.inl ⟨by simp only [closurerecBlockW, closurerecSize]; omega, by simp only [closurerecBlockW, closurerecSize]; omega⟩,
    trivial⟩

theorem closurerecStackSlot_in {v : BitVec 64} (tailRoom : 8 ≤ sp + 8 * (count - 1)) :
    LogInW [closurerecStackW sp count (targets.length + 1)] [(closurerecStackStart sp count, 8, v)] := by
  have start : closurerecStackStart sp count + 8 = sp + 8 * (count - 1) := by
    unfold closurerecStackStart; omega
  exact ⟨Or.inl ⟨by simp only [closurerecStackW]; omega, by simp only [closurerecStackW]; omega⟩, trivial⟩

theorem closurerecInfix_in (tailRoom : 8 ≤ sp + 8 * (count - 1))
    (stackRoom : 8 * targets.length ≤ closurerecStackStart sp count) :
    LogInW [closurerecBlockW a (targets.length + 1) count, closurerecStackW sp count (targets.length + 1)]
      (infixGroups pl a (closurerecStackStart sp count) targets).flatten := by
  have start : closurerecStackStart sp count + 8 = sp + 8 * (count - 1) := by
    unfold closurerecStackStart; omega
  apply log_in_windows_of_mem
  intro e member
  have h := logInW_mem (infix_groups_in pl a (closurerecStackStart sp count) targets stackRoom) member
  rcases h with h | h | h
  · refine Or.inl ⟨?_, ?_⟩ <;> simp only [closurerecBlockW, closurerecSize] at h ⊢ <;> omega
  · refine Or.inr (Or.inl ⟨?_, ?_⟩) <;> simp only [closurerecStackW] at h ⊢ <;> omega
  · exact False.elim h

/-- The body lies in the block and the stack window. -/
theorem closurerecBodyLog_in (room : 8 ≤ a) (tailRoom : 8 ≤ sp + 8 * (count - 1))
    (stackRoom : 8 * targets.length ≤ closurerecStackStart sp count) :
    LogInW [closurerecBlockW a (targets.length + 1) count, closurerecStackW sp count (targets.length + 1)]
      (closurerecBodyLog c pl sp count dest a accu targets) :=
  logInW_append' (logInW_left (closurerecHeaderLog_in room)) (logInW_append' (logInW_left (closurerecCaptures_in room))
    (logInW_append' (closurerecFirstLog_in room tailRoom) (closurerecInfix_in tailRoom stackRoom)))

end Pieces

/-- The pushed accumulator lies in the stack window. -/
theorem closurerecPushLog_in {sp count functions : Nat} {accu : BitVec 64} (room : 8 ≤ sp) :
    LogInW [closurerecStackW sp count functions] (closurePushLog sp count accu) := by
  unfold closurePushLog
  split
  · exact ⟨Or.inl ⟨by simp only [closurerecStackW, closurerecStackStart]; omega,
      by simp only [closurerecStackW]; omega⟩, trivial⟩
  · trivial

/-- CLOSUREREC never halts. -/
theorem closurerec_no_halt {P : Prog} {s : St} {args : List Int} {e : Nat} {w : World} :
    stepI P s ⟨.CLOSUREREC, args⟩ ≠ .halt e w := by
  intro step
  match args, step with
  | [], step => simp [stepI] at step
  | [_], step => simp [stepI] at step
  | nf :: nv :: ofss, step =>
    simp only [stepI] at step
    split at step
    · cases step
    · split at step
      · cases step
      · split at step <;> split at step
        all_goals first
          | cases step
          | (unfold opt at step; split at step <;> cases step)

end OCaml.Vm.Sim
