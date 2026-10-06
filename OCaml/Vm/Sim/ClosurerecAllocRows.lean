import OCaml.Vm.Sim.ClosurerecPlan

/-!
# The CLOSUREREC row

CLOSUREREC pushes the accumulator (when it captures), reserves the whole
recursive closure, initializes it, and pushes one pointer per function over
the consumed captures. The push is a VM-stack prefix of the reservation, and
the stores after it reach the VM stack too, so the runtime invariant comes
from the two-window `AllocFrame.prefixed`; every separation fact comes from
`ClosurerecPlan`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem closurerecStack_length {s : St} {count functions fresh : Nat} :
    (closurerecStack s count functions fresh).length = functions - 1 + 1 + (s.stack.length - (count - 1)) := by
  simp [closurerecStack]; omega

/-- **Every reachable CLOSUREREC builds a closure of at most 256 words**
(named per-program code fact: the closure then fits the minor heap's size
limit). -/
structure ClosurerecSizes (P : Prog) : Prop where
  small : ∀ s (nf nv : BitVec 32), Reach P s → DispatchCode P s .CLOSUREREC →
    P.code[s.pc + 1]? = some nf → P.code[s.pc + 2]? = some nv →
    closurerecSize nf.toInt.toNat nv.toInt.toNat ≤ 256

/-- The model's offsets, read back from the code. -/
def closurerecOffsets (P : Prog) (pc : Nat) (i : Nat) : BitVec 32 := (P.code[pc + 4 + i]?).getD 0

/-- **The CLOSUREREC row.** -/
theorem closurerec_row {L : OCaml.Layout} {P : Prog} {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (allocFrame : AllocFrame L) (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget)
    (sizes : ClosurerecSizes P) : OCaml.OpArm P (OCaml.LoopAt L P) .CLOSUREREC :=
  opArm_of_next (fun s s' c args reach reach' h code fetches step => by
      match args, fetches, step with
      | [], _, step => simp [stepI] at step
      | [_], _, step => simp [stepI] at step
      | nf :: nv :: ofss, fetches, step =>
      obtain ⟨-, nvNN, nfPos, ofLen, bound, dest, targets, jumps, arity⟩ := closurerec_shape step
      obtain ⟨wf, hf, rfl⟩ := fetches 0 nf rfl
      obtain ⟨wc, hc, rfl⟩ := fetches 1 nv rfl
      have state := closurerec_state_of_step arity ofLen bound jumps step
      cases ofss with
      | nil => simp at ofLen; omega
      | cons o0 rest =>
      obtain ⟨w3, h3, rfl⟩ := fetches 2 o0 rfl
      replace hf : P.code[s.pc + 1]? = some wf := by simpa using hf
      replace hc : P.code[s.pc + 2]? = some wc := by simpa using hc
      replace h3 : P.code[s.pc + 3]? = some w3 := by simpa using h3
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at jumps
      obtain ⟨d0, jump0, ts, hrest, hts⟩ := jumps
      injection hts with hd ht
      subst hd ht
      simp only [List.length_cons] at ofLen
      have restLen := option_mapM_length hrest
      -- the model's offsets are the code words after the first
      have offsetsAt : ∀ i, i < ts.length → P.code[s.pc + 4 + i]? = some (closurerecOffsets P s.pc i) ∧
          ∃ x, rest[i]? = some x ∧ (closurerecOffsets P s.pc i).toInt = x := by
        intro i hi
        obtain ⟨x, hx⟩ : ∃ x, rest[i]? = some x := ⟨rest[i]'(by omega), by simp⟩
        obtain ⟨w, hw, rfl⟩ := fetches (i + 3) x (by simpa using hx)
        have e : s.pc + 1 + (i + 3) = s.pc + 4 + i := by omega
        rw [e] at hw
        exact ⟨by simp [closurerecOffsets, hw], w.toInt, hx, by simp [closurerecOffsets, hw]⟩
      have jumpsAt : ∀ i (hi : i < ts.length), target s.pc 2 (closurerecOffsets P s.pc i).toInt = some ts[i] := by
        intro i hi
        obtain ⟨x, hx, hj⟩ := option_mapM_get hrest (List.getElem?_eq_getElem hi)
        obtain ⟨-, x', hx', e⟩ := offsetsAt i hi
        rw [hx] at hx'
        cases hx'
        rw [e]; exact hj
      -- sizes and budgets
      have young := sizes.small s wf wc reach code hf hc
      rw [arity] at young
      have budget := (fits s' reach').2
      have stackAfter := (fits s' reach').1
      rw [← state] at budget stackAfter
      simp only [closurerecState, Heap.words_alloc, closurerecObject_wosize (dest := d0) (targets := ts) bound]
        at budget
      simp only [closurerecState, closurerecStack_length] at stackAfter
      unfold StackCapacity at capacity
      have space := stack_fits fits capacity reach (k := 1)
      obtain ⟨pl0, cp, sp, high, input0⟩ := ArmInput.of_loop h code
      have reserve : Reservation L s c (closurerecSize (ts.length + 1) wc.toInt.toNat) := ⟨input0.geometry.room, by omega⟩
      have b := ReservedBlock.of_reservation input0.geometry.nursery reserve
      have input := input0.put (alloc_absent s.heap (closurerecObject s wc.toInt.toNat (d0 :: ts))) b.aligned
      obtain ⟨accu, -, value⟩ := input.accu
      have plan : ClosurerecPlan L P s .CLOSUREREC c _ cp sp high wc.toInt.toNat d0 _ ts (closurerecOffsets P s.pc) :=
        ⟨input, b, put_self, bound, young, space, by omega, ⟨w3, h3⟩, fun i hi => (offsetsAt i hi).1, jumpsAt⟩
      -- the runtime invariant across the push and the reservation
      have k := plan.scalars
      have kl := k.low
      have kp := k.push
      have kr := k.ptrs
      have khs := k.hs
      have sg := input.geometry.toStackGeometry
      have hd := sg.domain.1
      simp only [stackWindow] at hd
      have hb : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
      have hc' : Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Layout.sym_bss_end := by decide
      have hh : Layout.off_stack_high + 8 ≤ Layout.domainStateBytes := by decide
      have stat := sg.statics
      have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
      have pushIn : LogInW [⟨sp - 8, sp⟩] (closurePushLog sp wc.toInt.toNat accu) := by
        unfold closurePushLog; split
        · exact ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, trivial⟩
        · trivial
      have vm : ∀ w ∈ [(⟨sp - 8, sp⟩ : W)], VmWindow high (word c Layout.sym_Caml_state).toNat w := by
        intro w hw; simp only [List.mem_singleton] at hw; subst hw
        exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
      have stable : WindowStable L.runtimeOk [⟨sp - 8, sp⟩] := rf.windows _ fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; rw [← same]
        exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
      have bodyIn : LogInW [Gc.nurseryFree c, stackWindow (domainWord c Layout.off_stack_high)]
          (closurerecBodyLog c (pl0.put (s.heap.alloc (closurerecObject s wc.toInt.toNat (d0 :: ts))).2
            ((runtimeFields c).youngPtr - 8 * closurerecSize (ts.length + 1) wc.toInt.toNat)) sp wc.toInt.toNat d0
            ((runtimeFields c).youngPtr - 8 * closurerecSize (ts.length + 1) wc.toInt.toNat) accu ts) := by
        have inside := closurerecBodyLog_in (c := c) (pl := pl0.put (s.heap.alloc (closurerecObject s wc.toInt.toNat (d0 :: ts))).2
          ((runtimeFields c).youngPtr - 8 * closurerecSize (ts.length + 1) wc.toInt.toNat)) (dest := d0) (accu := accu)
          b.room plan.tailRoom plan.stackRoom
        have y := b.young
        have cap := b.capacity
        have dh : domainWord c Layout.off_stack_high = high := input.stackHigh
        rw [dh]
        apply log_in_windows_of_mem
        intro e member
        rcases logInW_mem inside member with h | h | h
        · exact Or.inl ⟨by simp only [Gc.nurseryFree, closurerecBlockW] at h ⊢; omega,
            by simp only [Gc.nurseryFree, closurerecBlockW] at h ⊢; omega⟩
        · exact Or.inr (Or.inl ⟨by simp only [stackWindow, closurerecStackW, closurerecStackStart] at h ⊢; omega,
            by simp only [stackWindow, closurerecStackW, closurerecStackStart] at h ⊢; omega⟩)
        · exact False.elim h
      have runtime := allocFrame.prefixed stable pushIn
        (outLRange_of_windows pushIn ⟨by dsimp only; omega, trivial⟩)
        (outLRange_of_windows pushIn ⟨by dsimp only; omega, trivial⟩)
        (outLRange_of_windows pushIn ⟨by dsimp only; omega, trivial⟩)
        (.of_windows sg pushIn vm) input.geometry.nursery bodyIn b.capacity
        (by have := b.young; omega) (by have := b.aligned; omega)
      obtain ⟨after, run, running⟩ := closurerec_step_arm (w3.toInt :: rest) (by simpa using ofLen)
        (by simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
            exact ⟨d0, jump0, ts, hrest, rfl⟩)
        step input
        (OperandAt.of_fetch input.geometry.toArmGeometry hf) (by omega)
        (OperandAt.of_fetch input.geometry.toArmGeometry hc) (by omega)
        (OperandAt.of_fetch input.geometry.toArmGeometry h3) jump0 arity value
        (by rw [closurerecFullLog_eq]; exact runtime) (plan.writes accu) (plan.reserve accu) (plan.arena accu)
        (plan.machine accu)
      exact ⟨after, run, h.of_plus run running⟩)
    (fun _ _ _ _ => closurerec_no_halt)

end OCaml.Vm.Sim
