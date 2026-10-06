import OCaml.Vm.Sim.MakeblockRows
import OCaml.Vm.Sim.GrabAlloc
import OCaml.Vm.Sim.GrabRows

/-!
# GRAB's allocating path at the loop head

When fewer than `required` extra arguments are present, GRAB allocates a
partial-application closure of `extra + 4` fields (code, arity, environment
and the `1 + extra` arguments) and returns to the caller. Its input comes from
the loop head through the shared reservation facts (`ReservedBlock`,
`AllocLogOk.of_block`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem grabClosure_wosize {s : St} (frame : 1 + s.extra ≤ s.stack.length) :
    (grabClosure s).wosize = s.extra + 4 := by
  simp [grabClosure, Obj.wosize]
  omega

theorem stackWords_get {c : Config} {sp n i : Nat} {w : BitVec 64} (h : (stackWords c sp n)[i]? = some w) :
    word c (sp + 8 * i) = w := by
  simp only [stackWords, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨j, hj, rfl⟩ := h
  have bound := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_range] at bound
  rw [List.getElem?_range bound] at hj
  cases hj
  rfl

/-- A partial-application closure log lies in its reserved block. -/
theorem partialClosureLog_in {a : Nat} {code env : BitVec 64} {args : List (BitVec 64)} (room : 8 ≤ a) :
    LogInW [⟨a - 8, a + 8 * (args.length + 3)⟩] (partialClosureLog a code env args) := by
  simp only [partialClosureLog]
  refine logInW_append' (logInW_append' ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
    Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, trivial⟩ ?_)
    ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
      trivial⟩
  exact logInW_widen (value_log_in (a + 24) args) fun w hw => by
    simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega

/-- **GRAB's allocation input at the loop head**, the fresh location placed at
the reserved block `a`. -/
theorem GrabAllocInput.of_input {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a : Nat} {env : BitVec 64}
    (h : ArmInput L P s op c pl cp sp high) (b : ReservedBlock c a (s.extra + 4))
    (placed : pl.φ (s.heap.alloc (grabClosure s)).2 = some a)
    (frame : s.extra + 4 ≤ s.stack.length) (pcPositive : 0 < s.pc) (small : s.extra + 4 < 2^31)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) :
    GrabAllocInput P s c pl cp sp high a (word c Layout.sym_Caml_state).toNat (runtimeFields c).youngLimit env := by
  have g := h.geometry.nursery
  have sg := h.geometry.toStackGeometry
  have hs := h.stack.1
  have spSpace := stack_space h.stack space
  have room := b.room
  have alignedA := b.aligned
  have apartStack := b.stackApart g
  have apartDomain := b.domainApart g
  have size := grabClosure_wosize (s := s) (by omega)
  have argsLen : (stackWords c sp (1 + s.extra)).length = 1 + s.extra := by simp [stackWords]
  have partialIn : LogInW [⟨a - 8, a + 8 * (s.extra + 4)⟩]
      (partialClosureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc - 1))) env (stackWords c sp (1 + s.extra))) := by
    have hin := partialClosureLog_in (code := BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc - 1))) (env := env)
      (args := stackWords c sp (1 + s.extra)) room
    rw [argsLen] at hin
    simpa only [show 1 + s.extra + 3 = s.extra + 4 by omega] using hin
  have ok := AllocLogOk.of_block b g sg h.stack spSpace partialIn
  have initIn : LogInW [⟨a - 8, a + 8 * (s.extra + 4)⟩] (grabInitLog a s.extra env) :=
    ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
      trivial⟩
  have copyIn : LogInW [⟨a - 8, a + 8 * (s.extra + 4)⟩] (valueLog (a + 24) (stackWords c sp (1 + s.extra))) :=
    logInW_widen (value_log_in (a + 24) _) fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; dsimp only; rw [argsLen]; omega
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have hd := sg.domain.1
  simp only [stackWindow] at hd
  have hb : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
  have statics := b.statics
  have domainLow := sg.domainLow
  -- a range in the VM stack misses the reserved block
  have blockMissStack : ∀ {log : List WEntry}, LogInW [⟨a - 8, a + 8 * (s.extra + 4)⟩] log →
      OutLRange log sp (8 * (1 + s.extra)) := fun inside =>
    outLRange_of_windows inside ⟨by dsimp only; omega, trivial⟩
  refine
    { nursery := NurseryInput.of_block b g sg small
      initializer := ?_
      allocation := ⟨placed, g.allocationOutside b.young b.capacity room (by omega), ok.payload, ok.image,
        ok.bindings, by rw [size]; exact ok.reserve, ok.arena⟩
      codeWrite := b.write (by omega) (by omega) alignedA
      arityWrite := b.write (by omega) (by omega) (by omega)
      frameReads := ⟨by simpa only [Nat.mul_add, Nat.add_assoc] using sg.read h.stack spSpace (i := 1 + s.extra) (by omega),
        by simpa only [Nat.mul_add, Nat.add_assoc] using sg.read h.stack spSpace (i := 1 + s.extra + 1) (by omega),
        by simpa only [Nat.mul_add, Nat.add_assoc] using sg.read h.stack spSpace (i := 1 + s.extra + 2) (by omega)⟩
      pcPositive }
  refine ⟨b.write (by omega) (by omega) (by omega), g.toWindowSeparated.image (b.free initIn),
    outLRange_append (grab_out (by omega)) ⟨by dsimp only; omega, trivial⟩, ⟨by dsimp only; omega, trivial⟩,
    ⟨?_, fun i hi => sg.read h.stack spSpace (by rw [argsLen] at hi; omega),
      fun i hi => b.write (by omega) (by rw [argsLen] at hi; omega) (by omega),
      g.toWindowSeparated.image (b.free copyIn), by rw [argsLen]; exact blockMissStack copyIn,
      fun i w hw => stackWords_get hw⟩,
    outLRange_append (grab_out (by omega)) (blockMissStack initIn)⟩
  simp only [PointerCopyShape.counterBase, cursorCopyShape, Bool.false_eq_true, ite_false, argsLen]
  have := sg.top
  omega

/-- A continuing GRAB without enough extra arguments allocates and returns to
a saved frame. -/
theorem grab_alloc_shape {P : Prog} {s s' : St} {w : BitVec 32}
    (step : stepI P s ⟨.GRAB, [w.toInt]⟩ = .next s') (short : ¬ w.toInt.toNat ≤ s.extra) :
    s.extra + 4 ≤ s.stack.length ∧ 0 < s.pc ∧ s'.heap = (s.heap.alloc (grabClosure s)).1 ∧
      ∃ (dest : Nat) (savedEnv : Val) (savedExtra : BitVec 63) (rest : List Val),
        s.stack.drop (1 + s.extra) = .code dest :: savedEnv :: .int savedExtra :: rest ∧
        0 ≤ savedExtra.toInt := by
  have body := Res.unguard (Res.unguard step)
  simp only [stepI, short, ite_false] at body
  by_cases valid : s.stack.length < 1 + s.extra + 3 ∨ s.pc < 1
  · rw [if_pos valid] at body; cases body
  · rw [if_neg valid] at body
    split at body
    · rename_i dest savedEnv savedExtra rest frame
      -- BcSem's guard: the saved count is nonnegative
      have saved := Int.not_lt.mp (Res.guard_ok body)
      have next := Res.unguard body
      simp only [Res.next.injEq] at next
      subst next
      exact ⟨by omega, by omega, by simp [grabClosure], dest, savedEnv, savedExtra, rest, frame, saved⟩
    · cases body

/-- `F1`'s heap budget is small. -/
theorem f1_budgetSmall : Gc.f1Layout.budget.heapWords < 2^31 := by decide

/-- **The GRAB row**: the fast path when enough extra arguments are present,
the allocating path otherwise. -/
theorem grab_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (allocFrame : AllocFrame L) (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget)
    (budgetSmall : L.budget.heapWords < 2^31) :
    OCaml.OpArm P (OCaml.LoopAt L P) .GRAB :=
  opArm_of_next1 (fun s s' c w reach reach' h code fetch step => by
      have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
      -- BcSem's guard: the extra count fits a native long
      have smallExtra : s.extra < 2 ^ 62 := Nat.not_le.mp (Res.guard_ok (Res.unguard step))
      by_cases enough : w.toInt.toNat ≤ s.extra
      · exact grab_fast_next stable h code fetch nonnegative (by omega) enough step
      · obtain ⟨frame, pcPositive, heapEq, dest, savedEnv, savedExtra, rest, shape, savedOk⟩ :=
          grab_alloc_shape step enough
        have budget := (fits s' reach').2
        rw [heapEq, Heap.words_alloc, grabClosure_wosize (by omega)] at budget
        have space := stack_fits fits capacity reach (k := 0)
        simp only [Nat.add_zero] at space
        obtain ⟨pl0, cp, sp, high, input0⟩ := ArmInput.of_loop h code
        have reserve : Reservation L s c (s.extra + 4) := ⟨input0.geometry.room, by omega⟩
        have b := ReservedBlock.of_reservation input0.geometry.nursery reserve
        have input := input0.put (alloc_absent s.heap (grabClosure s)) b.aligned
        obtain ⟨env, -, environment⟩ := input.env
        have grab := GrabAllocInput.of_input (env := env) input b put_self frame pcPositive (by omega) space
        have argsLen : (stackWords c sp (1 + s.extra)).length = 1 + s.extra := by simp [stackWords]
        have partialIn : LogInW [⟨((runtimeFields c).youngPtr - 8 * (s.extra + 4)) - 8, ((runtimeFields c).youngPtr - 8 * (s.extra + 4)) + 8 * (s.extra + 4)⟩]
            (partialClosureLog ((runtimeFields c).youngPtr - 8 * (s.extra + 4))
              (BitVec.ofNat 64 ((pl0.put (s.heap.alloc (grabClosure s)).2
                ((runtimeFields c).youngPtr - 8 * (s.extra + 4))).codeBase + 4 * (s.pc - 1))) env
              (stackWords c sp (1 + s.extra))) := by
          have hin := partialClosureLog_in (code := BitVec.ofNat 64 ((pl0.put (s.heap.alloc (grabClosure s)).2
              ((runtimeFields c).youngPtr - 8 * (s.extra + 4))).codeBase + 4 * (s.pc - 1))) (env := env)
            (args := stackWords c sp (1 + s.extra)) b.room
          rw [argsLen] at hin
          simpa only [show 1 + s.extra + 3 = s.extra + 4 by omega] using hin
        have runtime := allocFrame.alloc P s c _ cp high _ _ input.runtime input.geometry.nursery
          (b.free partialIn) b.capacity (by have := b.young; omega) (by have := b.aligned; omega)
        obtain ⟨after, run, running⟩ := grab_alloc_step_arm runtime input
          (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (by omega) environment shape
          savedOk grab step
        exact ⟨after, run, h.of_plus run running⟩)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl))
    (fun s a e w step => by
      simp only [stepI] at step
      split at step
      · cases step
      · split at step
        · cases step
        · split at step
          · cases step
          · split at step
            · cases step
            · split at step
              · split at step <;> cases step
              · cases step)

end OCaml.Vm.Sim
