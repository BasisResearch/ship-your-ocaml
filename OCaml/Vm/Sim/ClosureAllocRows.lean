import OCaml.Vm.Sim.GrabAllocRows
import OCaml.Vm.Sim.Closure

/-!
# CLOSURE from the loop head

CLOSURE pushes the accumulator (when it captures), reserves `count + 2` words
and initializes the closure. The push is a VM-stack prefix of the
reservation (`AllocLogOk.of_prefixed`, `AllocFrame.prefixed`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem closureWords_length {c : Config} {sp count : Nat} {accu : BitVec 64} :
    (closureWords c sp count accu).length = count := by
  unfold closureWords
  split <;> simp [stackWords] <;> omega

theorem closureObject_wosize {s : St} {count dest : Nat} (bound : count - 1 ≤ s.stack.length) :
    (closureObject s count dest).wosize = count + 2 := by
  simp only [closureObject, closureCaptures, Obj.wosize]
  split <;> simp <;> omega

/-- A closure log lies in its reserved block. -/
theorem closureLog_in {a : Nat} {code : BitVec 64} {captures : List (BitVec 64)} (room : 8 ≤ a) :
    LogInW [⟨a - 8, a + 8 * (captures.length + 2)⟩] (closureLog a code captures) := by
  simp only [closureLog]
  refine logInW_append' (logInW_append' ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, trivial⟩ ?_)
    ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩,
      trivial⟩
  exact logInW_widen (value_log_in (a + 16) captures) fun w hw => by
    simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega

/-- The pushed accumulator lies below the stack pointer. -/
theorem closurePushLog_in {sp high count : Nat} {accu : BitVec 64} (low : high - Layout.stackBytes + 8 ≤ sp) :
    LogInW [freeWindow sp high] (closurePushLog sp count accu) := by
  unfold closurePushLog
  split
  · exact ⟨Or.inl ⟨by dsimp only [freeWindow]; omega, by dsimp only [freeWindow]; omega⟩, trivial⟩
  · trivial

/-- **CLOSURE's allocation input at the loop head**, the fresh location placed
at the reserved block `a`. -/
theorem ClosureAllocInput.of_input {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a count dest : Nat} {accu : BitVec 64}
    (h : ArmInput L P s op c pl cp sp high) (b : ReservedBlock c a (count + 2))
    (placed : pl.φ (s.heap.alloc (closureObject s count dest)).2 = some a)
    (bound : count - 1 ≤ s.stack.length) (young : count ≤ 254)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes) :
    ClosureAllocInput P s c pl cp sp high count dest a (word c Layout.sym_Caml_state).toNat (runtimeFields c).youngLimit accu := by
  have g := h.geometry.nursery
  have sg := h.geometry.toStackGeometry
  have hs := h.stack.1
  have stat0 := sg.statics
  have spSpace : high - Layout.stackBytes ≤ sp := by omega
  have pushRoom : high - Layout.stackBytes + 8 ≤ sp := by omega
  have room := b.room
  have alignedA := b.aligned
  have apartStack := b.stackApart g
  have apartDomain := b.domainApart g
  have size := closureObject_wosize (dest := dest) bound
  have wordsLen := closureWords_length (c := c) (sp := sp) (count := count) (accu := accu)
  have hd := sg.domain.1
  simp only [stackWindow] at hd
  have domainLow := sg.domainLow
  have statics := b.statics
  have hb : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have hl : Layout.off_young_limit + 8 ≤ Layout.domainStateBytes := by decide
  have stat := sg.statics
  have top := sg.top
  have hal := sg.aligned
  have ht : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hr : 0x80000000 ≤ Layout.sym_tohost := by decide
  have pushW : RamWriteAt (sp - 8) 8 :=
    ⟨by omega, by omega, by simp only [tohostAddr, ← mailbox_layout] at *; omega, by omega⟩
  have pushIn := closurePushLog_in (count := count) (accu := accu) pushRoom
  have blockIn : LogInW [⟨a - 8, a + 8 * (count + 2)⟩]
      (closureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (closureWords c sp count accu)) := by
    have hin := closureLog_in (code := BitVec.ofNat 64 (pl.codeBase + 4 * dest))
      (captures := closureWords c sp count accu) room
    rwa [wordsLen] at hin
  have ok := AllocLogOk.of_prefixed b g sg h.stack spSpace pushIn blockIn
  have headerIn : LogInW [⟨a - 8, a + 8 * (count + 2)⟩] (closureHeaderLog a count) :=
    ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, trivial⟩
  have copyIn : LogInW [⟨a - 8, a + 8 * (count + 2)⟩] (valueLog (a + 16) (closureWords c sp count accu)) :=
    logInW_widen (value_log_in (a + 16) _) fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; dsimp only; rw [wordsLen]; omega
  -- ranges in the VM stack miss the reserved block and the young/limit words
  have blockMiss : ∀ {log : List WEntry} {x k : Nat}, LogInW [⟨a - 8, a + 8 * (count + 2)⟩] log →
      high - Layout.stackBytes ≤ x → x + k ≤ high → OutLRange log x k := fun inside lo hi =>
    outLRange_of_windows inside ⟨by dsimp only; omega, trivial⟩
  have pushMiss : ∀ {x : Nat}, x + 8 ≤ high - Layout.stackBytes ∨ high ≤ x →
      OutLRange (closurePushLog sp count accu) x 8 := fun h' =>
    outLRange_of_windows pushIn ⟨by simp only [freeWindow]; omega, trivial⟩
  have sourceLow : high - Layout.stackBytes ≤ closureSource sp count := by
    unfold closureSource; split <;> omega
  have sourceHigh : closureSource sp count + 8 * count ≤ high := by
    unfold closureSource; split <;> omega
  refine
    { bound, small := by omega, room, placed
      separate := g.allocationOutside b.young b.capacity room (by omega)
      payload := by rw [closureAllocationLog, List.append_assoc]; exact ok.payload
      image := by rw [closureAllocationLog, List.append_assoc]; exact ok.image
      bindings := by rw [closureAllocationLog, List.append_assoc]; exact ok.bindings
      reserve := by rw [closureAllocationLog, List.append_assoc, size]; exact ok.reserve
      arena := by rw [closureAllocationLog, List.append_assoc]; exact ok.arena
      young
      push := ⟨fun _ => by omega, fun _ => pushW,
        sg.image pushIn⟩
      nursery := ⟨NurseryInput.of_block b g sg (by omega), pushMiss (by omega), pushMiss (by omega),
        pushMiss (by omega)⟩
      initializer := ⟨g.toWindowSeparated.image (b.free headerIn),
        outLRange_append (pushMiss (by omega)) (outLRange_append (grab_out (by omega))
          ⟨by dsimp only; omega, trivial⟩),
        ⟨by dsimp only; omega, trivial⟩,
        fun i hi => ?_,
        fun i hi => b.write (by omega) (by omega) (by omega),
        g.toWindowSeparated.image (b.free copyIn),
        blockMiss copyIn sourceLow sourceHigh,
        outLRange_append (grab_out (by omega)) (blockMiss headerIn sourceLow sourceHigh)⟩
      metadata := ⟨b.write (by omega) (by omega) alignedA, b.write (by omega) (by omega) (by omega)⟩ }
  -- reads of the capture source: the pushed slot, then the stack
  unfold closureSource at *
  split
  · rename_i positive
    cases i with
    | zero => simpa using pushW.read
    | succ j =>
      have r := sg.read h.stack spSpace (i := j) (by omega)
      have e : sp - 8 + 8 * (j + 1) = sp + 8 * j := by omega
      rwa [e]
  · omega

/-- A continuing CLOSURE had its captures and a valid target. -/
theorem closure_shape {P : Prog} {s s' : St} {nv ofs : Int} (step : stepI P s ⟨.CLOSURE, [nv, ofs]⟩ = .next s') :
    0 ≤ nv ∧ nv.toNat - 1 ≤ s.stack.length ∧ ∃ dest, target s.pc 1 ofs = some dest := by
  have neg : ¬ nv < 0 := Res.guard_ok step
  simp only [stepI] at step
  by_cases pos : 0 < nv.toNat
  · simp [neg, pos] at step
    split at step
    · simp at step
    · rename_i enough
      cases hj : target s.pc 1 ofs with
      | none => simp [hj, opt] at step
      | some dest => exact ⟨by omega, by omega, dest, rfl⟩
  · simp [neg, pos] at step
    split at step
    · simp at step
    · cases hj : target s.pc 1 ofs with
      | none => simp [hj, opt] at step
      | some dest => exact ⟨by omega, by omega, dest, rfl⟩

/-- **The CLOSURE row.** -/
theorem closure_row {L : OCaml.Layout} {P : Prog} {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (allocFrame : AllocFrame L) (fits : OCaml.Fits L.budget P) (capacity : StackCapacity L.budget)
    (good : OCaml.GoodF1 P) : OCaml.OpArm P (OCaml.LoopAt L P) .CLOSURE :=
  opArm_of_next2_f1 good (fun s s' c n o reach reach' h code fetchN fetchO f1 step => by
      obtain ⟨nonnegative, bound, dest, jump⟩ := closure_shape step
      have state := closure_state_of_step bound jump step
      have young : n.toInt.toNat ≤ 254 := by
        have m := f1.minor
        simp only [Instr.minorAlloc] at m
        have m := of_decide_eq_true m
        simp only [OCaml.maxYoungWosize] at m
        omega
      have budget := (fits s' reach').2
      rw [← state] at budget
      simp only [closureState, Heap.words_alloc, closureObject_wosize (dest := dest) bound] at budget
      have space := stack_fits fits capacity reach (k := 1)
      obtain ⟨pl0, cp, sp, high, input0⟩ := ArmInput.of_loop h code
      have reserve : Reservation L s c (n.toInt.toNat + 2) := ⟨input0.geometry.room, by omega⟩
      have b := ReservedBlock.of_reservation input0.geometry.nursery reserve
      have input := input0.put (alloc_absent s.heap (closureObject s n.toInt.toNat dest)) b.aligned
      obtain ⟨accu, -, value⟩ := input.accu
      have alloc := ClosureAllocInput.of_input (accu := accu) input b put_self bound young space
      -- the runtime invariant across the push and the reservation
      have sg := input.geometry.toStackGeometry
      have hs := input.stack.1
      have stat := sg.statics
      have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
      have pushIn : LogInW [⟨sp - 8, sp⟩] (closurePushLog sp n.toInt.toNat accu) := by
        unfold closurePushLog; split
        · exact ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, trivial⟩
        · trivial
      have vm : ∀ w ∈ [(⟨sp - 8, sp⟩ : W)], VmWindow high (word c Layout.sym_Caml_state).toNat w := by
        intro w hw; simp only [List.mem_singleton] at hw; subst hw
        exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
      have stable : WindowStable L.runtimeOk [⟨sp - 8, sp⟩] := rf.windows _ fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; rw [← same]
        exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
      have hb : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
      have hc : Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Layout.sym_bss_end := by decide
      have wordsLen := closureWords_length (c := c) (sp := sp) (count := n.toInt.toNat) (accu := accu)
      have blockIn : LogInW [⟨((runtimeFields c).youngPtr - 8 * (n.toInt.toNat + 2)) - 8, ((runtimeFields c).youngPtr - 8 * (n.toInt.toNat + 2)) + 8 * (n.toInt.toNat + 2)⟩]
          (closureLog ((runtimeFields c).youngPtr - 8 * (n.toInt.toNat + 2))
            (BitVec.ofNat 64 ((pl0.put (s.heap.alloc (closureObject s n.toInt.toNat dest)).2
              ((runtimeFields c).youngPtr - 8 * (n.toInt.toNat + 2))).codeBase + 4 * dest))
            (closureWords c sp n.toInt.toNat accu)) := by
        have hin := closureLog_in (code := BitVec.ofNat 64 ((pl0.put (s.heap.alloc (closureObject s n.toInt.toNat dest)).2
            ((runtimeFields c).youngPtr - 8 * (n.toInt.toNat + 2))).codeBase + 4 * dest))
          (captures := closureWords c sp n.toInt.toNat accu) b.room
        rwa [wordsLen] at hin
      have hd := sg.domain.1
      simp only [stackWindow] at hd
      have hh : Layout.off_stack_high + 8 ≤ Layout.domainStateBytes := by decide
      have runtime := allocFrame.prefixed stable pushIn
        (outLRange_of_windows pushIn ⟨by dsimp only; omega, trivial⟩)
        (outLRange_of_windows pushIn ⟨by dsimp only; omega, trivial⟩)
        (outLRange_of_windows pushIn ⟨by dsimp only; omega, trivial⟩)
        (.of_windows sg pushIn vm) input.geometry.nursery (logInW_left (b.free blockIn)) b.capacity
        (by have := b.young; omega) (by have := b.aligned; omega)
      obtain ⟨after, run, running⟩ := closure_step_arm (by rw [closureAllocationLog, List.append_assoc]; exact runtime)
        input (OperandAt.of_fetch input.geometry.toArmGeometry fetchN)
        (OperandAt.of_fetch input.geometry.toArmGeometry fetchO) nonnegative jump value alloc step
      exact ⟨after, run, h.of_plus run running⟩)
    (shape2 (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
    (fun s a b e w step => by
      simp only [stepI] at step
      by_cases neg : a < 0
      · simp [neg] at step
      · by_cases pos : 0 < a.toNat <;> simp [neg, pos] at step <;> split at step <;>
          first | simp at step | (cases hj : target s.pc 1 b <;> simp [hj, opt] at step))

end OCaml.Vm.Sim
