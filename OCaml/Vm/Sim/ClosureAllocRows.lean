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

end OCaml.Vm.Sim
