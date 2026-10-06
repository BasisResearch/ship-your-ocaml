import OCaml.Vm.Sim.ClosurerecRows
import OCaml.Vm.Sim.FreshLog

/-!
# CLOSUREREC's allocation inputs from the loop geometry

`ClosurerecPlan` names what the row knows at a CLOSUREREC: the arm input with
the fresh location placed at the reserved block, the block, the model's
counts and the code words. Every store of the arm lies in the reserved block,
the VM stack allocation or the young-pointer word (`closurerecFresh`), so
`FreshLogOk.of_windows` gives every separation fact once; the theorems below
read the write certificate, the reservation summary and the machine input
off it.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A CLOSUREREC's premises at the loop head. -/
structure ClosurerecPlan (L : OCaml.Layout) (P : Prog) (s : St) (op : Opcode) (c : Config) (pl : Place)
    (cp : ChanPlace) (sp high count dest a : Nat) (targets : List Nat) (offsets : Nat → BitVec 32) : Prop where
  input : ArmInput L P s op c pl cp sp high
  block : ReservedBlock c a (closurerecSize (targets.length + 1) count)
  placed : pl.φ (s.heap.alloc (closurerecObject s count (dest :: targets))).2 = some a
  bound : count - 1 ≤ s.stack.length
  young : closurerecSize (targets.length + 1) count ≤ 256
  /-- the pushed accumulator fits -/
  space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes
  /-- the stack after the arm fits -/
  after : 8 * (s.stack.length - (count - 1) + (targets.length + 1)) ≤ Layout.stackBytes
  /-- the first function's offset word -/
  first : ∃ w, P.code[s.pc + 3]? = some w
  /-- the other functions' offset words and their targets -/
  offsetsAt : ∀ i, i < targets.length → P.code[s.pc + 4 + i]? = some (offsets i)
  jumps : ∀ i (bound : i < targets.length), target s.pc 2 (offsets i).toInt = some targets[i]

namespace ClosurerecPlan

variable {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config} {pl : Place} {cp : ChanPlace}
  {sp high count dest a : Nat} {targets : List Nat} {offsets : Nat → BitVec 32}

/-- The arm's write windows. -/
def windows (c : Config) (sp count a functions : Nat) : List W :=
  [closurerecBlockW a functions count, closurerecStackW sp count functions, youngPtrW c]

/-- The plan's scalar geometry, in one place for `omega`. -/
structure Scalars (c : Config) (sp high count a functions : Nat) (len : Nat) : Prop where
  hs : sp + 8 * len = high
  low : high - Layout.stackBytes ≤ sp
  statics : Layout.sym_bss_end + Layout.stackBytes ≤ high
  top : high ≤ 0x100000000
  spAligned : sp % 8 = 0
  push : 8 ≤ sp - (high - Layout.stackBytes)
  ptrs : 8 * functions ≤ sp + 8 * (count - 1) - (high - Layout.stackBytes)
  below : a + 8 * closurerecSize functions count ≤ high - Layout.stackBytes

theorem scalars (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) :
    Scalars c sp high count a (targets.length + 1) s.stack.length := by
  have hs := p.input.stack.1
  have g := p.input.geometry
  have st := g.statics
  have tp := g.top
  have al := g.aligned
  have fits := p.space
  have fits' := p.after
  have bd := p.bound
  have ab := g.nursery.stackAbove
  have y := p.block.young
  exact ⟨by omega, by omega, st, tp, by omega, by omega, by omega, by omega⟩

theorem tailRoom (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) :
    8 ≤ sp + 8 * (count - 1) := by
  have k := p.scalars; have := k.push; have := k.ptrs; omega

theorem stackRoom (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) :
    8 * targets.length ≤ closurerecStackStart sp count := by
  have k := p.scalars; have := k.push; have := k.ptrs; unfold closurerecStackStart; omega

/-- Every arm window is a fresh-allocation window. -/
theorem fresh (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) :
    ∀ w ∈ windows c sp count a (targets.length + 1), FreshWindow c high w := by
  have k := p.scalars
  have b := p.block
  have bd := p.bound
  have kr := k.push; have kr' := k.ptrs
  have khs := k.hs
  have y := b.young
  have cap := b.capacity
  intro w hw
  simp only [windows, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inl ⟨by simp only [closurerecBlockW]; omega, by simp only [closurerecBlockW]; omega⟩
  · exact Or.inr (Or.inl ⟨by simp only [closurerecStackW, closurerecStackStart]; omega,
      by simp only [closurerecStackW]; omega⟩)
  · exact Or.inr (Or.inr rfl)

theorem pair_in {log : List WEntry} {a sp count functions : Nat}
    (h : LogInW [closurerecBlockW a functions count, closurerecStackW sp count functions] log) :
    LogInW (windows c sp count a functions) log :=
  logInW_mono h fun w hw => by
    simp only [windows, List.mem_cons, List.mem_nil_iff, or_false] at hw ⊢
    rcases hw with rfl | rfl <;> simp

theorem push_in (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {accu : BitVec 64} :
    LogInW (windows c sp count a (targets.length + 1)) (closurePushLog sp count accu) :=
  logInW_mono (closurerecPushLog_in (functions := targets.length + 1) (by have k := p.scalars; have := k.push; have := k.ptrs; omega)) fun w hw => by
    simp only [windows, List.mem_cons, List.mem_nil_iff, or_false] at hw ⊢
    simp [hw]

theorem grab_in {a sp count functions : Nat} :
    LogInW (windows c sp count a functions) (grabReserveLog (word c Layout.sym_Caml_state).toNat a) :=
  logInW_mono (grabReserveLog_in c a) fun w hw => by
    simp only [windows, List.mem_cons, List.mem_nil_iff, or_false] at hw ⊢
    simp [hw]

theorem full_in (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {accu : BitVec 64} :
    LogInW (windows c sp count a (targets.length + 1))
      (closurerecFullLog c pl sp count dest a (word c Layout.sym_Caml_state).toNat accu targets) := by
  rw [closurerecFullLog_eq]
  exact logInW_append' p.push_in (logInW_append' grab_in
    (pair_in (closurerecBodyLog_in p.block.room p.tailRoom p.stackRoom)))

/-- Separation of any log in the arm windows. -/
theorem ok (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {log : List WEntry}
    (inside : LogInW (windows c sp count a (targets.length + 1)) log) : FreshLogOk log P s c pl cp :=
  FreshLogOk.of_windows p.input.geometry.toArmGeometry inside p.fresh

/-- A range above the consumed captures, inside the VM stack allocation, misses every arm store. -/
theorem above_out (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {log : List WEntry}
    (inside : LogInW (windows c sp count a (targets.length + 1)) log) {x n : Nat}
    (lo : sp + 8 * (count - 1) ≤ x) (hi : x + n ≤ high) : OutLRange log x n := by
  have k := p.scalars
  have kb := k.below
  have kl := k.low
  have hd := p.input.geometry.domain.1
  simp only [stackWindow] at hd
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  exact outLRange_of_windows inside ⟨by simp only [closurerecBlockW]; omega,
    by simp only [closurerecStackW]; omega, by simp only [youngPtrW]; omega, trivial⟩

/-- **The CLOSUREREC write certificate.** -/
theorem writes (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) (accu : BitVec 64) :
    ClosurerecWriteOk P s c pl cp sp count dest a (word c Layout.sym_Caml_state).toNat accu targets := by
  have k := p.scalars
  have kr := k.push; have kr' := k.ptrs
  have kb := k.below
  have b := p.block
  have size := closurerecObject_wosize (dest := dest) (targets := targets) p.bound
  have whole := p.ok (p.full_in (accu := accu))
  have bd := p.bound
  have khs := k.hs
  exact ⟨p.bound, by have := p.young; omega, b.room, p.tailRoom, p.stackRoom,
    by unfold closurerecStackStart closurerecCaptureBase; simp only [closurerecSize] at kb; omega,
    p.placed, p.input.geometry.nursery.allocationOutside b.young b.capacity b.room (by omega),
    whole.core, whole.external, fun l a o _ => whole.heap l a o,
    fun i v hv => p.above_out p.full_in (by omega) (by
      have := (List.getElem?_eq_some_iff.mp hv).1
      simp only [List.length_drop] at this; omega),
    whole.trap, whole.bindings⟩

/-- Every aligned word of the VM stack allocation is writable RAM. -/
theorem stack_write (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {x : Nat}
    (lo : high - Layout.stackBytes ≤ x) (hi : x + 8 ≤ high) (al : x % 8 = 0) : RamWriteAt x 8 := by
  have k := p.scalars
  have ks := k.statics
  have kt := k.top
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hr : 0x80000000 ≤ Layout.sym_tohost := by decide
  exact ⟨by omega, by omega, by
    simp only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost, Layout.sym_bss_end] at hb hr ks ⊢; omega, by omega⟩

/-- The words the reservation reads and moves. -/
abbrev reserveWords (c : Config) : List Nat :=
  [Layout.sym_Caml_state, (word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr,
   (word c Layout.sym_Caml_state).toNat + Layout.off_young_limit]

/-- The arm's block and stack stores miss the words the reservation reads. -/
theorem pair_domain_out (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets)
    {log : List WEntry}
    (h : LogInW [closurerecBlockW a (targets.length + 1) count, closurerecStackW sp count (targets.length + 1)] log) :
    ∀ x ∈ reserveWords c, OutLRange log x 8 := by
  have g := p.input.geometry
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have k := p.scalars
  have kl := k.low
  have ks := k.statics
  have bs := p.block.statics
  have kr := k.push; have kr' := k.ptrs
  have bd := p.bound
  have khs := k.hs
  have apart := p.block.domainApart g.nursery
  have dl := g.domainLow
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have hl : Layout.off_young_limit + 8 ≤ Layout.domainStateBytes := by decide
  have hb : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
  intro x hx
  simp only [reserveWords, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    exact outLRange_of_windows h ⟨by simp only [closurerecBlockW]; omega,
      by simp only [closurerecStackW, closurerecStackStart]; omega, trivial⟩

theorem block_in {log : List WEntry} {functions : Nat} (h : LogInW [closurerecBlockW a functions count] log) :
    LogInW [closurerecBlockW a functions count, closurerecStackW sp count functions] log :=
  logInW_left h

theorem stack_in {log : List WEntry} {functions : Nat} (h : LogInW [closurerecStackW sp count functions] log) :
    LogInW [closurerecBlockW a functions count, closurerecStackW sp count functions] log :=
  logInW_mono h fun w hw => by simp only [List.mem_singleton] at hw; simp [hw]

theorem push_pair (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {accu : BitVec 64} :
    LogInW [closurerecBlockW a (targets.length + 1) count, closurerecStackW sp count (targets.length + 1)]
      (closurePushLog sp count accu) :=
  stack_in (closurerecPushLog_in (by have k := p.scalars; have := k.push; have := k.ptrs; omega))

/-- **The CLOSUREREC reservation summary.** -/
theorem reserve (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) (accu : BitVec 64) :
    NurseryReserve c (closurerecFullLog c pl sp count dest a (word c Layout.sym_Caml_state).toNat accu targets) a
      (closurerecObject s count (dest :: targets)).wosize (closurerecObject s count (dest :: targets)).wosize := by
  rw [closurerecObject_wosize p.bound, closurerecFullLog_eq]
  exact NurseryReserve.of_prefixed p.block p.input.geometry.domainLow (p.pair_domain_out p.push_pair)
    (p.pair_domain_out (closurerecBodyLog_in p.block.room p.tailRoom p.stackRoom))

theorem arena (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) (accu : BitVec 64) :
    LogInW [arenaWindow] (closurerecFullLog c pl sp count dest a (word c Layout.sym_Caml_state).toNat accu targets) :=
  (p.ok p.full_in).arena

/-- The capture source (the pushed accumulator, then the stack) is readable. -/
theorem source_read (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) {i : Nat}
    (hi : i < count) : RamReadAt (closureSource sp count + 8 * i) 8 := by
  have k := p.scalars
  have kl := k.low
  have khs := k.hs
  have kr := k.push; have kr' := k.ptrs
  have bd := p.bound
  have ka := k.spAligned
  unfold closureSource
  split
  · cases i with
    | zero => simpa using (p.stack_write (x := sp - 8) (by omega) (by omega) (by omega)).read
    | succ j =>
      have r := p.input.geometry.read p.input.stack kl (i := j) (by omega)
      have e : sp - 8 + 8 * (j + 1) = sp + 8 * j := by omega
      rwa [e]
  · omega

/-- **The CLOSUREREC machine input.** -/
theorem machine (p : ClosurerecPlan L P s op c pl cp sp high count dest a targets offsets) (accu : BitVec 64) :
    ClosurerecMachineInput c pl s.pc sp count dest a (word c Layout.sym_Caml_state).toNat
      (runtimeFields c).youngLimit accu targets offsets := by
  have g := p.input.geometry
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have k := p.scalars
  have kl := k.low
  have kr := k.push; have kr' := k.ptrs
  have kb := k.below
  have khs := k.hs
  have ka := k.spAligned
  have bd := p.bound
  have b := p.block
  have room := b.room
  have ba := b.aligned
  have young := p.young
  have dl := g.domainLow
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have start : closurerecStackStart sp count + 8 = sp + 8 * (count - 1) := by
    unfold closurerecStackStart; omega
  have wordsLen := closureWords_length (c := c) (sp := sp) (count := count) (accu := accu)
  have pushIn : LogInW (windows c sp count a (targets.length + 1)) (closurePushLog sp count accu) := p.push_in
  have headerIn := closurerecHeaderLog_in (targets := targets) (count := count) room
  have capturesIn := closurerecCaptures_in (c := c) (sp := sp) (count := count) (accu := accu) (targets := targets) room
  have setupIn : LogInW (windows c sp count a (targets.length + 1))
      (closurerecSetupLog sp (targets.length + 1) count a (word c Layout.sym_Caml_state).toNat accu) :=
    logInW_append' pushIn (logInW_append' grab_in (pair_in (block_in headerIn)))
  have readyIn : LogInW (windows c sp count a (targets.length + 1))
      (closurerecReadyLog c sp (targets.length + 1) count a (word c Layout.sym_Caml_state).toNat accu) :=
    logInW_append' setupIn (pair_in (block_in capturesIn))
  have firstIn := closurerecFirstLog_in (pl := pl) (dest := dest) (targets := targets) room p.tailRoom
  have infixIn := closurerecInfix_in (pl := pl) (a := a) p.tailRoom p.stackRoom
  have slotIn := closurerecStackSlot_in (targets := targets) (v := BitVec.ofNat 64 a) p.tailRoom
  -- the capture source lies in the VM stack, above the reserved block
  have sourceLow : sp - 8 ≤ closureSource sp count := by unfold closureSource; split <;> omega
  have sourceHigh : closureSource sp count + 8 * count ≤ high := by unfold closureSource; split <;> omega
  have blockMiss : ∀ {log : List WEntry}, LogInW [closurerecBlockW a (targets.length + 1) count] log →
      OutLRange log (closureSource sp count) (8 * count) := fun inside =>
    outLRange_of_windows inside ⟨by simp only [closurerecBlockW]; omega, trivial⟩
  obtain ⟨w3, fetch3⟩ := p.first
  have codeAt : ∀ i, i < targets.length → ∃ w, P.code[s.pc + 4 + i]? = some w := fun i hi =>
    ⟨_, p.offsetsAt i hi⟩
  refine ⟨⟨young, ⟨fun _ => by omega, fun _ => p.stack_write (by omega) (by omega) (by omega),
      (p.ok pushIn).image⟩,
    ⟨NurseryInput.of_block b g.nursery g.toStackGeometry (by omega),
      (p.pair_domain_out p.push_pair) _ (by simp), (p.pair_domain_out p.push_pair) _ (by simp),
      (p.pair_domain_out p.push_pair) _ (by simp)⟩,
    ⟨(p.ok (pair_in (block_in headerIn))).image, (p.ok setupIn).core.domain,
      (p.pair_domain_out (block_in headerIn)) _ (by simp),
      by have := b.top; unfold closurerecCaptureBase; simp only [closurerecSize] at this; omega,
      fun i hi => p.source_read hi,
      fun i hi => b.write (by unfold closurerecCaptureBase; omega)
        (by unfold closurerecCaptureBase; simp only [closurerecSize]; omega)
        (by unfold closurerecCaptureBase; omega),
      (p.ok (pair_in (block_in capturesIn))).image, blockMiss capturesIn,
      outLRange_append (grab_out (by omega)) (blockMiss headerIn)⟩⟩,
    ⟨fun _ => by omega, p.tailRoom, p.stack_write (by unfold closurerecStackStart; omega) (by omega)
        (by unfold closurerecStackStart; omega),
      b.write (by omega) (by simp only [closurerecSize]; omega) ba,
      b.write (by omega) (by simp only [closurerecSize]; omega) (by omega),
      (p.ok (pair_in firstIn)).image,
      (p.ok (logInW_append' readyIn (pair_in (stack_in slotIn)))).core.code _ _ fetch3⟩,
    ⟨by have := young; simp only [closurerecSize] at this; omega, p.stackRoom, fun i hi => g.code_read (by
        simpa using (Array.getElem?_eq_some_iff.mp (p.offsetsAt i hi)).1),
      fun i hi => ⟨b.write (by omega) (by simp only [closurerecSize]; omega) (by omega),
        p.stack_write (by unfold closurerecStackStart at *; omega) (by unfold closurerecStackStart at *; omega)
          (by unfold closurerecStackStart; omega),
        b.write (by omega) (by simp only [closurerecSize]; omega) (by omega),
        b.write (by omega) (by simp only [closurerecSize]; omega) (by omega)⟩,
      (p.ok (pair_in infixIn)).image,
      fun i hi => (p.ok (pair_in infixIn)).core.code _ _ (p.offsetsAt i hi),
      fun i hi => (OperandAt.of_fetch g.toArmGeometry (p.offsetsAt i hi)).read32 p.input.code rfl,
      p.jumps⟩,
    fun i hi => (p.ok (logInW_append' readyIn (pair_in firstIn))).core.code _ _ (p.offsetsAt i hi)⟩

end ClosurerecPlan

end OCaml.Vm.Sim
