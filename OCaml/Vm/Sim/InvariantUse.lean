import OCaml.Vm.Sim.Invariant
import OCaml.Vm.Sim.LogWindow
import OCaml.Vm.Sim.ReadGeometry
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.ImageFrame
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Sim.Invocation

/-!
# Consuming the stack geometry

Every write an arm makes to the VM stack lies in `[high - stackBytes, sp)`,
the free part of the stack allocation. `StackGeometry.outside` turns that one
window fact into the complete `PayloadOutside`/`ImageOutside`/`BindingsOutside`
certificates. `stack_read` and `stack_write` give the read and write windows
of stack words.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The free part of the stack allocation, below the live words. -/
def freeWindow (sp high : Nat) : W := ⟨high - Layout.stackBytes, sp⟩

theorem OutWRange.narrow {high sp a n : Nat} (h : OutWRange [stackWindow high] a n)
    (below : sp ≤ high) : OutWRange [freeWindow sp high] a n := by
  obtain ⟨h, -⟩ := h
  exact ⟨by simp only [stackWindow, freeWindow] at h ⊢; omega, trivial⟩

/-- A static range (below `.bss`'s end) is outside the free window. -/
theorem freeWindow_static {sp high a n : Nat} (g : Layout.sym_bss_end + Layout.stackBytes ≤ high)
    (static : a + n ≤ Layout.sym_bss_end) : OutWRange [freeWindow sp high] a n :=
  ⟨Or.inl (by simp only [freeWindow]; omega), trivial⟩

/-- **Stack writes are separated from the rest of the payload.** -/
theorem StackGeometry.payload {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (inside : LogInW [freeWindow sp high] log) : PayloadOutside log P s c pl cp sp := by
  have below : sp ≤ high := by have := stack.1; omega
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 :=
    fun a ha => outLRange_of_windows inside (freeWindow_static g.statics ha)
  have domainField : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := by
    intro off hoff
    apply outLRange_of_windows inside
    have hd := (OutWRange.narrow g.domain below).1
    exact ⟨by simp only [freeWindow] at hd ⊢; omega, trivial⟩
  refine ⟨static _ (by decide), domainField _ (by decide), domainField _ (by decide),
    static _ (by decide), static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_, static _ (by decide)⟩
  · exact fun i w hw => outLRange_of_windows inside (OutWRange.narrow (g.code i w hw) below)
  · intro i v _
    exact outLRange_of_windows inside ⟨Or.inr (by simp only [freeWindow]; omega), trivial⟩
  · intro l a o _ placed object
    have ho := (OutWRange.narrow (g.heap l a o placed object) below).1
    refine ⟨outLRange_of_windows inside ⟨?_, trivial⟩, outLRange_of_windows inside ⟨?_, trivial⟩⟩
    · simp only [freeWindow] at ho ⊢; omega
    · simp only [freeWindow] at ho ⊢; omega
  · exact fun id ch a hch hcp =>
      outLRange_of_windows inside (OutWRange.narrow (g.channels id ch a hch hcp) below)

theorem StackGeometry.image {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (inside : LogInW [freeWindow sp high] log) :
    ImageOutside log :=
  ⟨outLRange_of_windows inside (freeWindow_static g.statics (by decide)),
   outLRange_of_windows inside (freeWindow_static g.statics (by decide))⟩

theorem StackGeometry.bindings {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (inside : LogInW [freeWindow sp high] log) : BindingsOutside log P c := by
  have below : sp ≤ high := by have := stack.1; omega
  exact ⟨outLRange_of_windows inside (freeWindow_static g.statics (by decide)),
    fun i name h => outLRange_of_windows inside (OutWRange.narrow (g.primitives i name h) below)⟩

/-- The live stack fits the allocation when its length fits the budget
(`Fits`, with `8 * B.stackWords ≤ Layout.stackBytes`). -/
theorem stack_space {c pl sp high} {stk : List Val} (stack : StackRepr c pl sp high stk)
    (fits : 8 * stk.length ≤ Layout.stackBytes) : high - Layout.stackBytes ≤ sp := by
  have := stack.1
  omega

/-- Every live stack word is readable. -/
theorem StackGeometry.read {P s c pl cp sp high} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (space : high - Layout.stackBytes ≤ sp)
    {i : Nat} (hi : i < s.stack.length) : RamReadAt (sp + 8 * i) 8 := by
  have hs := stack.1
  have hb : Layout.sym_tohost + 8 ≤ Layout.sym_bss_end := by decide
  have ht := g.top
  have hg := g.statics
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega

/-- A word in the free window is writable. -/
theorem StackGeometry.write {P s c pl cp sp high} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) {k : Nat} (pos : 0 < k)
    (space : high - Layout.stackBytes + 8 * k ≤ sp) :
    WriteWindow (BitVec.ofNat 64 (sp - 8 * k)) 8 := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have ha := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hn : (BitVec.ofNat 64 (sp - 8 * k)).toNat = sp - 8 * k :=
    Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hn] <;> simp only [Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega

/-- Transport across a write footprint that misses the two pointer words the
geometry reads (supplied by `PayloadOutside.domain` and `BindingsOutside.contents`). -/
theorem StackGeometry.frame_outsideLog {P s s' c c' pl cp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (heap : s'.heap = s.heap) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (memory : ∀ x, OutL log x → byte c' x = byte c x) : StackGeometry P s' c' pl cp high :=
  g.transport (fun l o' h => ⟨o', heap ▸ h, rfl⟩) (by rw [world])
    (Reloc.bytesT_congr (copied_of_outsideLog memory domain))
    (Reloc.bytesT_congr (copied_of_outsideLog memory contents))

/-- Exact write-log form of `StackGeometry.frame_outsideLog`. -/
theorem StackGeometry.frame_log {P s s' c c' pl cp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (heap : s'.heap = s.heap) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : StackGeometry P s' c' pl cp high :=
  g.frame_outsideLog heap world domain contents fun x hx => by
    rw [byte_total, byte_total, memory, writeLog_out _ _ _ hx]

/-! ## The native invocation across an arm -/

/-- The allocator arena, below every native frame (`NativeValid.low`). -/
def arenaWindow : W := ⟨0, Vsa.Sim.DlHeap.heapEnd⟩

theorem insideW_arena {ws : List W} {a n : Nat} (below : ∀ w ∈ ws, w.hi ≤ Vsa.Sim.DlHeap.heapEnd)
    (inside : InsideW ws a n) : InsideW [arenaWindow] a n := by
  induction ws with
  | nil => exact False.elim inside
  | cons w ws ih =>
    rcases inside with here | tail
    · have := below w (by simp)
      exact Or.inl ⟨Nat.zero_le _, by simp only [arenaWindow]; omega⟩
    · exact ih (fun w' hw => below w' (by simp [hw])) tail

/-- A write log inside windows below the arena end is inside the arena. -/
theorem logInW_arena {ws : List W} {log : List WEntry}
    (below : ∀ w ∈ ws, w.hi ≤ Vsa.Sim.DlHeap.heapEnd) (inside : LogInW ws log) :
    LogInW [arenaWindow] log := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨insideW_arena below inside.1, ih inside.2⟩

/-! ## The `external_raise` word across a write -/

/-- The `Caml_state->external_raise` word of `c`. -/
abbrev externalWord (c : Config) : Nat := (word c Layout.sym_Caml_state).toNat + Layout.off_external_raise

/-- A log in windows apart from `external_raise` misses it. -/
theorem external_out {c : Config} {ws : List W} {log : List WEntry} (inside : LogInW ws log)
    (apart : ∀ w ∈ ws, w.hi ≤ externalWord c ∨ externalWord c + 8 ≤ w.lo) :
    OutLRange log (externalWord c) 8 := by
  apply outLRange_of_windows inside
  clear inside
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨(apart w (by simp)).symm, ih (fun w' hw => apart w' (by simp [hw]))⟩

/-- A window in the VM stack allocation is apart from `external_raise`. -/
theorem StackGeometry.external_stack {P s c pl cp high} (g : StackGeometry P s c pl cp high)
    {lo hi : Nat} (low : high - Layout.stackBytes ≤ lo) (top : hi ≤ high) :
    hi ≤ externalWord c ∨ externalWord c + 8 ≤ lo := by
  have fits : Layout.off_external_raise + 8 ≤ Layout.domainStateBytes := by decide
  obtain ⟨d, -⟩ := g.domain
  simp only [stackWindow] at d
  simp only [externalWord]
  omega

/-- A log inside the VM stack allocation misses `external_raise`. -/
theorem StackGeometry.external_of_stack {P s c pl cp high} (g : StackGeometry P s c pl cp high)
    {log : List WEntry} (inside : LogInW [stackWindow high] log) : OutLRange log (externalWord c) 8 :=
  external_out inside fun w hw => by
    simp only [List.mem_singleton] at hw
    subst hw
    exact g.external_stack (Nat.le_refl _) (Nat.le_refl _)

/-- Another `Caml_state` field is apart from `external_raise`. -/
theorem external_field {c : Config} {off : Nat}
    (apart : off + 8 ≤ Layout.off_external_raise ∨ Layout.off_external_raise + 8 ≤ off) :
    (word c Layout.sym_Caml_state).toNat + off + 8 ≤ externalWord c ∨
      externalWord c + 8 ≤ (word c Layout.sym_Caml_state).toNat + off := by
  simp only [externalWord]
  omega

/-- A range inside a placed object is apart from `external_raise`. -/
theorem StackGeometry.external_object {P s c pl cp high} (g : StackGeometry P s c pl cp high)
    {l a : Nat} {o : Obj} (placed : pl.φ l = some a) (got : s.heap.get? l = some o) {lo hi : Nat}
    (low : a - 8 ≤ lo) (top : hi ≤ a - 8 + (8 * o.wosize + 8)) :
    hi ≤ externalWord c ∨ externalWord c + 8 ≤ lo := by
  have fits : Layout.off_external_raise + 8 ≤ Layout.domainStateBytes := by decide
  obtain ⟨d, -⟩ := g.domainHeap l a o placed got
  dsimp only at d
  simp only [externalWord]
  omega

/-- **The native invocation survives an arena write** that misses the
`Caml_state` pointer and restores `x2`. -/
theorem NativePlaced.frame_log {c c' : Config} {log : List WEntry} (n : NativePlaced c)
    (inside : LogInW [arenaWindow] log) (domain : OutLRange log Layout.sym_Caml_state 8)
    (external : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (stack : gpr c' 2 = gpr c 2) : NativePlaced c' := by
  obtain ⟨D, inv, valid⟩ := n
  rw [inv.domain] at external
  refine ⟨D, inv.frame_log ⟨domain, fun r _ => outLRange_of_windows inside ⟨?_, trivial⟩, external⟩ memory stack,
    valid⟩
  have := valid.low
  exact Or.inr (by simp only [arenaWindow]; omega)

/-- **Arm writes keep the native invocation**: every window of the log ends
inside the allocator arena. -/
theorem NativePlaced.frame_vm {c c' : Config} {ws : List W} {log : List WEntry}
    (n : NativePlaced c) (inside : LogInW ws log)
    (below : ∀ w ∈ ws, w.hi ≤ Vsa.Sim.DlHeap.heapEnd)
    (domain : OutLRange log Layout.sym_Caml_state 8) (external : OutLRange log (externalWord c) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (stack : gpr c' 2 = gpr c 2) : NativePlaced c' :=
  n.frame_log (logInW_arena below inside) domain external memory stack

theorem outW_of_above {ws : List W} {a : Nat} (below : ∀ w ∈ ws, w.hi ≤ a) : OutW ws a := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨Or.inr (below w (by simp)), ih (fun w' hw => below w' (by simp [hw]))⟩

/-- Window form of `NativePlaced.frame_vm`, for sites that already frame
their memory by `FrameOn`. -/
theorem NativePlaced.frameOn {c c' : Config} {ws : List W} (n : NativePlaced c)
    (frame : FrameOn ws c.σ.mem c'.σ.mem) (below : ∀ w ∈ ws, w.hi ≤ Vsa.Sim.DlHeap.heapEnd)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (external : word c' (externalWord c) = word c (externalWord c))
    (stack : gpr c' 2 = gpr c 2) : NativePlaced c' := by
  obtain ⟨D, inv, valid⟩ := n
  refine ⟨D, ⟨stack.trans inv.stack, domain.trans inv.domain, fun r hr i hi => ?_, ?_⟩, valid⟩
  · rw [← inv.region r hr i hi, byte_total, byte_total, frame]
    apply outW_of_above
    intro w hw
    have := below w hw
    have := valid.low
    omega
  · have e := inv.externalRaise
    rw [← inv.domain] at e ⊢
    exact external.trans e

/-- A window ending in the VM stack ends in the arena. -/
theorem StackGeometry.stack_below {P s c pl cp high} (g : StackGeometry P s c pl cp high)
    {hi : Nat} (h : hi ≤ high) : hi ≤ Vsa.Sim.DlHeap.heapEnd :=
  Nat.le_trans h g.arena

/-- A window ending in the `Caml_state` record ends in the arena. -/
theorem StackGeometry.domain_below {P s c pl cp high} (g : StackGeometry P s c pl cp high)
    {off : Nat} (h : off ≤ Layout.domainStateBytes) :
    (word c Layout.sym_Caml_state).toNat + off ≤ Vsa.Sim.DlHeap.heapEnd := by
  have := g.domainArena
  omega

/-- The native invocation with the native stack pointer elsewhere (inside a
C callee or a `longjmp`): the snapshot's bytes and `Caml_state` pointer are
intact, and restoring `x2 = nsp` re-establishes `NativePlaced`. -/
def NativeHeld (nsp : Nat) (c : Config) : Prop :=
  ∃ D, D.nativeSp = nsp ∧ NativeValid D ∧ word c Layout.sym_Caml_state = D.domain ∧
    word c (D.domain.toNat + Layout.off_external_raise) = BitVec.ofNat 64 (D.nativeSp + raiseBufOffset) ∧
    ∀ r ∈ invocationRanges, ∀ i < r.2,
      byte c (D.nativeSp + r.1 + i) = D.snapshot (D.nativeSp + r.1 + i)

/-- Leave the loop head: the invocation is held at the current native sp. -/
theorem NativePlaced.held {c : Config} {nsp : Nat} (n : NativePlaced c)
    (sp : gpr c 2 = some (BitVec.ofNat 64 nsp)) (small : nsp < 2^64) : NativeHeld nsp c := by
  obtain ⟨D, inv, valid⟩ := n
  have top : D.nativeSp < 2^64 := by
    have := valid.high
    simp only [Layout.sym_stack_top] at this
    omega
  have same := congrArg BitVec.toNat (Option.some.inj (sp.symm.trans inv.stack))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt top] at same
  exact ⟨D, same.symm, valid, inv.domain, inv.externalRaise, inv.region⟩

/-- Return to the loop head across a write log that misses the invocation. -/
theorem NativeHeld.frame_log {c c' : Config} {nsp : Nat} {log : List WEntry} (n : NativeHeld nsp c)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (region : ∀ r ∈ invocationRanges, OutLRange log (nsp + r.1) r.2)
    (external : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log)
    (stack : gpr c' 2 = some (BitVec.ofNat 64 nsp)) : NativePlaced c' := by
  obtain ⟨D, rfl, valid, dom, ext, reg⟩ := n
  have bytes : ∀ x, OutL log x → byte c' x = byte c x := fun x hx => by
    rw [byte_total, byte_total, memory, writeLog_out _ _ _ hx]
  rw [dom] at external
  refine ⟨D, ⟨stack, ?_, fun r hr i hi => ?_, ?_⟩, valid⟩
  · rw [← dom]
    exact Reloc.bytesT_congr (copied_of_outsideLog bytes domain)
  · rw [← reg r hr i hi]
    simpa only [Nat.add_zero] using copied_of_outsideLog bytes (region r hr) i hi
  · rw [← ext]
    exact Reloc.bytesT_congr (copied_of_outsideLog bytes external)

/-- A held invocation survives a write log that misses it. -/
theorem NativeHeld.frame {c c' : Config} {nsp : Nat} {log : List WEntry} (n : NativeHeld nsp c)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (region : ∀ r ∈ invocationRanges, OutLRange log (nsp + r.1) r.2)
    (external : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : NativeHeld nsp c' := by
  obtain ⟨D, rfl, valid, dom, ext, reg⟩ := n
  have bytes : ∀ x, OutL log x → byte c' x = byte c x := fun x hx => by
    rw [byte_total, byte_total, memory, writeLog_out _ _ _ hx]
  rw [dom] at external
  refine ⟨D, rfl, valid, ?_, ?_, fun r hr i hi => ?_⟩
  · rw [← dom]
    exact Reloc.bytesT_congr (copied_of_outsideLog bytes domain)
  · rw [← ext]
    exact Reloc.bytesT_congr (copied_of_outsideLog bytes external)
  · rw [← reg r hr i hi]
    simpa only [Nat.add_zero] using copied_of_outsideLog bytes (region r hr) i hi

/-- An arena write log misses the held invocation. -/
theorem NativeHeld.region_of_arena {c : Config} {nsp : Nat} {log : List WEntry}
    (n : NativeHeld nsp c) (inside : LogInW [arenaWindow] log) :
    ∀ r ∈ invocationRanges, OutLRange log (nsp + r.1) r.2 := by
  obtain ⟨D, rfl, valid, -, -, -⟩ := n
  intro r _
  apply outLRange_of_windows inside
  have := valid.low
  exact ⟨Or.inr (by simp only [arenaWindow]; omega), trivial⟩

/-- A read-only run keeps the native invocation once `x2` is restored. -/
theorem NativePlaced.frame_read {c c' : Config} (n : NativePlaced c)
    (memory : c'.σ.mem = c.σ.mem) (stack : gpr c' 2 = gpr c 2) : NativePlaced c' :=
  let ⟨D, inv, valid⟩ := n; ⟨D, inv.frame_read memory stack, valid⟩

end OCaml.Vm.Sim
