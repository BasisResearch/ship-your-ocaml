import OCaml.Vm.Primitives.Uncaught.FatalReport
import OCaml.Vm.Boot.Startup.StatFree
import OCaml.Vm.Boot.Startup.SearchExeFrames
import OCaml.Vm.Primitives.ExitPath.LibcExitHandler
import OCaml.Vm.Primitives.Uncaught.StdioState

/-!
# `caml_fatal_uncaught_exception`: the report, the free and the call of `exit(2)`

At `fprintf`'s entry (`AtFprintf`), the call prints `"Fatal error: exception "`,
the message and a newline (`FprintfReport`, a named obligation: there is no
stdio summary here). Then `caml_stat_free(msg)` (`stat_free_blockL`), the
backtrace test (`backtrace_active` is zero), the test of
`caml_abort_on_uncaught_exn` (zero), and the call of `exit(2)`
(`fatal_exit_call`, post `AtExitCall`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gprReg_ne_htif strOf NameAt)
open OCaml.Vm.Primitives.Uncaught.FormatException (ready_transport_framed)

/-- `"Fatal error: exception %s\n"`, `fprintf`'s format. -/
def fatalFormat : List (BitVec 8) :=
  [0x46#8, 0x61#8, 0x74#8, 0x61#8, 0x6c#8, 0x20#8, 0x65#8, 0x72#8, 0x72#8, 0x6f#8, 0x72#8, 0x3a#8, 0x20#8,
   0x65#8, 0x78#8, 0x63#8, 0x65#8, 0x70#8, 0x74#8, 0x69#8, 0x6f#8, 0x6e#8, 0x20#8, 0x25#8, 0x73#8, 0x0a#8]

theorem fatalFormat_rodata : RodataString 13040 fatalFormat := by decide +kernel

theorem fatalFormat_at {c : Config} (image : ExecutableImage c) : NameAt c.σ.mem 0x80056470#64 fatalFormat :=
  rodata_nameAt image fatalFormat_rodata

/-- What the report prints: the format with the message for `%s`. -/
def fatalText (name : List (BitVec 8)) : String := "Fatal error: exception " ++ strOf name ++ "\n"

/-- The bytes read after the report: `backtrace_active` and
`caml_abort_on_uncaught_exn`'s word. -/
def ExitReads (dom : BitVec 64) (a : Nat) : Prop :=
  ((dom + 232#64).toNat ≤ a ∧ a < (dom + 232#64).toNat + 8) ∨ TailBytes a

/-- What `fprintf` keeps, from its call to its return to `0x8000e02c`. -/
structure FprintfReturned (live : List (Nat × Nat)) (capacity : Nat) (sp ra res dom : BitVec 64)
    (name : List (BitVec 8)) (before : List (Nat × Nat)) (c g : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, name.length + 1) :: live) capacity (sp + 18446744073709551568#64)
    ra g
  pc : PCAt 0x8000e02c#64 g
  callee : ∀ k, (k = 8 ∨ k = 9 ∨ (18 ≤ k ∧ k ≤ 27)) → gprGet g.σ k = gprGet c.σ k
  domainLive : ∀ q n, (q, n) ∈ before → q ≤ (dom + 232#64).toNat → (dom + 232#64).toNat + 16 ≤ q + n → (q, n) ∈ live
  kept : ∀ a, ExitReads dom a → (g.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0
  printed : Vsa.Machine.output g.σ = Vsa.Machine.output c.σ ++ fatalText name
  /-- stdio is initialized: `__sinit` installed `stdio_exit_handler` -/
  installed : bytesVal .ld (read8 g.σ.mem ExitPath.stdioExitHandler.toNat) = ExitPath.stdioExitHandlerFn
  /-- the standard streams as `exit`'s stdio handler will find them -/
  stdio : StdioState.StdioAtExit g.σ.mem

/-- **Named obligation: `fprintf(stderr, "Fatal error: exception %s\n", msg)`
prints the report and returns.** Supplied by a summary of newlib's
`fprintf` on the unbuffered `stderr` stream down to `_write` and the HTIF
console (the stdio step tables, A0). -/
structure FprintfReport (live : List (Nat × Nat)) (capacity : Nat) (sp res dom err : BitVec 64)
    (name : List (BitVec 8)) : Prop where
  returns : ∀ c, PCAt 0x8003ee20#64 c →
    RuntimeReadyL imageLive ((res.toNat, name.length + 1) :: live) capacity (sp + 18446744073709551568#64)
      0x8000e02c#64 c →
    gprGet c.σ 10 = some err → gprGet c.σ 11 = some 0x80056470#64 → gprGet c.σ 12 = some res →
    NameAt c.σ.mem 0x80056470#64 fatalFormat → MessageAt c.σ.mem res name →
    ∃ g live' capacity' ra, Steps c g ∧ FprintfReturned live' capacity' sp ra res dom name live c g

/-- At `exit`'s entry with status 2, the report printed. -/
structure AtExitCall (live : List (Nat × Nat)) (capacity : Nat) (sp : BitVec 64) (name : List (BitVec 8))
    (before e : Config) : Prop where
  ready : RuntimeReadyL imageLive live capacity (sp + 18446744073709551568#64) 0x8000dfb8#64 e
  pc : PCAt 0x800373c8#64 e
  status : gprGet e.σ 10 = some 2#64
  callee : ∀ k, 20 ≤ k → k ≤ 27 → gprGet e.σ k = gprGet before.σ k
  tail : TailLow e.σ.mem
  installed : bytesVal .ld (read8 e.σ.mem ExitPath.stdioExitHandler.toNat) = ExitPath.stdioExitHandlerFn
  stdio : StdioState.StdioAtExit e.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output before.σ ++ fatalText name

/-- A free keeps every byte of another live block disjoint from the freed one. -/
theorem _root_.OCaml.Vm.Boot.Startup.StatFreedL.live_byte {live : Nat → Prop} {H : List (Nat × Nat)} {q : BitVec 64} {n capacity : Nat}
    {sp ra : BitVec 64} {before after : Config} (w : StatFreedL live H q n capacity sp ra before after)
    (frame : NativeFrame sp allocHeadroom) {e : Nat × Nat} (member : e ∈ H) {x : Nat} (inside : InExt e x)
    (apart : ¬ InExt (q.toNat, n) x) (arena : heapStart ≤ x ∧ x < heapEnd) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have same := w.free.memory x (fS_live_outside frame member inside apart arena)
  change (after.σ.mem[x]?).getD 0 = (w.atFree.σ.mem[x]?).getD 0 at same
  rw [same, w.dispatch.memory]

/-- A free keeps low memory outside the allocator's globals. -/
theorem _root_.OCaml.Vm.Boot.Startup.StatFreedL.low_byte {live : Nat → Prop} {H : List (Nat × Nat)} {q : BitVec 64} {n capacity : Nat}
    {sp ra : BitVec 64} {before after : Config} (w : StatFreedL live H q n capacity sp ra before after)
    (frame : NativeFrame sp allocHeadroom) (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd)
    {x : Nat} (low : x < heapStart) (notGlobal : ¬ allocGlobal x) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have outside : ¬ OCaml.Vm.Boot.Startup.fS H q n sp x := fun owned => by
    have lower := frame.lower
    have order : heapStart ≤ heapEnd := by decide
    rcases fS_coarse blockLow blockHigh owned with stack | global | heap
    · obtain ⟨s1, -⟩ := stack
      change sp.toNat - allocHeadroom ≤ x at s1
      omega
    · exact notGlobal global
    · omega
  have same := w.free.memory x outside
  change (after.σ.mem[x]?).getD 0 = (w.atFree.σ.mem[x]?).getD 0 at same
  rw [same, w.dispatch.memory]

/-- **From `fprintf`'s call to `exit(2)`'s**: the report, `caml_stat_free(msg)`,
the backtrace test and the abort test. -/
theorem fatal_exit_call {live : List (Nat × Nat)} {capacity : Nat} {sp res dom active pos err : BitVec 64}
    {name : List (BitVec 8)} {cbOut : String} {r g : Config}
    (at_ : AtFprintf live capacity sp res dom active pos err name cbOut r g)
    (printf : FprintfReport live capacity sp res dom err name)
    (domain : dom = firstDomainPtr) (activeWindow : WriteWindow (dom + 232#64) 8)
    (frame : NativeFrame (sp + 18446744073709551568#64) allocHeadroom)
    (msgLow : heapStart ≤ res.toNat) (msgHigh : res.toNat + (name.length + 1) ≤ heapEnd)
    (msgApart : ∀ a, res.toNat ≤ a → a ≤ res.toNat + name.length → FieldsApart dom a)
    (inactive : active = 0#64) :
    ∃ e live' capacity', Steps g e ∧ AtExitCall live' capacity' sp name g e := by
  have he : heapEnd < 2 ^ 64 := by decide
  have hs : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  obtain ⟨q, n, member, qlo, qhi, qa, aq⟩ := at_.domainBlock
  -- fprintf(stderr, "Fatal error: exception %s\n", msg)
  obtain ⟨g1, live1, cap1, ra1, run1, pr⟩ := printf.returns g at_.pc at_.ready at_.stream at_.format at_.arg
    (fatalFormat_at at_.ready.image) at_.message
  have leaf1 := pr.ready.toLeafInput
  have e18 : gprGet g1.σ 18 = some res := (pr.callee 18 (by omega)).trans at_.msgReg
  have e8 : gprGet g1.σ 8 = some 0x80064d08#64 := (pr.callee 8 (by omega)).trans at_.stateReg
  have r1 := regsAt_of leaf1.raReg
  have l1 : LeafInput (regsAt g1 1) g1 := by rw [r1]; exact leaf1
  -- caml_stat_free(msg)
  obtain ⟨c2, run2, p2⟩ := (release_fast g1 (regsAt g1) l1
    (by simp only [release_input, GHolds, r1, regsAt_of e18]; exact ⟨leaf1.raReg, e18, trivial⟩)).run g1
    ⟨pr.pc, rfl⟩
  have o2 := p2.regs
  simp only [release_regs, regsAt_of e18, GHolds] at o2
  obtain ⟨g10, -, -, -⟩ := o2
  have k2 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10]) : gprGet c2.σ k = gprGet g1.σ k :=
    p2.gpr_frame (by decide) k lo hi out
  obtain ⟨c3, run3, p3⟩ := (call_registers_summary release_call_shape release_call_decode c2
    (release_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(10, res), (2, sp + 18446744073709551568#64)]
    ⟨g10, (k2 2 (by decide) (by decide) (by decide)).trans pr.ready.stack, trivial⟩
    (by change KeysOK [10, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c2 ⟨p2.pc, rfl⟩
  have m3 : c3.σ.mem = g1.σ.mem := by rw [p3.memory, p2.memory, Named.NamedValue.wl_nil]
  have k3 (k : Nat) (lo : 2 ≤ k) (hi : k ≤ 31) (out : k ≠ 10) : gprGet c3.σ k = gprGet g1.σ k :=
    (p3.gpr_frame (by decide) k (by omega) hi (by simp; omega)).trans (k2 k (by omega) hi (by simp; omega))
  have leaf3 : LeafInput 0x8000e034#64 c3 :=
    ⟨p3.good, p3.image, p3.minstret, gholds_lookup (n := 1) _ p3.regs rfl, by decide, p3.tick⟩
  have ready3 : RuntimeReadyL imageLive ((res.toNat, name.length + 1) :: live1) cap1 (sp + 18446744073709551568#64)
      0x8000e034#64 c3 :=
    ready_transport_framed pr.ready leaf3
      ((pr.ready.library.carry p2.kept (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p3.kept
        (p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))
      (fun _ _ => by rw [m3]) (fun _ _ => by rw [m3]) (fun _ _ => by rw [m3]) (fun _ _ => by rw [m3])
      (gholds_lookup (n := 2) _ p3.regs rfl)
  obtain ⟨c4, run4, ⟨freed⟩⟩ := (stat_free_blockL c3 live1 res (name.length + 1) cap1
    (sp + 18446744073709551568#64) 0x8000e034#64 ready3 (gholds_lookup (n := 10) _ p3.regs rfl) frame msgLow
    msgHigh).run c3 ⟨by have := p3.pc; rw [release_call_target] at this; exact this, rfl⟩
  have ready4 := freed.ready
  have pc4 : PCAt 0x8000e034#64 c4 := library_pc freed.free.good freed.free.result.frame.pc
  have s4 (k : Nat) (hk : k ∈ abiSaved) : gprGet c4.σ k = gprGet g1.σ k :=
    (freed.saved_gpr hk).trans (k3 k (by simp [abiSaved] at hk; omega) (by simp [abiSaved] at hk; omega)
      (by simp [abiSaved] at hk; omega))
  -- the bytes read below survive the free and the report
  have fromG (x : Nat) (hx : ExitReads dom x) (c4c3 : (c4.σ.mem[x]?).getD 0 = (c3.σ.mem[x]?).getD 0) :
      (c4.σ.mem[x]?).getD 0 = (g.σ.mem[x]?).getD 0 := by
    rw [c4c3, m3, pr.kept x hx]
  have fieldKept (x : Nat) (lo : (dom + 232#64).toNat ≤ x) (hi : x < (dom + 232#64).toNat + 8) :
      (c4.σ.mem[x]?).getD 0 = (g.σ.mem[x]?).getD 0 :=
    fromG x (Or.inl ⟨lo, hi⟩) (freed.live_byte frame (pr.domainLive q n member qa aq)
      (show q ≤ x ∧ x < q + n by omega)
      (fun inside => by
        have := msgApart x inside.1 (by have := inside.2; omega)
        unfold FieldsApart at this; omega)
      ⟨by omega, by omega⟩)
  have tailKept (x : Nat) (hx : TailBytes x) : (c4.σ.mem[x]?).getD 0 = (g.σ.mem[x]?).getD 0 :=
    fromG x (Or.inr hx) (freed.low_byte frame msgLow msgHigh
      (by unfold TailBytes Layout.sym_caml_abort_on_uncaught_exn Layout.sym_atexit at hx; unfold heapStart; omega)
      (by unfold allocGlobal InRange; unfold TailBytes Layout.sym_caml_abort_on_uncaught_exn Layout.sym_atexit at hx
          omega))
  -- `__stdio_exit_handler`, installed by `fprintf`, survives the free
  have installed4 : bytesVal .ld (read8 c4.σ.mem ExitPath.stdioExitHandler.toNat) = ExitPath.stdioExitHandlerFn := by
    have slot : ExitPath.stdioExitHandler.toNat = Layout.sym_stdio_exit_handler := rfl
    rw [ConsoleWrite.read8_same (m := g1.σ.mem) fun i hi => by
      rw [freed.low_byte frame msgLow msgHigh (by rw [slot]; unfold Layout.sym_stdio_exit_handler heapStart; omega)
        (by rw [slot]; unfold allocGlobal InRange Layout.sym_stdio_exit_handler; omega), m3]]
    exact pr.installed
  -- `backtrace_active` is zero
  have stateAddr : (0x80064d08#64 : BitVec 64).toNat = Layout.sym_Caml_state := rfl
  have dw : bytesVal .ld (read8 c4.σ.mem (0x80064d08#64).toNat) = dom := by
    rw [read8_value, stateAddr, ready4.domainWord, domain]
  have active0 : bytesVal .ld (read8 c4.σ.mem (dom + 232#64).toNat) = 0#64 := by
    rw [read8_value, word_observed (m := g.σ.mem) _ (fun i hi => fieldKept _ (by omega) (by omega)),
      at_.activeRestored, inactive]
  have e8' : gprGet c4.σ 8 = some 0x80064d08#64 := (s4 8 (by decide)).trans e8
  have a10 : gprGet c4.σ 10 = some (regsAt c4 10) :=
    gpr_some (by rw [show gprGet c4.σ 10 = OCaml.Vm.gpr c4 10 from rfl,
      library_gpr ready4.platform (r := 10) (by decide) (by decide) rfl]; rfl)
  have r1' := regsAt_of ready4.raReg
  have l4 : LeafInput (regsAt c4 1) c4 := by rw [r1']; exact ready4.toLeafInput
  obtain ⟨c5, run5, p5⟩ := (trace_fast c4 (regsAt c4) l4
    (by simp only [trace_input, GHolds, regsAt_of e8']; exact ⟨e8', a10, trivial⟩)
    (by rw [regsAt_of e8']; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by rw [regsAt_of e8', dw]; exact activeWindow.read)
    (by simp only [trace_loads, List.getD_cons_succ, List.getD_cons_zero, regsAt_of e8', dw, active0]; decide)).run
    c4 ⟨pc4, rfl⟩
  have m5 : c5.σ.mem = c4.σ.mem := by rw [p5.memory, Named.NamedValue.wl_nil]
  have k5 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [15]) : gprGet c5.σ k = gprGet c4.σ k :=
    p5.gpr_frame (by decide) k lo hi out
  -- `caml_abort_on_uncaught_exn` is zero
  have flag0 : bytesVal .lw (read8 c5.σ.mem (0x80064b34#64).toNat) = 0#64 := by
    have fa : (0x80064b34#64 : BitVec 64).toNat = Layout.sym_caml_abort_on_uncaught_exn := rfl
    rw [m5, fa, ConsoleWrite.read8_same (m := g.σ.mem) fun i hi => tailKept _ (Or.inl ⟨by omega, by omega⟩)]
    exact at_.tail.abort
  have e1 : gprGet c5.σ 1 = some 0x8000e034#64 := (k5 1 (by decide) (by decide) (by decide)).trans ready4.raReg
  have e10 : gprGet c5.σ 10 = some (regsAt c4 10) := (k5 10 (by decide) (by decide) (by decide)).trans a10
  have l5 : LeafInput (regsAt c5 1) c5 := by
    rw [regsAt_of e1]; exact ⟨p5.good, p5.image, p5.minstret, e1, by decide, p5.tick⟩
  obtain ⟨c6, run6, p6⟩ := (abortOff_fast c5 (regsAt c5) l5
    (by simp only [abortOff_input, GHolds, regsAt_of e10]; exact ⟨e10, trivial⟩)
    (by simp only [abortOff_loads, List.getD_cons_zero, flag0]; decide)).run c5 ⟨p5.pc, rfl⟩
  have m6 : c6.σ.mem = c4.σ.mem := by rw [p6.memory, Named.NamedValue.wl_nil, m5]
  have k6 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [15]) : gprGet c6.σ k = gprGet c5.σ k :=
    p6.gpr_frame (by decide) k lo hi out
  -- exit(2)
  have e1' : gprGet c6.σ 1 = some 0x8000e034#64 := (k6 1 (by decide) (by decide) (by decide)).trans e1
  have l6 : LeafInput (regsAt c6 1) c6 := by
    rw [regsAt_of e1']; exact ⟨p6.good, p6.image, p6.minstret, e1', by decide, p6.tick⟩
  obtain ⟨c7, run7, p7⟩ := (leave_fast c6 (regsAt c6) l6
    (by simp only [leave_input, GHolds, regsAt_of e1']; exact ⟨e1', trivial⟩)).run c6 ⟨p6.pc, rfl⟩
  have o7 := p7.regs
  simp only [leave_regs, leave_loads, GHolds] at o7
  obtain ⟨f10, -⟩ := o7
  have k7 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10]) : gprGet c7.σ k = gprGet c6.σ k :=
    p7.gpr_frame (by decide) k lo hi out
  have back (k : Nat) (lo : 2 ≤ k) (hi : k ≤ 31) (out : k ≠ 10 ∧ k ≠ 15) : gprGet c7.σ k = gprGet c4.σ k :=
    (k7 k (by omega) hi (by simp; omega)).trans ((k6 k (by omega) hi (by simp; omega)).trans
      (k5 k (by omega) hi (by simp; omega)))
  obtain ⟨c8, run8, p8⟩ := (call_registers_summary leave_call_shape leave_call_decode c7
    (leave_call_pins p7.image) p7.good p7.image p7.tick p7.minstret
    [(10, 2#64), (2, sp + 18446744073709551568#64)]
    ⟨f10, (back 2 (by decide) (by decide) (by decide)).trans ready4.stack, trivial⟩
    (by change KeysOK [10, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c7 ⟨p7.pc, rfl⟩
  have m8 : c8.σ.mem = c4.σ.mem := by rw [p8.memory, p7.memory, Named.NamedValue.wl_nil, m6]
  have leaf8 : LeafInput 0x8000dfb8#64 c8 :=
    ⟨p8.good, p8.image, p8.minstret, gholds_lookup (n := 1) _ p8.regs rfl, by decide, p8.tick⟩
  refine ⟨c8, live1, cap1, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    (run7.trans run8)))))), ?_⟩
  exact
    { ready := ready_transport_framed ready4 leaf8
        ((((ready4.library.carry p5.kept (p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p6.kept
          (p6.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p7.kept
          (p7.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p8.kept
          (p8.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))
        (fun _ _ => by rw [m8]) (fun _ _ => by rw [m8]) (fun _ _ => by rw [m8]) (fun _ _ => by rw [m8])
        (gholds_lookup (n := 2) _ p8.regs rfl)
      pc := by have := p8.pc; rw [leave_call_target] at this; exact this
      status := gholds_lookup (n := 10) _ p8.regs rfl
      tail := at_.tail.transport fun a ha => by rw [m8, tailKept a ha]
      installed := by rw [m8]; exact installed4
      stdio := pr.stdio.transport fun a ha => by
        rw [m8]
        exact ConsoleWrite.read8_same (m := g1.σ.mem) fun i hi => by
          rw [freed.low_byte frame msgLow msgHigh (ha.low i hi).1 (ha.low i hi).2, m3]
      callee := fun k lo hi =>
        (p8.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
          ((back k (by omega) (by omega) (by omega)).trans
            ((s4 k (by simp [abiSaved]; omega)).trans (pr.callee k (by omega))))
      output := by
        rw [← pr.printed]
        simp only [Vsa.Machine.output]
        rw [p8.output, p7.output, p6.output, p5.output]
        change Vsa.Machine.output c4.σ = Vsa.Machine.output g1.σ
        rw [show Vsa.Machine.output c4.σ = Vsa.Machine.output freed.atFree.σ from freed.free.output]
        simp only [Vsa.Machine.output]
        rw [freed.dispatch.output, p3.output, p2.output] }

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
